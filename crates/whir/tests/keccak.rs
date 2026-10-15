use fiat_shamir::{FSProver, FSVerifier, ProverState, VerifierState, flatten_scalars_to_base};
use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear as F, QuinticExtensionFieldKB as EF, default_koalabear_poseidon1_16};
use poly::{MleOwned, MultilinearPoint};
use symetric::ProofHashProfile;
use whir::{FoldingFactor, SecurityAssumption, SparseStatement, WhirConfig, WhirConfigBuilder};
use zk_alloc::ArenaVec;

#[test]
fn keccak_whir_roundtrip_and_changed_statement_rejection() {
    let config = WhirConfig::<EF>::new(
        &WhirConfigBuilder {
            security_level: 100,
            max_num_variables_to_send_coeffs: 3,
            pow_bits: 12,
            folding_factor: FoldingFactor::new(4, 3),
            soundness_type: SecurityAssumption::JohnsonBound,
            starting_log_inv_rate: 4,
            rs_domain_initial_reduction_factor: 3,
        },
        13,
    );
    let polynomial = MleOwned::<EF>::Base(ArenaVec::from_iter((0..(1 << 13)).map(|i| F::from_u32(i * 3 + 1))));
    let point = MultilinearPoint((0..13).map(|i| EF::from_u32(i + 2)).collect());
    let value = polynomial.evaluate(&point);
    let statement = vec![SparseStatement::dense(point.clone(), value)];
    let binding = flatten_scalars_to_base(&[point.0.as_slice(), &[value]].concat());
    let permutation = default_koalabear_poseidon1_16();
    let cap = [F::from_u32(123); 8];
    let mut prover = ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), cap, ProofHashProfile::Keccak240);
    prover.observe_scalars(&binding);
    let witness = config.commit(&mut prover, &polynomial, 1 << 13);
    config.prove(&mut prover, statement.clone(), witness, &polynomial.by_ref());
    let proof = prover.into_proof();
    let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
        proof.clone(),
        permutation.clone(),
        cap,
        ProofHashProfile::Keccak240,
    )
    .unwrap();
    verifier.observe_scalars(&binding);
    let parsed = config.parse_commitment::<F>(&mut verifier).unwrap();
    config.verify::<F>(&mut verifier, &parsed, statement.clone()).unwrap();
    verifier.check_fully_consumed().unwrap();

    let mut wrong_statement = statement;
    wrong_statement[0].values[0].value += EF::ONE;
    let mut wrong = VerifierState::<EF, _>::new_with_hash_profile(
        proof.clone(),
        permutation.clone(),
        cap,
        ProofHashProfile::Keccak240,
    )
    .unwrap();
    wrong.observe_scalars(&binding);
    let parsed = config.parse_commitment::<F>(&mut wrong).unwrap();
    assert!(config.verify::<F>(&mut wrong, &parsed, wrong_statement).is_err());

    let mut wrong_domain = VerifierState::<EF, _>::new_with_hash_profile(
        proof,
        permutation,
        [F::from_u32(124); 8],
        ProofHashProfile::Keccak240,
    )
    .unwrap();
    wrong_domain.observe_scalars(&binding);
    let parsed = config.parse_commitment::<F>(&mut wrong_domain).unwrap();
    assert!(
        config
            .verify::<F>(&mut wrong_domain, &parsed, vec![SparseStatement::dense(point, value)])
            .is_err()
    );
}
