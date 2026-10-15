use fiat_shamir::{FSProver, FSVerifier, ProverState, VerifierState};
use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear as F, QuinticExtensionFieldKB as EF, default_koalabear_poseidon1_16};
use poly::{MleOwned, MultilinearPoint};
use symetric::ProofHashProfile;
use whir::{FoldingFactor, SecurityAssumption, SparseStatement, WhirConfig, WhirConfigBuilder};
use zk_alloc::ArenaVec;

const NUM_VARIABLES: usize = 13;
const BATCHING_POW_BITS: usize = 6;
const PROTOCOL_TAG: &[u8] = b"leanvm-whir-two-commitments-v1";

fn protocol_binding(tag: &[u8], batching_pow_bits: usize) -> Vec<F> {
    let mut binding = Vec::with_capacity(tag.len() + 2);
    binding.push(F::from_u32(tag.len() as u32));
    binding.extend(tag.iter().map(|&byte| F::from_u32(byte.into())));
    binding.push(F::from_u32(batching_pow_bits as u32));
    binding
}

fn dense_statement(polynomial: &MleOwned<EF>, offset: u32) -> SparseStatement<EF> {
    let point = MultilinearPoint(
        (0..NUM_VARIABLES)
            .map(|index| EF::from_u32(offset + 3 * index as u32))
            .collect(),
    );
    let value = polynomial.evaluate(&point);
    SparseStatement::dense(point, value)
}

#[test]
fn keccak_two_commitment_whir_roundtrip_and_binding_rejections() {
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
        NUM_VARIABLES,
    );
    let num_coefficients = 1 << NUM_VARIABLES;
    let primary_polynomial = MleOwned::<EF>::Base(ArenaVec::from_iter(
        (0..num_coefficients).map(|index| F::from_u32(7 * index as u32 + 3)),
    ));
    let secondary_polynomial = MleOwned::<EF>::Base(ArenaVec::from_iter(
        (0..num_coefficients).map(|index| F::from_u32(11 * index as u32 + 19)),
    ));
    let primary_statement = vec![
        dense_statement(&primary_polynomial, 2),
        dense_statement(&primary_polynomial, 41),
    ];
    let secondary_statement = vec![
        dense_statement(&secondary_polynomial, 7),
        dense_statement(&secondary_polynomial, 53),
    ];

    let permutation = default_koalabear_poseidon1_16();
    let capacity = [F::from_u32(123); 8];
    let binding = protocol_binding(PROTOCOL_TAG, BATCHING_POW_BITS);
    let mut prover =
        ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
    prover.observe_scalars(&binding);
    let primary_witness = config.commit_without_ood(&mut prover, &primary_polynomial, num_coefficients);
    let secondary_witness = config.commit_without_ood(&mut prover, &secondary_polynomial, num_coefficients);
    config.prove_two_commitments(
        &mut prover,
        BATCHING_POW_BITS,
        primary_statement.clone(),
        primary_witness,
        &primary_polynomial.by_ref(),
        secondary_statement.clone(),
        secondary_witness,
        &secondary_polynomial.by_ref(),
    );
    let proof = prover.into_proof();

    let verify = |candidate_binding: &[F],
                  candidate_primary_statement: Vec<SparseStatement<EF>>,
                  candidate_secondary_statement: Vec<SparseStatement<EF>>,
                  swap_commitments: bool| {
        let mut verifier = match VerifierState::<EF, _>::new_with_hash_profile(
            proof.clone(),
            permutation.clone(),
            capacity,
            ProofHashProfile::Keccak240,
        ) {
            Ok(verifier) => verifier,
            Err(_) => return false,
        };
        verifier.observe_scalars(candidate_binding);
        let primary_parsed = match config.parse_commitment_without_ood::<F>(&mut verifier) {
            Ok(parsed) => parsed,
            Err(_) => return false,
        };
        let secondary_parsed = match config.parse_commitment_without_ood::<F>(&mut verifier) {
            Ok(parsed) => parsed,
            Err(_) => return false,
        };
        let result = if swap_commitments {
            config.verify_two_commitments::<F>(
                &mut verifier,
                BATCHING_POW_BITS,
                &secondary_parsed,
                candidate_primary_statement,
                &primary_parsed,
                candidate_secondary_statement,
            )
        } else {
            config.verify_two_commitments::<F>(
                &mut verifier,
                BATCHING_POW_BITS,
                &primary_parsed,
                candidate_primary_statement,
                &secondary_parsed,
                candidate_secondary_statement,
            )
        };
        result.is_ok() && verifier.check_fully_consumed().is_ok()
    };

    assert!(verify(
        &binding,
        primary_statement.clone(),
        secondary_statement.clone(),
        false,
    ));

    let mut changed_primary_statement = primary_statement.clone();
    changed_primary_statement[0].values[0].value += EF::ONE;
    assert!(!verify(
        &binding,
        changed_primary_statement,
        secondary_statement.clone(),
        false,
    ));

    let mut changed_secondary_statement = secondary_statement.clone();
    changed_secondary_statement[1].values[0].value += EF::ONE;
    assert!(!verify(
        &binding,
        primary_statement.clone(),
        changed_secondary_statement,
        false,
    ));

    assert!(!verify(
        &binding,
        primary_statement.clone(),
        secondary_statement.clone(),
        true,
    ));

    let changed_domain_binding = protocol_binding(b"leanvm-whir-two-commitments-v2", BATCHING_POW_BITS);
    assert!(!verify(
        &changed_domain_binding,
        primary_statement.clone(),
        secondary_statement.clone(),
        false,
    ));

    let changed_batching_binding = protocol_binding(PROTOCOL_TAG, BATCHING_POW_BITS + 1);
    assert!(!verify(
        &changed_batching_binding,
        primary_statement,
        secondary_statement,
        false,
    ));
}
