use fiat_shamir::{ChallengeSampler, FSProver, FSVerifier, Proof, ProverState, VerifierState};
use field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use koala_bear::{KoalaBear as F, QuinticExtensionFieldKB as EF, default_koalabear_poseidon1_16};
use poly::{EvaluationsList, MleOwned, MultilinearPoint};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use symetric::ProofHashProfile;
use whir::{FoldingFactor, SecurityAssumption, SparseStatement, SparseValue, WhirConfig, WhirConfigBuilder};
use zk_alloc::ArenaVec;

const N_VARS: usize = 13;
const BATCHING_POW_BITS: usize = 6;

fn protocol_binding() -> Vec<F> {
    let tag = b"leanvm-whir-three-commitments-test-v1";
    let mut fields = vec![F::from_usize(tag.len())];
    fields.extend(tag.iter().map(|&b| F::from_u8(b)));
    fields.extend([3, N_VARS, 100, 12, 4, 3, 4, 3, 3, BATCHING_POW_BITS].map(F::from_usize));
    fields
}

fn claim_binding(groups: &[Vec<SparseStatement<EF>>; 3]) -> Vec<F> {
    let mut fields = vec![F::from_usize(groups.len())];
    for group in groups {
        fields.push(F::from_usize(group.len()));
        for statement in group {
            fields.extend(
                [
                    statement.total_num_variables,
                    statement.point.len(),
                    statement.values.len(),
                    statement.is_next as usize,
                ]
                .map(F::from_usize),
            );
            for x in &statement.point.0 {
                fields.extend_from_slice(x.as_basis_coefficients_slice());
            }
            for value in &statement.values {
                fields.push(F::from_usize(value.selector));
                fields.extend_from_slice(value.value.as_basis_coefficients_slice());
            }
        }
    }
    fields
}

#[test]
fn keccak_three_commitments_verify_all_roots_cross_values_and_claim_groups() {
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
        N_VARS,
    );
    let mut rng = StdRng::seed_from_u64(1303);
    let polynomials: [MleOwned<EF>; 3] =
        std::array::from_fn(|_| MleOwned::Base(ArenaVec::from_iter((0..1 << N_VARS).map(|_| rng.random::<F>()))));
    let statements = polynomials.each_ref().map(|polynomial| {
        let dense_point = MultilinearPoint((0..N_VARS).map(|_| rng.random::<EF>()).collect());
        let dense_value = polynomial.evaluate(&dense_point);
        let suffix = MultilinearPoint((0..N_VARS - 3).map(|_| rng.random::<EF>()).collect());
        let refs = polynomial.by_ref();
        let base = refs.as_base().unwrap();
        let height = 1 << suffix.len();
        let values = [1, 3, 7]
            .map(|selector| {
                SparseValue::new(
                    selector,
                    (&base[selector * height..(selector + 1) * height]).evaluate(&suffix),
                )
            })
            .to_vec();
        let column = &base[2 * height..3 * height];
        let shifted = column[1..]
            .iter()
            .copied()
            .chain(std::iter::once(column[height - 1]))
            .collect::<Vec<_>>();
        let next_value = shifted.as_slice().evaluate(&suffix);
        vec![
            SparseStatement::dense(dense_point, dense_value),
            SparseStatement::new(N_VARS, suffix.clone(), values),
            SparseStatement::new_next(N_VARS, suffix, vec![SparseValue::new(2, next_value)]),
        ]
    });
    let binding = protocol_binding();
    let permutation = default_koalabear_poseidon1_16();
    let capacity = [F::from_u32(330); 8];
    let mut prover =
        ProverState::<EF, _>::new_with_hash_profile(permutation.clone(), capacity, ProofHashProfile::Keccak240);
    prover.observe_scalars(&binding);
    let witnesses = polynomials
        .each_ref()
        .map(|polynomial| config.commit_without_ood(&mut prover, polynomial, 1 << N_VARS));
    prover.observe_scalars(&claim_binding(&statements));
    let refs = polynomials.each_ref().map(|polynomial| polynomial.by_ref());
    let point = config.prove_three_commitments(
        &mut prover,
        BATCHING_POW_BITS,
        statements.clone(),
        witnesses,
        refs.each_ref(),
    );
    let final_challenges = prover.sample_vec(8);
    let proof = prover.into_proof();
    let encoded = serde_json::to_value(&proof).unwrap();
    assert_eq!(encoded["merkle_paths"].as_array().unwrap().len(), config.n_rounds() + 3);

    let verify = |candidate: &Proof<F>,
                  candidate_statements: [Vec<SparseStatement<EF>>; 3],
                  order: [usize; 3],
                  altered_geometry: Option<usize>,
                  altered_domain: bool,
                  observe_altered_claims: bool|
     -> bool {
        let Ok(mut verifier) = VerifierState::<EF, _>::new_with_hash_profile(
            candidate.clone(),
            permutation.clone(),
            capacity,
            ProofHashProfile::Keccak240,
        ) else {
            return false;
        };
        let mut candidate_binding = binding.clone();
        if altered_domain {
            candidate_binding[1] += F::ONE;
        }
        verifier.observe_scalars(&candidate_binding);
        let mut commitments = Vec::new();
        for _ in 0..3 {
            let Ok(commitment) = config.parse_commitment_without_ood::<F>(&mut verifier) else {
                return false;
            };
            commitments.push(commitment);
        }
        if let Some(index) = altered_geometry {
            commitments[index].num_variables -= 1;
        }
        verifier.observe_scalars(&claim_binding(if observe_altered_claims {
            &candidate_statements
        } else {
            &statements
        }));
        let result = config.verify_three_commitments::<F>(
            &mut verifier,
            BATCHING_POW_BITS,
            order.map(|i| &commitments[i]),
            candidate_statements,
        );
        let Ok(verifier_point) = result else {
            return false;
        };
        if verifier.check_fully_consumed().is_err() {
            return false;
        }
        assert_eq!(verifier_point, point);
        assert_eq!(verifier.sample_vec(8), final_challenges);
        true
    };
    assert!(verify(&proof, statements.clone(), [0, 1, 2], None, false, false));
    let mut negatives = 0;
    for group in 0..3 {
        for observe_altered_claims in [false, true] {
            let mut changed = statements.clone();
            changed[group][0].values[0].value += EF::ONE;
            assert!(!verify(&proof, changed, [0, 1, 2], None, false, observe_altered_claims));
            negatives += 1;
        }
        let mut changed = statements.clone();
        changed[group][1].values[0].selector += 1;
        assert!(!verify(&proof, changed, [0, 1, 2], None, false, false));
        let mut changed = statements.clone();
        changed[group].clear();
        assert!(!verify(&proof, changed, [0, 1, 2], None, false, false));
        assert!(!verify(
            &proof,
            statements.clone(),
            [0, 1, 2],
            Some(group),
            false,
            false
        ));
        negatives += 3;
    }
    for order in [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        assert!(!verify(&proof, statements.clone(), order, None, false, false));
        negatives += 1;
    }
    assert!(!verify(&proof, statements.clone(), [0, 1, 2], None, true, false));
    negatives += 1;
    // Three root limbs and all thirty base coordinates of six cross values.
    for index in [0, 8, 16].into_iter().chain(24..54) {
        let mut changed = encoded.clone();
        let value = changed["transcript"][index].as_u64().unwrap();
        changed["transcript"][index] = serde_json::json!((value + 1) % F::ORDER_U64);
        assert!(!verify(
            &serde_json::from_value(changed).unwrap(),
            statements.clone(),
            [0, 1, 2],
            None,
            false,
            false
        ));
        negatives += 1;
    }
    for index in 0..3 {
        let mut changed = encoded.clone();
        changed["merkle_paths"].as_array_mut().unwrap().remove(index);
        assert!(!verify(
            &serde_json::from_value(changed).unwrap(),
            statements.clone(),
            [0, 1, 2],
            None,
            false,
            false
        ));
        negatives += 1;
    }
    let mut changed = encoded.clone();
    changed["transcript"].as_array_mut().unwrap().pop();
    assert!(!verify(
        &serde_json::from_value(changed).unwrap(),
        statements.clone(),
        [0, 1, 2],
        None,
        false,
        false
    ));
    let mut changed = encoded;
    changed["transcript"].as_array_mut().unwrap().push(serde_json::json!(0));
    assert!(!verify(
        &serde_json::from_value(changed).unwrap(),
        statements.clone(),
        [0, 1, 2],
        None,
        false,
        false
    ));
    negatives += 2;
    println!(
        "three-commitment WHIR: {} proof base fields, {} Merkle batches, {negatives} negative cases rejected",
        proof.proof_size_fe(),
        config.n_rounds() + 3
    );
}
