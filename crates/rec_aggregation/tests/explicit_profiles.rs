use backend::{Air, ArenaVec, EvaluationsList, PrimeCharacteristicRing, PrimeField32, arena_vec};
use lean_compiler::{ProgramSource, compile_program};
use lean_prover::{
    WhirExecutionProfile,
    prove_execution::prove_execution_with_profile,
    verify_execution::{verify_execution, verify_execution_with_profile},
};
use lean_vm::{ExecutionWitness, F, try_execute_bytecode};
use rec_aggregation::{
    RecursiveChildShape, RecursiveVerifierOptions, compile_binary_node_bytecode_for_dimension_with_options,
    compile_binary_node_bytecode_for_fixed_shape_with_options, compile_binary_node_bytecode_with_options,
    compile_lifted_execution_bytecode_for_fixed_shape_with_options, compile_lifted_execution_bytecode_with_options,
    compile_lifted_execution_bytecode_with_profile, lift_execution_proof_with_profiles,
    prepare_binary_node_with_profiles, prove_binary_node_with_profiles, verify_binary_node_with_profiles,
    verify_lifted_execution_proof_with_profiles,
};

fn child_bytecode() -> lean_vm::Bytecode {
    compile_program(&ProgramSource::Raw(
        "def main():\n    public = 0\n    assert public[0] == 1\n    return\n".into(),
    ))
}

#[test]
fn profiles_bind_each_parameter_before_execution_challenges() {
    let child = child_bytecode();
    let profile = WhirExecutionProfile::security_100(1);
    let cap = profile.fiat_shamir_domain_sep(&child);
    let mut changes = [profile; 7];
    changes[0].security_bits -= 1;
    changes[1].grinding_bits -= 1;
    changes[2].first_folding_factor -= 1;
    changes[3].subsequent_folding_factor -= 1;
    changes[4].rs_domain_initial_reduction_factor -= 1;
    changes[5].max_num_variables_to_send_coeffs -= 1;
    changes[6].log_inv_rate += 1;
    for changed in changes {
        assert_ne!(cap, changed.fiat_shamir_domain_sep(&child));
    }
    let mut too_small = profile;
    too_small.first_folding_factor = 2;
    assert!(too_small.validate().is_err());
    let mut narrow = profile;
    narrow.first_folding_factor = 4;
    narrow.rs_domain_initial_reduction_factor = 2;
    assert!(narrow.validate_for_n_vars(29).is_err());
    assert!(profile.validate_for_n_vars(usize::MAX).is_err());
    let mut huge_threshold = profile;
    huge_threshold.max_num_variables_to_send_coeffs = usize::MAX;
    assert!(huge_threshold.validate().is_err());
    let mut more_grinding = profile;
    more_grinding.grinding_bits = 30;
    assert!(more_grinding.validate().is_ok());
    more_grinding.grinding_bits = 31;
    assert!(more_grinding.validate().is_err());
    let mut high_rate = profile;
    high_rate.log_inv_rate = 6;
    high_rate.first_folding_factor = 5;
    assert!(high_rate.validate_for_n_vars(23).is_ok());
    assert!(high_rate.validate_for_n_vars(24).is_err());
    high_rate.log_inv_rate = 7;
    assert!(high_rate.validate().is_err());
}

#[test]
fn fixed_child_shapes_verify_and_bind_the_recursive_program() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            let child = child_bytecode();
            let mut child_profile = WhirExecutionProfile::security_100(2);
            child_profile.first_folding_factor = 4;
            child_profile.subsequent_folding_factor = 4;
            child_profile.rs_domain_initial_reduction_factor = 2;
            child_profile.max_num_variables_to_send_coeffs = 3;
            let mut lift_profile = WhirExecutionProfile::security_100(4);
            lift_profile.first_folding_factor = 5;
            lift_profile.subsequent_folding_factor = 4;
            lift_profile.rs_domain_initial_reduction_factor = 1;
            lift_profile.max_num_variables_to_send_coeffs = 3;
            let node_profile = WhirExecutionProfile::security_100(1);
            let options = RecursiveVerifierOptions {
                horner_evaluation: true,
                fft_poseidon_mds: true,
                extension_subtractions: true,
            };
            let mut input = [F::ZERO; 8];
            input[0] = F::ONE;

            let child_proof =
                prove_execution_with_profile(&child, &input, &ExecutionWitness::default(), &child_profile, false)
                    .unwrap();
            let (_, child_raw) =
                verify_execution_with_profile(&child, &input, child_proof.proof.clone(), &child_profile).unwrap();
            let child_shape = RecursiveChildShape::from_verified_raw_proof(&child_raw).unwrap();
            let lift_code = compile_lifted_execution_bytecode_for_fixed_shape_with_options(
                &child,
                &child_profile,
                &options,
                &child_shape,
            );
            let lifted = lift_execution_proof_with_profiles(
                &child,
                &lift_code,
                &input,
                &child_proof,
                &child_profile,
                &lift_profile,
                false,
            )
            .unwrap();
            let verified_lift =
                verify_lifted_execution_proof_with_profiles(&child, &lift_code, &lifted, &child_profile, &lift_profile)
                    .unwrap();
            let lift_shape = RecursiveChildShape::from_verified_raw_proof(&verified_lift.raw_proof).unwrap();
            let node_code = compile_binary_node_bytecode_for_fixed_shape_with_options(
                &child,
                &lift_code,
                &lift_profile,
                &options,
                &lift_shape,
            );
            let node = prove_binary_node_with_profiles(
                &child,
                &lift_code,
                &node_code,
                [&lifted, &lifted],
                &child_profile,
                &lift_profile,
                &node_profile,
                false,
            )
            .unwrap();
            verify_binary_node_with_profiles(&child, &lift_code, &node_code, &node, &lift_profile, &node_profile)
                .unwrap();

            let mut wrong_shape = lift_shape;
            let changed_table = wrong_shape
                .table_log_heights
                .iter()
                .position(|&log_height| log_height > lean_vm::MIN_LOG_N_ROWS_PER_TABLE)
                .expect("a lifted proof has a non-minimal table");
            wrong_shape.table_log_heights[changed_table] -= 1;
            let wrong_node_code = compile_binary_node_bytecode_for_fixed_shape_with_options(
                &child,
                &lift_code,
                &lift_profile,
                &options,
                &wrong_shape,
            );
            assert_ne!(node_code.hash(), wrong_node_code.hash());
            assert!(
                verify_binary_node_with_profiles(
                    &child,
                    &lift_code,
                    &wrong_node_code,
                    &node,
                    &lift_profile,
                    &node_profile,
                )
                .is_err()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn explicit_profiles_verify_native_and_recursive_execution() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for first_fold in [4, 3] {
                let child = child_bytecode();
                let mut child_profile = WhirExecutionProfile::security_100(2);
                child_profile.first_folding_factor = first_fold;
                child_profile.subsequent_folding_factor = first_fold;
                child_profile.rs_domain_initial_reduction_factor = 2;
                child_profile.max_num_variables_to_send_coeffs = first_fold - 1;
                let mut lift_profile = WhirExecutionProfile::security_100(4);
                lift_profile.first_folding_factor = 5;
                lift_profile.subsequent_folding_factor = 4;
                lift_profile.rs_domain_initial_reduction_factor = 1;
                lift_profile.max_num_variables_to_send_coeffs = 3;
                let node_profile = WhirExecutionProfile::security_100(1);
                let mut input = [F::ZERO; 8];
                input[0] = F::ONE;
                let proof =
                    prove_execution_with_profile(&child, &input, &ExecutionWitness::default(), &child_profile, false)
                        .unwrap();
                verify_execution_with_profile(&child, &input, proof.proof.clone(), &child_profile).unwrap();
                assert!(verify_execution(&child, &input, proof.proof.clone()).is_err());
                let mut wrong_profile = child_profile;
                wrong_profile.security_bits = 99;
                assert!(verify_execution_with_profile(&child, &input, proof.proof.clone(), &wrong_profile).is_err());
                let mut wrong_input = input;
                wrong_input[1] = F::ONE;
                assert!(
                    verify_execution_with_profile(&child, &wrong_input, proof.proof.clone(), &child_profile).is_err()
                );
                let options = RecursiveVerifierOptions {
                    horner_evaluation: first_fold == 3,
                    fft_poseidon_mds: first_fold == 3,
                    extension_subtractions: first_fold == 3,
                };
                let lifted_code = compile_lifted_execution_bytecode_with_options(&child, &child_profile, &options);
                let lifted = lift_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &input,
                    &proof,
                    &child_profile,
                    &lift_profile,
                    false,
                )
                .unwrap();
                let verified_lift = verify_lifted_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &lifted,
                    &child_profile,
                    &lift_profile,
                )
                .unwrap();
                assert!(
                    verify_lifted_execution_proof_with_profiles(
                        &child,
                        &lifted_code,
                        &lifted,
                        &wrong_profile,
                        &lift_profile
                    )
                    .is_err()
                );
                let child_dimension = stacked_dimension(&lifted_code, &verified_lift.raw_proof);
                let node_code = if first_fold == 3 {
                    compile_binary_node_bytecode_for_dimension_with_options(
                        &child,
                        &lifted_code,
                        &lift_profile,
                        &options,
                        child_dimension,
                    )
                } else {
                    compile_binary_node_bytecode_with_options(&child, &lifted_code, &lift_profile, &options)
                };
                let node = prove_binary_node_with_profiles(
                    &child,
                    &lifted_code,
                    &node_code,
                    [&lifted, &lifted],
                    &child_profile,
                    &lift_profile,
                    &node_profile,
                    false,
                )
                .unwrap();
                verify_binary_node_with_profiles(&child, &lifted_code, &node_code, &node, &lift_profile, &node_profile)
                    .unwrap();
                let mut changed_original = node.clone();
                changed_original.info.original_bytecode_claim.value += lean_vm::EF::ONE;
                assert!(
                    verify_binary_node_with_profiles(
                        &child,
                        &lifted_code,
                        &node_code,
                        &changed_original,
                        &lift_profile,
                        &node_profile
                    )
                    .is_err()
                );
                let mut changed_original_point = node.clone();
                changed_original_point.info.original_bytecode_claim.point.0[0] += lean_vm::EF::ONE;
                changed_original_point.info.original_bytecode_claim.value = child
                    .instructions_multilinear()
                    .evaluate_sequential(&changed_original_point.info.original_bytecode_claim.point);
                // This is a valid evaluation of the same fixed original program.
                // The existing node proof must still reject its changed public claim.
                assert!(
                    verify_binary_node_with_profiles(
                        &child,
                        &lifted_code,
                        &node_code,
                        &changed_original_point,
                        &lift_profile,
                        &node_profile
                    )
                    .is_err()
                );
                let mut changed_lifted = node.clone();
                changed_lifted.info.child_bytecode_claim.value += lean_vm::EF::ONE;
                assert!(
                    verify_binary_node_with_profiles(
                        &child,
                        &lifted_code,
                        &node_code,
                        &changed_lifted,
                        &lift_profile,
                        &node_profile
                    )
                    .is_err()
                );
                assert_eq!(node.info.original_bytecode_claim.point.len(), child.cumulated_n_vars());
                assert_eq!(
                    node.info.child_bytecode_claim.point.len(),
                    lifted_code.cumulated_n_vars()
                );
                assert_ne!(child.cumulated_n_vars(), lifted_code.cumulated_n_vars());
                if first_fold == 4 {
                    let (_, node_input, mut witness) = prepare_binary_node_with_profiles(
                        &child,
                        &lifted_code,
                        &node_code,
                        [&lifted, &lifted],
                        &child_profile,
                        &lift_profile,
                    )
                    .unwrap();
                    let slot = node_code.hint_slot("original_bytecode_sumcheck_proof");
                    let valid_reduction = witness.hints.entries(slot)[0].to_vec();
                    let mut invalid_reduction = valid_reduction.clone();
                    invalid_reduction[0] += F::ONE;
                    witness.hints.insert(
                        &node_code,
                        "original_bytecode_sumcheck_proof",
                        arena_vec![ArenaVec::from_slice(&invalid_reduction)],
                    );
                    // Bypass host preparation checks and enter the node guest with
                    // unchanged valid lifted proofs but a false original-bytecode reduction.
                    assert!(try_execute_bytecode(&node_code, &node_input, &witness, false).is_err());
                    witness.hints.insert(
                        &node_code,
                        "original_bytecode_sumcheck_proof",
                        arena_vec![ArenaVec::from_slice(&valid_reduction)],
                    );
                    let slot = node_code.hint_slot("lifted_info");
                    let mut first_info = witness.hints.entries(slot)[0].to_vec();
                    let second_info = witness.hints.entries(slot)[1].to_vec();
                    first_info[8 + child.cumulated_n_vars() * 5] += F::ONE;
                    witness.hints.insert(
                        &node_code,
                        "lifted_info",
                        arena_vec![ArenaVec::from_slice(&first_info), ArenaVec::from_slice(&second_info)],
                    );
                    assert!(try_execute_bytecode(&node_code, &node_input, &witness, false).is_err());
                }
                if first_fold == 3 {
                    let wrong_dimension = (child_dimension + 1..=32)
                        .find(|&n| lift_profile.validate_for_n_vars(n).is_ok())
                        .expect("the test profile has another supported child dimension");
                    let wrong_code = compile_binary_node_bytecode_for_dimension_with_options(
                        &child,
                        &lifted_code,
                        &lift_profile,
                        &options,
                        wrong_dimension,
                    );
                    assert_ne!(node_code.hash(), wrong_code.hash());
                    // These same children verify natively above; rejection must
                    // also happen when their real dimensions enter the guest.
                    assert!(
                        prove_binary_node_with_profiles(
                            &child,
                            &lifted_code,
                            &wrong_code,
                            [&lifted, &lifted],
                            &child_profile,
                            &lift_profile,
                            &node_profile,
                            false,
                        )
                        .is_err()
                    );
                    assert!(
                        verify_binary_node_with_profiles(
                            &child,
                            &lifted_code,
                            &wrong_code,
                            &node,
                            &lift_profile,
                            &node_profile,
                        )
                        .is_err()
                    );
                }
                let mut wrong_node = node.clone();
                wrong_node.info.application_root[0] += F::ONE;
                assert!(
                    verify_binary_node_with_profiles(
                        &child,
                        &lifted_code,
                        &node_code,
                        &wrong_node,
                        &lift_profile,
                        &node_profile
                    )
                    .is_err()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn stacked_dimension(bytecode: &lean_vm::Bytecode, proof: &backend::RawProof<F>) -> usize {
    let dimensions = proof.transcript[..2 + lean_vm::N_TABLES]
        .iter()
        .map(|value| value.as_canonical_u32() as usize)
        .collect::<Vec<_>>();
    let mut maximum_height = bytecode.code().len();
    let mut entries = 2usize << dimensions[1];
    for (index, table) in lean_vm::ALL_TABLES.iter().enumerate() {
        let height = 1usize << dimensions[index + 2];
        maximum_height = maximum_height.max(height);
        entries += table.n_columns() * height;
    }
    (entries + maximum_height).next_power_of_two().ilog2() as usize
}

#[test]
fn native_and_lift_verify_merkle_paths_of_one_and_four_levels() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for (first_fold, expected_final_height) in [(6, 4), (9, 1)] {
                let child = child_bytecode();
                let mut profile = WhirExecutionProfile::security_100(1);
                profile.first_folding_factor = first_fold;
                profile.subsequent_folding_factor = 9;
                profile.rs_domain_initial_reduction_factor = first_fold;
                profile.max_num_variables_to_send_coeffs = 8;
                profile.validate_for_n_vars(18).unwrap();
                let config = backend::WhirConfig::<lean_vm::EF>::new(&profile.whir_config(), 18);
                let final_round = config.final_round_config();
                assert_eq!(
                    final_round.domain_size.ilog2() as usize - final_round.folding_factor,
                    expected_final_height
                );
                let mut input = [F::ZERO; 8];
                input[0] = F::ONE;
                let proof = prove_execution_with_profile(&child, &input, &ExecutionWitness::default(), &profile, false)
                    .unwrap();
                verify_execution_with_profile(&child, &input, proof.proof.clone(), &profile).unwrap();
                let lifted_code = compile_lifted_execution_bytecode_with_profile(&child, &profile);
                let lift_profile = WhirExecutionProfile::security_100(1);
                let lifted = lift_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &input,
                    &proof,
                    &profile,
                    &lift_profile,
                    false,
                )
                .unwrap();
                verify_lifted_execution_proof_with_profiles(&child, &lifted_code, &lifted, &profile, &lift_profile)
                    .unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn native_and_lift_verify_explicit_rates_five_and_six() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for log_inv_rate in [5, 6] {
                let child = child_bytecode();
                let mut profile = WhirExecutionProfile::security_100(log_inv_rate);
                profile.first_folding_factor = 5;
                profile.subsequent_folding_factor = 4;
                profile.rs_domain_initial_reduction_factor = 3;
                profile.max_num_variables_to_send_coeffs = 3;
                profile.validate().unwrap();
                let mut input = [F::ZERO; 8];
                input[0] = F::ONE;
                let proof = prove_execution_with_profile(&child, &input, &ExecutionWitness::default(), &profile, false)
                    .unwrap();
                verify_execution_with_profile(&child, &input, proof.proof.clone(), &profile).unwrap();
                assert!(verify_execution(&child, &input, proof.proof.clone()).is_err());
                let mut wrong_rate = profile;
                wrong_rate.log_inv_rate = if log_inv_rate == 5 { 6 } else { 5 };
                assert!(verify_execution_with_profile(&child, &input, proof.proof.clone(), &wrong_rate,).is_err());
                let lifted_code = compile_lifted_execution_bytecode_with_profile(&child, &profile);
                let lift_profile = WhirExecutionProfile::security_100(1);
                let lifted = lift_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &input,
                    &proof,
                    &profile,
                    &lift_profile,
                    false,
                )
                .unwrap();
                verify_lifted_execution_proof_with_profiles(&child, &lifted_code, &lifted, &profile, &lift_profile)
                    .unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
