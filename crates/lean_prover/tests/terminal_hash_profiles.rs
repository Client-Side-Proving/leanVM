use backend::{EvaluationsList, PrimeCharacteristicRing, ProofHashProfile};
use lean_compiler::{ProgramSource, compile_program};
use lean_prover::{
    WhirExecutionProfile,
    prove_execution::{prove_execution_with_profile, prove_execution_with_profile_and_hash},
    verify_execution::{verify_execution_with_profile, verify_execution_with_profile_and_hash},
};
use lean_vm::{ExecutionWitness, F, PUBLIC_INPUT_LEN};

#[test]
fn terminal_hash_profiles_verify_complete_execution_and_reject_changed_context() {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            let compile = |expected| {
                compile_program(&ProgramSource::Raw(format!(
                    "def main():\n    public = 0\n    assert public[0] == {expected}\n    return\n"
                )))
            };
            let bytecode = compile(1);
            let changed_bytecode = compile(2);
            assert_eq!(bytecode.cumulated_n_vars(), changed_bytecode.cumulated_n_vars());
            let profile = WhirExecutionProfile {
                security_bits: 100,
                grinding_bits: 12,
                first_folding_factor: 4,
                subsequent_folding_factor: 3,
                rs_domain_initial_reduction_factor: 3,
                max_num_variables_to_send_coeffs: 3,
                log_inv_rate: 4,
            };
            let mut input = [F::ZERO; PUBLIC_INPUT_LEN];
            input[0] = F::ONE;
            let mut changed_input = input;
            changed_input[1] = F::ONE;
            let mut changed_profile = profile;
            changed_profile.security_bits -= 1;
            let mut excessive_security = profile;
            excessive_security.security_bits = 121;
            assert!(
                excessive_security
                    .validate_for_hash(ProofHashProfile::Poseidon1)
                    .is_ok()
            );
            assert!(
                excessive_security
                    .validate_for_hash(ProofHashProfile::Keccak240)
                    .is_err()
            );
            assert!(
                prove_execution_with_profile_and_hash(
                    &bytecode,
                    &input,
                    &ExecutionWitness::default(),
                    &excessive_security,
                    ProofHashProfile::Keccak240,
                    false,
                )
                .is_err()
            );

            for hash_profile in [ProofHashProfile::Poseidon1, ProofHashProfile::Keccak240] {
                let witness = ExecutionWitness::default();
                let proof = if hash_profile == ProofHashProfile::Poseidon1 {
                    prove_execution_with_profile(&bytecode, &input, &witness, &profile, false).unwrap()
                } else {
                    prove_execution_with_profile_and_hash(&bytecode, &input, &witness, &profile, hash_profile, false)
                        .unwrap()
                };
                let (details, _) = verify_execution_with_profile_and_hash(
                    &bytecode,
                    &input,
                    proof.proof.clone(),
                    &profile,
                    hash_profile,
                )
                .unwrap();
                assert!(
                    verify_execution_with_profile_and_hash(
                        &bytecode,
                        &input,
                        proof.proof.clone(),
                        &excessive_security,
                        ProofHashProfile::Keccak240,
                    )
                    .is_err()
                );
                assert_eq!(
                    details.bytecode_evaluation.value,
                    bytecode
                        .instructions_multilinear()
                        .evaluate_sequential(&details.bytecode_evaluation.point)
                );
                if hash_profile == ProofHashProfile::Poseidon1 {
                    verify_execution_with_profile(&bytecode, &input, proof.proof.clone(), &profile).unwrap();
                }
                let other_hash = if hash_profile == ProofHashProfile::Poseidon1 {
                    ProofHashProfile::Keccak240
                } else {
                    ProofHashProfile::Poseidon1
                };
                assert!(
                    verify_execution_with_profile_and_hash(
                        &bytecode,
                        &input,
                        proof.proof.clone(),
                        &profile,
                        other_hash,
                    )
                    .is_err()
                );
                for (program, public, settings) in [
                    (&bytecode, &changed_input, &profile),
                    (&changed_bytecode, &input, &profile),
                    (&bytecode, &input, &changed_profile),
                ] {
                    assert!(
                        verify_execution_with_profile_and_hash(
                            program,
                            public,
                            proof.proof.clone(),
                            settings,
                            hash_profile,
                        )
                        .is_err()
                    );
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
