use backend::*;
use lean_compiler::{ProgramSource, compile_program};
use lean_prover::prove_execution::*;
use lean_prover::verify_execution::*;
use lean_prover::*;
use lean_vm::*;

#[test]
fn grouped_execution_entry_point_binds_program_public_memory_and_mode() {
    let bytecode = compile_program(&ProgramSource::Raw(
        r#"
def main():
    data = Array(3000)
    for i in unroll(0, 3000):
        data[i] = i
    public_region = fixed_address()
    for i in unroll(0, 32):
        public_region[i] = 0
    return

def fixed_address():
    return 4096
"#
        .to_owned(),
    ));
    let public = [F::ZERO; PUBLIC_INPUT_LEN];
    let witness = ExecutionWitness {
        preamble_memory_len: 4128,
        ..Default::default()
    };
    let region = PublicMemoryRegion {
        start: 4096,
        values: vec![F::ZERO; 32],
    };
    let trace = get_execution_trace(
        &bytecode,
        try_execute_bytecode(&bytecode, &public, &witness, false).unwrap(),
        &witness.min_table_log_n_rows,
    );
    let memory_len = trace
        .memory
        .len()
        .max(1 << MIN_LOG_MEMORY_SIZE)
        .max(bytecode.padded_size());
    let max_height = trace
        .traces
        .values()
        .map(|t| t.log_n_rows)
        .max()
        .unwrap()
        .max(bytecode.log_size());
    let entries = 2 * memory_len
        + (1 << max_height)
        + trace
            .traces
            .iter()
            .map(|(t, x)| t.n_columns() << x.log_n_rows)
            .sum::<usize>();
    println!(
        "test geometry: program {}, primary {}, tables {:?}",
        bytecode.cumulated_n_vars() + 2,
        log2_ceil_usize(entries),
        trace
            .traces
            .iter()
            .map(|(t, x)| (t.name(), x.log_n_rows))
            .collect::<Vec<_>>()
    );
    drop(trace);
    let n_vars = bytecode.cumulated_n_vars() + 2;
    let offset = 3 << bytecode.cumulated_n_vars();
    let mut fixed_values = vec![F::ZERO; 1 << n_vars];
    fixed_values[offset..].copy_from_slice(bytecode.instructions_multilinear());
    let fixed = MleOwned::<EF>::Base(ArenaVec::from_iter(fixed_values));
    let profile = WhirExecutionProfile {
        security_bits: 40,
        grinding_bits: 0,
        first_folding_factor: 3,
        subsequent_folding_factor: 3,
        rs_domain_initial_reduction_factor: 3,
        max_num_variables_to_send_coeffs: 4,
        log_inv_rate: 1,
    };
    let preprocessed =
        preprocess_two_commitment_whir_secondary(&fixed, 1 << n_vars, &profile, ProofHashProfile::Keccak240).unwrap();
    let statements = vec![SparseStatement::unique_value(n_vars, 0, EF::ZERO)];
    let bindings = vec![TwoCommitmentWhirStatementBinding {
        public_memory_offset: 0,
        point_prefix: vec![],
    }];
    let prover_input = TwoCommitmentWhirProverInput {
        secondary_polynomial: fixed,
        secondary_actual_data_len: 1 << n_vars,
        secondary_commitment: preprocessed.clone(),
        secondary_statements: statements.clone(),
        secondary_statement_public_memory_bindings: bindings.clone(),
        execution_bytecode_point_prefix: vec![EF::ONE, EF::ONE],
        two_commitment_batching_pow_bits: TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
    };
    let verifier_input = TwoCommitmentWhirVerifierInput {
        secondary_num_variables: n_vars,
        secondary_actual_data_len: 1 << n_vars,
        expected_secondary_root: preprocessed.root,
        secondary_statements: statements,
        secondary_statement_public_memory_bindings: bindings,
        execution_bytecode_point_prefix: vec![EF::ONE, EF::ONE],
        two_commitment_batching_pow_bits: TWO_COMMITMENT_WHIR_BATCHING_POW_BITS,
    };
    let proof = prove_execution_with_grouped_logup(
        &bytecode,
        &public,
        &witness,
        &profile,
        ProofHashProfile::Keccak240,
        Some(&region),
        prover_input.clone(),
        false,
    )
    .unwrap();
    let verify = |p: Proof<F>,
                  input: &[F; PUBLIC_INPUT_LEN],
                  region: &PublicMemoryRegion,
                  fixed: TwoCommitmentWhirVerifierInput| {
        verify_execution_with_grouped_logup(
            &bytecode,
            input,
            p,
            &profile,
            ProofHashProfile::Keccak240,
            Some(region),
            fixed,
        )
    };
    let (details, _) = verify(proof.proof.clone(), &public, &region, verifier_input.clone()).unwrap();
    assert_eq!(
        bytecode
            .instructions_multilinear()
            .evaluate(&details.bytecode_evaluation.point),
        details.bytecode_evaluation.value
    );
    // A valid proof of the prior mode must not be accepted in this mode, or vice versa.
    assert!(
        verify_execution_with_two_commitment_whir(
            &bytecode,
            &public,
            proof.proof.clone(),
            &profile,
            ProofHashProfile::Keccak240,
            Some(&region),
            verifier_input.clone()
        )
        .is_err()
    );
    let legacy = prove_execution_with_two_commitment_whir(
        &bytecode,
        &public,
        &witness,
        &profile,
        ProofHashProfile::Keccak240,
        Some(&region),
        prover_input.clone(),
        false,
    )
    .unwrap();
    verify_execution_with_two_commitment_whir(
        &bytecode,
        &public,
        legacy.proof.clone(),
        &profile,
        ProofHashProfile::Keccak240,
        Some(&region),
        verifier_input.clone(),
    )
    .unwrap();
    assert!(verify(legacy.proof, &public, &region, verifier_input.clone()).is_err());
    let mut changed = public;
    changed[1] += F::ONE;
    assert!(verify(proof.proof.clone(), &changed, &region, verifier_input.clone()).is_err());
    let mut changed_region = region.clone();
    changed_region.values[20] += F::ONE;
    assert!(verify(proof.proof.clone(), &public, &changed_region, verifier_input.clone()).is_err());
    changed_region = region.clone();
    changed_region.start += 32;
    assert!(verify(proof.proof.clone(), &public, &changed_region, verifier_input.clone()).is_err());
    let mut changed_fixed = verifier_input.clone();
    changed_fixed.expected_secondary_root[0] += F::ONE;
    assert!(verify(proof.proof.clone(), &public, &region, changed_fixed).is_err());
    changed_fixed = verifier_input.clone();
    changed_fixed.secondary_statements[0].values[0].value = EF::ONE;
    assert!(verify(proof.proof.clone(), &public, &region, changed_fixed).is_err());
    changed_fixed = verifier_input.clone();
    changed_fixed.secondary_statement_public_memory_bindings[0].public_memory_offset = 1;
    assert!(verify(proof.proof.clone(), &public, &region, changed_fixed).is_err());
    assert!(
        prove_execution_with_grouped_logup(
            &bytecode,
            &public,
            &witness,
            &profile,
            ProofHashProfile::Poseidon1,
            Some(&region),
            prover_input.clone(),
            false
        )
        .is_err()
    );
    assert!(
        prove_execution_with_grouped_logup(
            &bytecode,
            &public,
            &witness,
            &profile,
            ProofHashProfile::Keccak240,
            None,
            prover_input,
            false
        )
        .is_err()
    );
    let mut short = serde_json::to_value(&proof.proof).unwrap();
    short["transcript"].as_array_mut().unwrap().pop();
    let short = serde_json::from_value(short).unwrap();
    assert!(verify(short, &public, &region, verifier_input.clone()).is_err());
    let mut extra = serde_json::to_value(&proof.proof).unwrap();
    extra["transcript"]
        .as_array_mut()
        .unwrap()
        .push(serde_json::to_value(F::ZERO).unwrap());
    let extra = serde_json::from_value(extra).unwrap();
    assert!(verify(extra, &public, &region, verifier_input).is_err());
    println!(
        "grouped execution API: 2^{n_vars}; 12 negative cases; legacy mode roundtrip; diagnostic bytecode evaluation authenticated"
    );
}
