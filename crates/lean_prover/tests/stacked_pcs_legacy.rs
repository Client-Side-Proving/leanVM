use std::collections::BTreeMap;

use backend::{
    Air, ArenaVec, FoldingFactor, PrimeCharacteristicRing, ProverState, SecurityAssumption, WhirConfig,
    WhirConfigBuilder, default_koalabear_poseidon1_16,
};
use lean_vm::{ALL_TABLES, EF, F, MIN_LOG_N_ROWS_PER_TABLE, TableTrace};
use sub_protocols::{stack_polynomials, stack_polynomials_and_commit};

fn synthetic_stacked_inputs() -> (Vec<F>, Vec<F>, Vec<F>, BTreeMap<lean_vm::Table, TableTrace>) {
    let n_rows = 1 << MIN_LOG_N_ROWS_PER_TABLE;
    let memory = (0..n_rows).map(|index| F::from_usize(index + 1)).collect();
    let memory_acc = (0..n_rows).map(|index| F::from_usize(3 * index + 2)).collect();
    let bytecode_acc = (0..n_rows).map(|index| F::from_usize(5 * index + 4)).collect();
    let traces = ALL_TABLES
        .into_iter()
        .map(|table| {
            let columns = (0..table.n_columns())
                .map(|column| {
                    ArenaVec::from_iter((0..n_rows).map(|row| F::from_usize(11 * table.index() + 7 * column + row + 1)))
                })
                .collect();
            (
                table,
                TableTrace {
                    columns,
                    non_padded_n_rows: n_rows,
                    log_n_rows: MIN_LOG_N_ROWS_PER_TABLE,
                },
            )
        })
        .collect();
    (memory, memory_acc, bytecode_acc, traces)
}

#[test]
fn legacy_commit_wrapper_matches_extracted_stack_path() {
    let (memory, memory_acc, bytecode_acc, traces) = synthetic_stacked_inputs();
    let stacked = stack_polynomials(&memory, &memory_acc, &bytecode_acc, &traces);
    let builder = WhirConfigBuilder {
        security_level: 100,
        max_num_variables_to_send_coeffs: 3,
        pow_bits: 12,
        folding_factor: FoldingFactor::new(4, 3),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 1,
        rs_domain_initial_reduction_factor: 3,
    };
    let permutation = default_koalabear_poseidon1_16();
    let capacity = [F::from_u32(37); 8];

    let mut wrapper = ProverState::<EF, _>::new(permutation.clone(), capacity);
    stack_polynomials_and_commit(&mut wrapper, &builder, &memory, &memory_acc, &bytecode_acc, &traces);

    let mut extracted = ProverState::<EF, _>::new(permutation, capacity);
    WhirConfig::new(&builder, stacked.stacked_n_vars).commit(
        &mut extracted,
        &stacked.global_polynomial,
        stacked.actual_data_len,
    );

    assert_eq!(wrapper.into_proof(), extracted.into_proof());
}
