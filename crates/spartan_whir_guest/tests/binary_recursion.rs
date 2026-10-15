use rec_aggregation::{compile_binary_node_bytecode, compile_lifted_execution_bytecode};
use spartan_whir_guest::{SparkGuestOptimizations, compile_full_zk_spark_poseidon1_guest_with_optimizations};

#[test]
fn production_lift_and_binary_node_fit_the_supported_program_sizes() {
    check_program_sizes(&SparkGuestOptimizations::default());
}

#[test]
fn optimized_lift_and_binary_node_fit_the_supported_program_sizes() {
    check_program_sizes(&SparkGuestOptimizations::recommended());
}

fn check_program_sizes(options: &SparkGuestOptimizations) {
    let child = compile_full_zk_spark_poseidon1_guest_with_optimizations(options)
        .unwrap()
        .bytecode;
    let lifted = compile_lifted_execution_bytecode(&child);
    let node = compile_binary_node_bytecode(&child, &lifted);
    assert!(child.log_size() <= 19);
    assert!(lifted.log_size() <= 18);
    assert!(node.log_size() <= 18);
}
