#![cfg_attr(not(test), allow(unused_crate_dependencies))]
pub mod benchmark;
mod binary_recursion;
mod bytecode_claims;
mod compilation;
mod error;
mod multi_message_aggregation;
mod single_message_aggregation;

use backend::{Evaluation, Proof, ProofError, RawProof, poseidon_hash_slice};
pub use binary_recursion::{
    BINARY_NODE_INFO_DOMAIN, BinaryNodeInfo, BinaryNodeProof, LIFTED_INFO_DOMAIN, LiftedExecutionInfo,
    LiftedExecutionProof, RECURSIVE_VERIFIER_PREAMBLE_MEMORY_LEN, TERMINAL_C1_EXECUTION_PROGRAM_PREFIX,
    TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS, TERMINAL_NODE_INFO_ADDRESS, TERMINAL_NODE_INFO_SIZE,
    TERMINAL_NODE_PREAMBLE_MEMORY_LEN, TerminalC1FixedPrograms, TerminalC1VerifierPreprocessing,
    binary_application_root, compile_binary_node_bytecode, compile_binary_node_bytecode_for_dimension_with_options,
    compile_binary_node_bytecode_for_fixed_shape_with_options, compile_binary_node_bytecode_with_options,
    compile_binary_node_bytecode_with_profile, compile_lifted_execution_bytecode,
    compile_lifted_execution_bytecode_for_dimension_with_options,
    compile_lifted_execution_bytecode_for_fixed_shape_with_options, compile_lifted_execution_bytecode_with_options,
    compile_lifted_execution_bytecode_with_profile, compile_terminal_binary_node_bytecode_for_dimension_with_options,
    compile_terminal_binary_node_bytecode_for_fixed_shape_with_options,
    compile_terminal_binary_node_bytecode_with_options, lift_execution_proof, lift_execution_proof_with_profiles,
    prepare_binary_node_with_profiles, prepare_terminal_binary_node_with_profiles, prove_binary_node,
    prove_binary_node_with_profiles, prove_binary_node_with_profiles_and_hash,
    prove_terminal_binary_node_c1_v1_with_preprocessing, prove_terminal_binary_node_c1_v1_with_profiles,
    prove_terminal_binary_node_with_profiles_and_hash, terminal_binary_node_public_memory,
    terminal_c1_execution_program_prefix, terminal_c1_fixed_programs, terminal_c1_fixed_programs_for_dimension,
    terminal_c1_statement_public_memory_bindings, terminal_c1_statement_public_memory_bindings_for_dimension,
    verify_binary_node, verify_binary_node_with_profiles, verify_binary_node_with_profiles_and_hash,
    verify_lifted_execution_proof, verify_lifted_execution_proof_with_profiles,
    verify_terminal_binary_node_c1_v1_with_preprocessing, verify_terminal_binary_node_c1_v1_with_profiles,
    verify_terminal_binary_node_with_profiles_and_hash,
};
pub use compilation::{
    MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN,
    RecursiveChildShape, RecursiveVerifierOptions, ZERO_VEC_LEN, get_aggregation_bytecode, init_aggregation_bytecode,
};
pub use error::AggregationError;
pub use lean_prover::ProverError;
use lean_prover::verify_execution::verify_execution;
use lean_vm::{DIGEST_LEN, EF, F};
pub use multi_message_aggregation::{
    MultiMessageAggregateSignature, merge_single_message_aggregates, split_multi_message_aggregate,
    split_multi_message_aggregate_by_message, verify_multi_message_aggregate,
};
pub use single_message_aggregation::{
    SingleMessageAggregateSignature, SingleMessageCore, SingleMessageInfo, aggregate_single_message_signatures,
    verify_single_message_aggregate,
};

#[allow(missing_debug_implementations)]
pub struct InnerVerified {
    pub input_data: Vec<F>,
    pub input_data_hash: [F; DIGEST_LEN],
    pub bytecode_evaluation: Evaluation<EF>,
    pub raw_proof: RawProof<F>,
    pub sorted_table_perm: Vec<usize>,
}

pub(crate) fn verify_inner(input_data: Vec<F>, proof: Proof<F>) -> Result<InnerVerified, ProofError> {
    let input_data_hash = poseidon_hash_slice(&input_data);
    let bytecode = get_aggregation_bytecode();
    let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, proof)?;
    Ok(InnerVerified {
        input_data,
        input_data_hash,
        bytecode_evaluation: verif.bytecode_evaluation,
        raw_proof,
        sorted_table_perm: verif.sorted_table_perm,
    })
}

pub use binary_recursion::{
    prove_terminal_binary_node_grouped_logup_with_preprocessing,
    verify_terminal_binary_node_grouped_logup_with_preprocessing,
};
