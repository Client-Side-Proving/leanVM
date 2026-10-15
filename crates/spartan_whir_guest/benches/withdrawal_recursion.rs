use std::{env, fs, hint::black_box, path::Path, time::Duration};

use backend::{Air, PrimeField32, ProofHashProfile, RawProof};
use criterion::{BatchSize, BenchmarkId, Criterion, SamplingMode};
use lean_prover::{
    WhirExecutionProfile,
    prove_execution::{ExecutionProof, prove_execution_with_profile},
    verify_execution::verify_execution_with_profile,
};
use rec_aggregation::{
    RecursiveVerifierOptions, compile_binary_node_bytecode_for_dimension_with_options,
    compile_binary_node_bytecode_with_options, compile_lifted_execution_bytecode_for_dimension_with_options,
    compile_lifted_execution_bytecode_with_options, lift_execution_proof_with_profiles,
    prove_binary_node_with_profiles_and_hash, verify_binary_node_with_profiles_and_hash,
    verify_lifted_execution_proof_with_profiles,
};
use serde::Deserialize;
use spartan_whir_guest::{SparkGuestFixture, SparkGuestOptimizations};

#[derive(Deserialize)]
struct Case {
    name: String,
    direct: WhirExecutionProfile,
    lift: WhirExecutionProfile,
    node: WhirExecutionProfile,
    #[serde(default)]
    verifier_options: RecursiveVerifierOptions,
    #[serde(default)]
    node_child_num_variables: Option<usize>,
    #[serde(default)]
    lift_child_num_variables: Option<usize>,
    #[serde(default)]
    guest_extension_arithmetic: bool,
    #[serde(default)]
    guest_transcript_blocks: bool,
    #[serde(default)]
    terminal_keccak: bool,
    #[serde(default)]
    expected_root_num_variables: Option<usize>,
}

impl Case {
    fn terminal_hash(&self) -> ProofHashProfile {
        if self.terminal_keccak {
            ProofHashProfile::Keccak240
        } else {
            ProofHashProfile::Poseidon1
        }
    }
}

fn record_geometry(
    layer: &str,
    sample: usize,
    bytecode: &lean_vm::Bytecode,
    proof: &ExecutionProof,
    raw: &RawProof<lean_vm::F>,
) -> usize {
    let dimensions: Vec<_> = raw.transcript[..2 + lean_vm::N_TABLES]
        .iter()
        .map(|value| value.as_canonical_u32() as usize)
        .collect();
    let mut height = bytecode.code().len();
    let mut entries = 2usize << dimensions[1];
    for (index, table) in lean_vm::ALL_TABLES.iter().enumerate() {
        let rows = 1usize << dimensions[index + 2];
        height = height.max(rows);
        entries += rows * table.n_columns();
    }
    entries += height;
    let variables = entries.next_power_of_two().ilog2() as usize;
    let metadata = proof.metadata.as_ref().expect("execution metadata is recorded");
    println!(
        "validation_geometry: {}",
        serde_json::json!({
            "layer": layer, "sample": sample, "stacked_entries": entries, "stacked_num_variables": variables,
            "raw": {"execution_rows": metadata.cycles, "extension_rows": metadata.n_extension_ops,
                    "poseidon_calls": metadata.n_poseidons, "memory_cells": metadata.memory},
            "proof_bytes": postcard::to_allocvec(&proof.proof).unwrap().len(),
        })
    );
    variables
}

fn benchmark(c: &mut Criterion) {
    let directories: Vec<String> = serde_json::from_str(
        &env::var("LEANVM_WITHDRAWAL_FIXTURES").expect("set LEANVM_WITHDRAWAL_FIXTURES to a JSON directory list"),
    )
    .unwrap();
    assert!(directories.len() >= 2, "use at least two distinct withdrawals");
    let cases: Vec<Case> = serde_json::from_slice(
        &fs::read(env::var("LEANVM_RECURSION_CASES").expect("set LEANVM_RECURSION_CASES to a JSON case file")).unwrap(),
    )
    .unwrap();
    let mut options = SparkGuestOptimizations::recommended();
    let guest_extension_arithmetic = cases.first().expect("at least one case").guest_extension_arithmetic;
    let guest_transcript_blocks = cases.first().unwrap().guest_transcript_blocks;
    assert!(
        cases
            .iter()
            .all(|case| case.guest_extension_arithmetic == guest_extension_arithmetic
                && case.guest_transcript_blocks == guest_transcript_blocks),
        "compare guest options in separate runs with matching case files"
    );
    options.extension_arithmetic = guest_extension_arithmetic;
    options.transcript_blocks = guest_transcript_blocks;
    let fixtures: Vec<_> = directories
        .iter()
        .map(|directory| {
            SparkGuestFixture::from_directory(Path::new(directory))
                .unwrap()
                .with_fixed_sibling_storage()
                .unwrap()
        })
        .collect();
    let child = fixtures[0].compile(&options).unwrap().bytecode;
    let mut inputs = Vec::new();
    let mut witnesses = Vec::new();
    for fixture in &fixtures {
        assert_eq!(fixture.compile(&options).unwrap().bytecode.hash(), child.hash());
        let input = fixture.public_input().unwrap();
        assert!(!inputs.contains(&input), "each corpus statement must differ");
        inputs.push(input);
        let words = fixture.compact_words(&options).unwrap();
        witnesses.push(fixture.execution_witness(&child, &words, &options).unwrap());
    }
    println!("effective_threads: {}", system_info::num_threads());
    println!("distinct_application_statements: {}", inputs.len());
    let mut group = c.benchmark_group("privacy_pools_leanvm_recursion");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(5))
        .measurement_time(Duration::from_secs(30))
        .sampling_mode(SamplingMode::Flat);
    for case in cases {
        for profile in [&case.direct, &case.lift, &case.node] {
            profile.validate().unwrap();
            assert_eq!(profile.security_bits, 100);
        }
        let lifted_code = match case.lift_child_num_variables {
            Some(dimension) => compile_lifted_execution_bytecode_for_dimension_with_options(
                &child,
                &case.direct,
                &case.verifier_options,
                dimension,
            ),
            None => compile_lifted_execution_bytecode_with_options(&child, &case.direct, &case.verifier_options),
        };
        let node_code = match case.node_child_num_variables {
            Some(dimension) => compile_binary_node_bytecode_for_dimension_with_options(
                &child,
                &lifted_code,
                &case.lift,
                &case.verifier_options,
                dimension,
            ),
            None => compile_binary_node_bytecode_with_options(&child, &lifted_code, &case.lift, &case.verifier_options),
        };
        let direct: Vec<_> = (0..inputs.len())
            .map(|i| {
                let proof = prove_execution_with_profile(&child, &inputs[i], &witnesses[i], &case.direct, false)
                    .expect("direct execution proof succeeds");
                let (_, raw) = verify_execution_with_profile(&child, &inputs[i], proof.proof.clone(), &case.direct)
                    .expect("direct execution proof verifies");
                let variables = record_geometry("direct", i, &child, &proof, &raw);
                if let Some(expected) = case.lift_child_num_variables {
                    assert_eq!(variables, expected);
                }
                proof
            })
            .collect();
        let lifts: Vec<_> = (0..inputs.len())
            .map(|i| {
                let proof = lift_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &inputs[i],
                    &direct[i],
                    &case.direct,
                    &case.lift,
                    false,
                )
                .expect("lift proving succeeds");
                let verified =
                    verify_lifted_execution_proof_with_profiles(&child, &lifted_code, &proof, &case.direct, &case.lift)
                        .expect("lift verifies");
                let variables = record_geometry("lift", i, &lifted_code, &proof.proof, &verified.raw_proof);
                if let Some(expected) = case.node_child_num_variables {
                    assert_eq!(variables, expected);
                }
                proof
            })
            .collect();
        for i in 0..inputs.len() {
            let node = prove_binary_node_with_profiles_and_hash(
                &child,
                &lifted_code,
                &node_code,
                [&lifts[i], &lifts[(i + 1) % lifts.len()]],
                &case.direct,
                &case.lift,
                &case.node,
                case.terminal_hash(),
                false,
            )
            .expect("binary node proving succeeds");
            let verified = verify_binary_node_with_profiles_and_hash(
                &child,
                &lifted_code,
                &node_code,
                &node,
                &case.lift,
                &case.node,
                case.terminal_hash(),
            )
            .expect("binary node verifies");
            let variables = record_geometry("binary_root", i, &node_code, &node.proof, &verified.raw_proof);
            if let Some(expected) = case.expected_root_num_variables {
                assert_eq!(variables, expected);
            }
        }
        let mut cursor = 0usize;
        group.bench_with_input(BenchmarkId::new("direct", &case.name), &case, |b, case| {
            b.iter_batched(
                || {
                    let i = cursor % inputs.len();
                    cursor += 1;
                    i
                },
                |i| {
                    black_box(
                        prove_execution_with_profile(
                            black_box(&child),
                            black_box(&inputs[i]),
                            black_box(&witnesses[i]),
                            black_box(&case.direct),
                            false,
                        )
                        .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            );
        });
        group.bench_with_input(BenchmarkId::new("lift", &case.name), &case, |b, case| {
            b.iter_batched(
                || {
                    let i = cursor % inputs.len();
                    cursor += 1;
                    i
                },
                |i| {
                    black_box(
                        lift_execution_proof_with_profiles(
                            black_box(&child),
                            black_box(&lifted_code),
                            black_box(&inputs[i]),
                            black_box(&direct[i]),
                            black_box(&case.direct),
                            black_box(&case.lift),
                            false,
                        )
                        .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            );
        });
        group.bench_with_input(BenchmarkId::new("binary_root", &case.name), &case, |b, case| {
            b.iter_batched(
                || {
                    let i = cursor % inputs.len();
                    cursor += 1;
                    i
                },
                |i| {
                    black_box(
                        prove_binary_node_with_profiles_and_hash(
                            black_box(&child),
                            black_box(&lifted_code),
                            black_box(&node_code),
                            black_box([&lifts[i], &lifts[(i + 1) % lifts.len()]]),
                            black_box(&case.direct),
                            black_box(&case.lift),
                            black_box(&case.node),
                            case.terminal_hash(),
                            false,
                        )
                        .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            );
        });
    }
    group.finish();
}

fn main() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let mut c = Criterion::default().configure_from_args();
            benchmark(&mut c);
            c.final_summary();
        })
        .unwrap()
        .join()
        .unwrap();
}
