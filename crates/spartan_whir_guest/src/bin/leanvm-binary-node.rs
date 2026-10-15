use std::error::Error;
use std::time::Instant;

use backend::{PrimeCharacteristicRing, PrimeField32};
use lean_vm::TableT;
use rec_aggregation::{
    compile_binary_node_bytecode, compile_lifted_execution_bytecode, lift_execution_proof, prove_binary_node,
    verify_binary_node, verify_lifted_execution_proof,
};
use serde_json::json;
use spartan_whir_guest::{
    CONTROL_ROOT_LOG_INV_RATE, FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE, SparkGuestFixture, SparkGuestOptimizations,
    compile_control_guest, control_public_input, control_words, prove_control_guest,
};

fn main() {
    let result = std::thread::Builder::new()
        .name("leanvm-binary-node".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| run().map_err(|error| error.to_string()))
        .expect("spawn binary-node compiler thread")
        .join()
        .expect("binary-node compiler thread panicked");
    if let Err(error) = result {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mode = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "compile-production".to_string());
    match mode.as_str() {
        "compile-production" => compile_production(&SparkGuestOptimizations::default()),
        "prove-production" => prove_production(&SparkGuestOptimizations::default()),
        "compile-optimized" => compile_production(&SparkGuestOptimizations::recommended()),
        "prove-optimized" => prove_production(&SparkGuestOptimizations::recommended()),
        "smoke-control" => smoke_control(),
        _ => Err(format!("expected compile-production, prove-production, compile-optimized, prove-optimized, or smoke-control; got {mode}").into()),
    }
}

fn compile_production(options: &SparkGuestOptimizations) -> Result<(), Box<dyn Error>> {
    let child_start = Instant::now();
    let external_fixture = std::env::args()
        .nth(2)
        .map(|directory| SparkGuestFixture::from_directory(std::path::Path::new(&directory)))
        .transpose()?;
    let fixture = match &external_fixture {
        Some(fixture) => fixture,
        None => SparkGuestFixture::embedded()?,
    };
    let child = fixture.compile(options)?.bytecode;
    let child_elapsed = child_start.elapsed();
    let lifted_start = Instant::now();
    let lifted = compile_lifted_execution_bytecode(&child);
    let lifted_elapsed = lifted_start.elapsed();
    let node_start = Instant::now();
    let node = compile_binary_node_bytecode(&child, &lifted);
    let node_elapsed = node_start.elapsed();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "profile": "spartan-whir-poseidon1-full-zk-spark-binary-node-v1",
            "optimized": options.uses_compact_input(),
            "child": bytecode_report(&child, child_elapsed.as_secs_f64()),
            "lifted": bytecode_report(&lifted, lifted_elapsed.as_secs_f64()),
            "node": bytecode_report(&node, node_elapsed.as_secs_f64()),
            "node_arity": 2,
            "node_child_type": "lifted execution proof",
            "node_application_root": "Poseidon1(domain, left application digest, right application digest)",
        }))?
    );
    Ok(())
}

fn smoke_control() -> Result<(), Box<dyn Error>> {
    let child = compile_control_guest()?.bytecode;
    let public_input = control_public_input()?;
    let words = control_words()?;
    let child_root = prove_control_guest(&child, &public_input, &words)?;

    let lifted_bytecode = compile_lifted_execution_bytecode(&child);
    let lifted_start = Instant::now();
    let lifted = lift_execution_proof(
        &child,
        &lifted_bytecode,
        &public_input,
        &child_root.proof,
        CONTROL_ROOT_LOG_INV_RATE,
    )?;
    let lifted_elapsed = lifted_start.elapsed();
    let lifted_verification = verify_lifted_execution_proof(&child, &lifted_bytecode, &lifted)?;

    let node_bytecode = compile_binary_node_bytecode(&child, &lifted_bytecode);
    let node_start = Instant::now();
    let node = prove_binary_node(
        &child,
        &lifted_bytecode,
        &node_bytecode,
        [&lifted, &lifted],
        CONTROL_ROOT_LOG_INV_RATE,
    )?;
    let node_elapsed = node_start.elapsed();
    let node_verification = verify_binary_node(&child, &lifted_bytecode, &node_bytecode, &node)?;
    check_public_claim_rejections(&child, &lifted_bytecode, &node_bytecode, &lifted, &node)?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "profile": "control-binary-node-smoke-v1",
            "child_proving_ms": child_root.proving_elapsed.as_secs_f64() * 1_000.0,
            "lifted_proving_ms": lifted_elapsed.as_secs_f64() * 1_000.0,
            "node_proving_ms": node_elapsed.as_secs_f64() * 1_000.0,
            "lifted_proof_bytes": postcard::to_allocvec(&lifted.proof.proof)?.len(),
            "node_proof_bytes": postcard::to_allocvec(&node.proof.proof)?.len(),
            "lifted_proof_shape": proof_shape(&lifted_verification.raw_proof),
            "node_proof_shape": proof_shape(&node_verification.raw_proof),
            "public_claim_mutations": "lifted application digest and binary application root rejected",
            "application_root": node.info.application_root
                .iter()
                .map(|value| value.as_canonical_u32())
                .collect::<Vec<_>>(),
            "native_verification": "passed",
        }))?
    );
    Ok(())
}

fn prove_production(options: &SparkGuestOptimizations) -> Result<(), Box<dyn Error>> {
    let external_fixture = std::env::args()
        .nth(2)
        .map(|directory| SparkGuestFixture::from_directory(std::path::Path::new(&directory)))
        .transpose()?;
    let fixture = match &external_fixture {
        Some(fixture) => fixture,
        None => SparkGuestFixture::embedded()?,
    };
    let child = fixture.compile(options)?.bytecode;
    let public_input = fixture.public_input()?;
    let words = fixture.compact_words(options)?;
    let child_root = fixture.prove(&child, &words, options)?;

    let lifted_bytecode = compile_lifted_execution_bytecode(&child);
    let lifted_start = Instant::now();
    let lifted = lift_execution_proof(
        &child,
        &lifted_bytecode,
        &public_input,
        &child_root.proof,
        FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE,
    )?;
    let lifted_elapsed = lifted_start.elapsed();
    let lifted_verification_start = Instant::now();
    let lifted_verification = verify_lifted_execution_proof(&child, &lifted_bytecode, &lifted)?;
    let lifted_verification_elapsed = lifted_verification_start.elapsed();

    let node_bytecode = compile_binary_node_bytecode(&child, &lifted_bytecode);
    let node_start = Instant::now();
    let node = prove_binary_node(
        &child,
        &lifted_bytecode,
        &node_bytecode,
        [&lifted, &lifted],
        FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE,
    )?;
    let node_elapsed = node_start.elapsed();
    let node_verification_start = Instant::now();
    let node_verification = verify_binary_node(&child, &lifted_bytecode, &node_bytecode, &node)?;
    let node_verification_elapsed = node_verification_start.elapsed();
    check_public_claim_rejections(&child, &lifted_bytecode, &node_bytecode, &lifted, &node)?;
    let lifted_serialization_start = Instant::now();
    let lifted_proof_bytes = postcard::to_allocvec(&lifted.proof.proof)?.len();
    let lifted_serialization_elapsed = lifted_serialization_start.elapsed();
    let node_serialization_start = Instant::now();
    let node_proof_bytes = postcard::to_allocvec(&node.proof.proof)?.len();
    let node_serialization_elapsed = node_serialization_start.elapsed();

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "profile": "spartan-whir-poseidon1-full-zk-spark-binary-node-v1",
            "optimized": options.uses_compact_input(),
            "children": "the same valid lifted production proof supplied in both ordered child slots",
            "child_proving_ms": child_root.proving_elapsed.as_secs_f64() * 1_000.0,
            "child_proof_bytes": child_root.serialized_proof_bytes,
            "child_verification_ms": child_root.verification_elapsed.as_secs_f64() * 1_000.0,
            "lifted_proving_ms": lifted_elapsed.as_secs_f64() * 1_000.0,
            "node_proving_ms": node_elapsed.as_secs_f64() * 1_000.0,
            "lifted_proof_bytes": lifted_proof_bytes,
            "node_proof_bytes": node_proof_bytes,
            "lifted_verification_ms": lifted_verification_elapsed.as_secs_f64() * 1_000.0,
            "node_verification_ms": node_verification_elapsed.as_secs_f64() * 1_000.0,
            "lifted_serialization_ms": lifted_serialization_elapsed.as_secs_f64() * 1_000.0,
            "node_serialization_ms": node_serialization_elapsed.as_secs_f64() * 1_000.0,
            "lifted_proof_shape": proof_shape(&lifted_verification.raw_proof),
            "node_proof_shape": proof_shape(&node_verification.raw_proof),
            "public_claim_mutations": "lifted application digest and binary application root rejected",
            "application_root": node.info.application_root
                .iter()
                .map(|value| value.as_canonical_u32())
                .collect::<Vec<_>>(),
            "peak_rss_bytes": system_info::peak_rss_bytes(),
            "native_verification": "passed",
        }))?
    );
    Ok(())
}

fn bytecode_report(bytecode: &lean_vm::Bytecode, compile_seconds: f64) -> serde_json::Value {
    json!({
        "compile_ms": compile_seconds * 1_000.0,
        "instruction_count": bytecode.unpadded_size(),
        "padded_instruction_count": bytecode.size(),
        "bytecode_bytes": bytecode.instructions_multilinear().len() * 4,
        "log_size": bytecode.log_size(),
        "hash": bytecode.hash()
            .iter()
            .map(|value| value.as_canonical_u32())
            .collect::<Vec<_>>(),
    })
}

fn check_public_claim_rejections(
    child_bytecode: &lean_vm::Bytecode,
    lifted_bytecode: &lean_vm::Bytecode,
    node_bytecode: &lean_vm::Bytecode,
    lifted: &rec_aggregation::LiftedExecutionProof,
    node: &rec_aggregation::BinaryNodeProof,
) -> Result<(), Box<dyn Error>> {
    let mut changed_lifted = lifted.clone();
    changed_lifted.info.application_digest[0] += lean_vm::F::from_u32(1);
    if verify_lifted_execution_proof(child_bytecode, lifted_bytecode, &changed_lifted).is_ok() {
        return Err("changed lifted application digest was accepted".into());
    }

    let mut changed_node = node.clone();
    changed_node.info.application_root[0] += lean_vm::F::from_u32(1);
    if verify_binary_node(child_bytecode, lifted_bytecode, node_bytecode, &changed_node).is_ok() {
        return Err("changed binary application root was accepted".into());
    }
    Ok(())
}

fn proof_shape(raw: &backend::RawProof<lean_vm::F>) -> serde_json::Value {
    let dims = raw.transcript[..2 + lean_vm::N_TABLES]
        .iter()
        .map(|value| value.as_canonical_u32() as usize)
        .collect::<Vec<_>>();
    json!({
        "log_inv_rate": dims[0],
        "log_memory": dims[1],
        "table_log_heights": lean_vm::ALL_TABLES
            .iter()
            .enumerate()
            .map(|(index, table)| (table.name(), dims[index + 2]))
            .collect::<std::collections::BTreeMap<_, _>>(),
    })
}
