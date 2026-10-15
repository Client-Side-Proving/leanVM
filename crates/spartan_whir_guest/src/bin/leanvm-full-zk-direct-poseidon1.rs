use std::error::Error;

use backend::PrimeField32;
use serde_json::json;
use spartan_whir_guest::{
    FULL_ZK_DIRECT_POSEIDON1_INPUT_BYTES, FULL_ZK_DIRECT_POSEIDON1_ROOT_LOG_INV_RATE,
    compile_full_zk_direct_poseidon1_guest, execute_full_zk_direct_poseidon1_guest_report,
    full_zk_direct_poseidon1_public_input, full_zk_direct_poseidon1_words, prove_full_zk_direct_poseidon1_guest,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "execute".to_string());
    if !matches!(mode.as_str(), "compile" | "execute" | "prove") {
        return Err(format!("expected mode compile, execute, or prove; got {mode}").into());
    }

    let compile = compile_full_zk_direct_poseidon1_guest()?;
    let bytecode = &compile.bytecode;
    let mut output = json!({
        "profile": "spartan-whir-poseidon1-quintic-full-zk-direct-leanvm-v1",
        "input_bytes": FULL_ZK_DIRECT_POSEIDON1_INPUT_BYTES,
        "compile_ms": compile.elapsed.as_secs_f64() * 1_000.0,
        "compiled_instruction_count": bytecode.unpadded_size(),
        "padded_instruction_count": bytecode.size(),
        "bytecode_bytes": bytecode.instructions_multilinear().len() * 4,
        "bytecode_log_size": bytecode.log_size(),
        "bytecode_hash": bytecode.hash().iter().map(|value| value.as_canonical_u32()).collect::<Vec<_>>(),
        "compiler_limit_reached": false,
        "compiler_peak_rss_bytes": system_info::peak_rss_bytes(),
        "effective_threads": system_info::num_threads(),
    });

    if mode == "compile" {
        println!("{}", serde_json::to_string_pretty(&output)?);
        return Ok(());
    }

    let public_input = full_zk_direct_poseidon1_public_input()?;
    let words = full_zk_direct_poseidon1_words()?;
    let execution = execute_full_zk_direct_poseidon1_guest_report(bytecode, &public_input, &words)?;
    output["execution"] = json!({
        "cycles": execution.metadata.cycles,
        "memory_cells": execution.metadata.memory,
        "padded_memory_cells": execution.padded_memory_cells,
        "runtime_memory_cells": execution.metadata.runtime_memory,
        "memory_usage_percent": execution.metadata.memory_usage_percent,
        "poseidon1_precompile_calls": execution.metadata.n_poseidons,
        "extension_operation_calls": execution.metadata.n_extension_ops,
        "tables": execution.tables.iter().map(|table| json!({
            "name": table.name,
            "non_padded_rows": table.non_padded_rows,
            "log_n_rows": table.log_n_rows,
            "padded_rows": table.padded_rows,
        })).collect::<Vec<_>>(),
        "peak_rss_bytes": system_info::peak_rss_bytes(),
    });

    if mode == "prove" {
        let root = prove_full_zk_direct_poseidon1_guest(bytecode, &public_input, &words)?;
        output["root_proof"] = json!({
            "log_inv_rate": FULL_ZK_DIRECT_POSEIDON1_ROOT_LOG_INV_RATE,
            "proving_ms": root.proving_elapsed.as_secs_f64() * 1_000.0,
            "verification_ms": root.verification_elapsed.as_secs_f64() * 1_000.0,
            "serialized_proof_bytes": root.serialized_proof_bytes,
            "peak_rss_bytes": system_info::peak_rss_bytes(),
        });
    }

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}
