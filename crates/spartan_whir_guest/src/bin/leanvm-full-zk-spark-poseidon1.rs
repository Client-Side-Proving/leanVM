use std::error::Error;

use backend::PrimeField32;
use serde_json::json;
use spartan_whir_guest::{
    FULL_ZK_SPARK_POSEIDON1_INPUT_BYTES, FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE, SparkGuestFixture,
    SparkGuestOptimizations,
};

fn main() {
    let result = std::thread::Builder::new()
        .name("leanvm-full-zk-spark".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| run().map_err(|error| error.to_string()))
        .expect("spawn guest compiler thread")
        .join()
        .expect("guest compiler thread panicked");
    if let Err(error) = result {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "execute".to_string());
    if !matches!(mode.as_str(), "compile" | "execute" | "prove" | "profile" | "validate") {
        return Err(format!("expected mode compile, execute, prove, profile, or validate; got {mode}").into());
    }

    let selection = std::env::args().nth(2).unwrap_or_default();
    let mut options = SparkGuestOptimizations::default();
    let mut fixed_siblings = false;
    for name in selection.split(',').filter(|name| !name.is_empty()) {
        match name {
            "recommended" => options = SparkGuestOptimizations::recommended(),
            "control" => {
                options = SparkGuestOptimizations::recommended();
                options.query_permutation = false;
                options.unroll_powers = false;
                options.block_query_powers = false;
            }
            "fresh_relation" => options.fresh_relation = true,
            "fresh_rows" => options.fresh_rows = true,
            "structured_rows" => options.structured_rows = true,
            "row_counts" => options.row_counts = true,
            "derived_fields" => options.derived_fields = true,
            "query_product" => options.query_product = true,
            "radix_prefix" => options.radix_prefix = true,
            "query_permutation" => options.query_permutation = true,
            "unroll_powers" => options.unroll_powers = true,
            "block_query_powers" => options.block_query_powers = true,
            "horner_cubic" => options.horner_cubic = true,
            "eq_precompile" => options.eq_precompile = true,
            "factor_eq_endpoints" => options.factor_eq_endpoints = true,
            "merkle_query_bits" => options.merkle_query_bits = true,
            "paired_merkle" => options.paired_merkle = true,
            "extension_arithmetic" => options.extension_arithmetic = true,
            "transcript_blocks" => options.transcript_blocks = true,
            "fixed_siblings" => fixed_siblings = true,
            _ => return Err(format!("unknown optimization: {name}").into()),
        }
    }
    let fixture_directory = std::env::args().nth(3);
    let external_fixture = fixture_directory
        .as_ref()
        .map(|directory| SparkGuestFixture::from_directory(std::path::Path::new(directory)))
        .transpose()?;
    let mut fixture = match external_fixture {
        Some(fixture) => fixture,
        None => SparkGuestFixture::embedded()?.clone(),
    };
    if fixed_siblings {
        fixture = fixture.with_fixed_sibling_storage()?;
    }
    let compile = fixture.compile(&options)?;
    let bytecode = &compile.bytecode;
    let mut output = json!({
        "profile": "spartan-whir-poseidon1-quintic-full-zk-spark-leanvm-v1",
        "input_bytes": FULL_ZK_SPARK_POSEIDON1_INPUT_BYTES,
        "optimizations": selection,
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

    let words = fixture.compact_words(&options)?;
    output["input_bytes"] = json!(words.len() * 4);
    output["canonical_proof_words"] = json!(fixture.canonical_words());
    let execution = fixture.execute_report(bytecode, &words, &options, mode == "profile")?;
    output["execution"] = json!({
        "cycles": execution.metadata.cycles,
        "profiling_report": execution.metadata.profiling_report,
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

    if mode == "validate" {
        let mutation_text = match &fixture_directory {
            Some(directory) => {
                std::fs::read_to_string(std::path::Path::new(directory).join("full_zk_spark_mutations.json"))?
            }
            None => include_str!("../../testdata/full_zk_spark_poseidon1/full_zk_spark_mutations.json").to_string(),
        };
        let mutations: serde_json::Value = serde_json::from_str(&mutation_text)?;
        let mut rejected = Vec::new();
        for case in mutations["cases"].as_array().ok_or("missing mutation cases")? {
            let mut changed = words.clone();
            let mut applied = 0;
            for patch in case["patches"].as_array().ok_or("missing patches")? {
                let original_offset =
                    fixture.normalized_offset(patch["offset"].as_u64().ok_or("invalid offset")? as usize)?;
                let offset = if options.uses_compact_input() {
                    match fixture.compact_offset(original_offset, &options)? {
                        Some(offset) => offset,
                        None => continue,
                    }
                } else {
                    original_offset
                };
                applied += 1;
                let before = patch["before"].as_u64().ok_or("invalid before")? as u32;
                let after = patch["after"].as_u64().ok_or("invalid after")? as u32;
                if original_offset == 8 && fixed_siblings {
                    changed[offset] = u32::try_from(i64::from(changed[offset]) + i64::from(after) - i64::from(before))?;
                } else {
                    if changed[offset] != before {
                        return Err(format!("mutation precondition failed: {}", case["name"]).into());
                    }
                    changed[offset] = after;
                }
            }
            if applied == 0 {
                rejected.push(json!({"name": case["name"], "status": "field omitted from encoding"}));
                continue;
            }
            let error = fixture
                .validate_words(bytecode, &changed, &options)
                .err()
                .ok_or_else(|| format!("mutation accepted: {}", case["name"]))?;
            rejected.push(json!({"name": case["name"], "error": error.to_string()}));
        }
        output["rejected_mutations"] = json!(rejected);
    }

    if mode == "prove" {
        let root = fixture.prove(bytecode, &words, &options)?;
        output["root_proof"] = json!({
            "log_inv_rate": FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE,
            "proving_ms": root.proving_elapsed.as_secs_f64() * 1_000.0,
            "verification_ms": root.verification_elapsed.as_secs_f64() * 1_000.0,
            "serialized_proof_bytes": root.serialized_proof_bytes,
            "peak_rss_bytes": system_info::peak_rss_bytes(),
        });
    }

    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}
