use std::error::Error;

use backend::PrimeField32;
use serde_json::json;
use spartan_whir_guest::{
    compile_poseidon1_primitives_guest, execute_poseidon1_primitives_guest, poseidon1_primitive_words,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let compile = compile_poseidon1_primitives_guest();
    let bytecode = &compile.bytecode;
    let execution = execute_poseidon1_primitives_guest(bytecode, &poseidon1_primitive_words())?;
    let output = json!({
        "profile": "spartan-whir-poseidon1-primitives-v1",
        "input_words": spartan_whir_guest::POSEIDON1_PRIMITIVE_WORDS,
        "compile_ms": compile.elapsed.as_secs_f64() * 1_000.0,
        "compiled_instruction_count": bytecode.unpadded_size(),
        "padded_instruction_count": bytecode.size(),
        "bytecode_bytes": bytecode.instructions_multilinear().len() * 4,
        "bytecode_log_size": bytecode.log_size(),
        "bytecode_hash": bytecode.hash().iter().map(|value| value.as_canonical_u32()).collect::<Vec<_>>(),
        "compiler_peak_rss_bytes": system_info::peak_rss_bytes(),
        "execution": {
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
        },
    });
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}
