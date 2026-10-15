//! Diagnostic complete-chain measurements for two distinct application proofs.
use std::{
    collections::BTreeMap,
    error::Error,
    fs,
    path::{Path, PathBuf},
    sync::Mutex,
    time::{Duration, Instant},
};

use backend::{
    Air, BasedVectorSpace, Evaluation, PrimeCharacteristicRing, PrimeField32, ProofHashProfile, RawProof, RoundConfig,
    WhirConfig,
};
use lean_prover::{
    TWO_COMMITMENT_WHIR_MODE_TAG, TWO_COMMITMENT_WHIR_STATEMENT_TAG, WhirExecutionProfile,
    prove_execution::{ExecutionProof, prove_execution_with_profile},
    two_commitment_fiat_shamir_domain_sep, two_commitment_fiat_shamir_static_descriptor,
    two_commitment_statement_observation,
    verify_execution::verify_execution_with_profile,
};
use lean_vm::{Bytecode, EF, F, TableT};
use rec_aggregation::{
    RecursiveChildShape, RecursiveVerifierOptions, TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
    TerminalC1VerifierPreprocessing, compile_binary_node_bytecode_for_dimension_with_options,
    compile_binary_node_bytecode_for_fixed_shape_with_options,
    compile_lifted_execution_bytecode_for_dimension_with_options,
    compile_lifted_execution_bytecode_for_fixed_shape_with_options,
    compile_terminal_binary_node_bytecode_for_dimension_with_options,
    compile_terminal_binary_node_bytecode_for_fixed_shape_with_options, lift_execution_proof_with_profiles,
    prove_binary_node_with_profiles_and_hash, prove_terminal_binary_node_c1_v1_with_preprocessing,
    prove_terminal_binary_node_with_profiles_and_hash, terminal_c1_execution_program_prefix,
    terminal_c1_fixed_programs, terminal_c1_fixed_programs_for_dimension,
    terminal_c1_statement_public_memory_bindings_for_dimension, verify_binary_node_with_profiles_and_hash,
    verify_lifted_execution_proof_with_profiles, verify_terminal_binary_node_c1_v1_with_preprocessing,
    verify_terminal_binary_node_with_profiles_and_hash,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use spartan_whir_guest::{SparkGuestFixture, SparkGuestOptimizations};

static PROVING_PHASE: Mutex<Option<(&'static str, Instant)>> = Mutex::new(None);

#[derive(Clone, Serialize, Deserialize)]
struct Profiles {
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
    fixed_child_shape: bool,
    #[serde(default)]
    guest_extension_arithmetic: bool,
    #[serde(default)]
    guest_transcript_blocks: bool,
    #[serde(default)]
    terminal_keccak: bool,
    #[serde(default)]
    terminal_public_memory: bool,
    #[serde(default)]
    terminal_two_commitment: bool,
    #[serde(default)]
    terminal_grouped_logup: bool,
    #[serde(default)]
    terminal_num_variables: Option<usize>,
}

struct TerminalC1Export {
    preprocessing: TerminalC1VerifierPreprocessing,
    fixed_polynomial_ms: f64,
    fixed_commitment_ms: f64,
}

#[derive(Serialize, Deserialize)]
struct CachedDirectProof {
    proof: Vec<u8>,
    proving_ms: f64,
    execution_rows: usize,
    extension_rows: usize,
    poseidon_calls: usize,
    memory_cells: usize,
    profiling_report: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct CachedLiftProof {
    execution: CachedDirectProof,
    application_digest: Vec<u32>,
    claim_point: Vec<Vec<u32>>,
    claim_value: Vec<u32>,
}

fn direct_cache_path(
    bytecode: &Bytecode,
    input: &[F; 8],
    profile: &WhirExecutionProfile,
    profiling: bool,
) -> Option<PathBuf> {
    let directory = std::env::var_os("LEANVM_DIRECT_PROOF_CACHE")?;
    let mut identity = profile.fiat_shamir_domain_sep(bytecode).to_vec();
    identity.extend_from_slice(input);
    identity.extend_from_slice(bytecode.hash());
    identity.push(F::from_bool(profiling));
    identity.resize(identity.len().next_multiple_of(8), F::ZERO);
    let name = backend::poseidon_hash_slice(&identity)
        .iter()
        .map(|value| format!("{:08x}", value.as_canonical_u32()))
        .collect::<String>();
    Some(PathBuf::from(directory).join(format!("{name}.json")))
}

fn read_direct_cache(path: &Path) -> Result<Option<(ExecutionProof, f64)>, Box<dyn Error>> {
    if !path.exists() {
        return Ok(None);
    }
    let cached: CachedDirectProof = serde_json::from_slice(&fs::read(path)?)?;
    Ok(Some(execution_from_cache(cached)?))
}

fn execution_from_cache(cached: CachedDirectProof) -> Result<(ExecutionProof, f64), Box<dyn Error>> {
    let proof = ExecutionProof {
        proof: postcard::from_bytes(&cached.proof)?,
        metadata: Some(lean_vm::ExecutionMetadata {
            cycles: cached.execution_rows,
            memory: cached.memory_cells,
            n_poseidons: cached.poseidon_calls,
            n_extension_ops: cached.extension_rows,
            profiling_report: cached.profiling_report,
            ..Default::default()
        }),
    };
    Ok((proof, cached.proving_ms))
}

fn execution_cache_record(proof: &ExecutionProof, proving_ms: f64) -> Result<CachedDirectProof, Box<dyn Error>> {
    let metadata = proof.metadata.as_ref().ok_or("missing execution metadata")?;
    Ok(CachedDirectProof {
        proof: postcard::to_allocvec(&proof.proof)?,
        proving_ms,
        execution_rows: metadata.cycles,
        extension_rows: metadata.n_extension_ops,
        poseidon_calls: metadata.n_poseidons,
        memory_cells: metadata.memory,
        profiling_report: metadata.profiling_report.clone(),
    })
}

fn write_direct_cache(path: &Path, proof: &ExecutionProof, proving_ms: f64) -> Result<(), Box<dyn Error>> {
    let cached = execution_cache_record(proof, proving_ms)?;
    fs::create_dir_all(path.parent().ok_or("cache path has no parent")?)?;
    fs::write(path, serde_json::to_vec(&cached)?)?;
    Ok(())
}

fn read_lift_cache(path: &Path) -> Result<Option<(rec_aggregation::LiftedExecutionProof, f64)>, Box<dyn Error>> {
    if !path.exists() {
        return Ok(None);
    }
    let cached: CachedLiftProof = serde_json::from_slice(&fs::read(path)?)?;
    let extension = |words: &[u32]| -> Result<EF, Box<dyn Error>> {
        if words.len() != 5 || words.iter().any(|&word| word >= 2_130_706_433) {
            return Err("invalid cached extension field value".into());
        }
        EF::from_basis_coefficients_slice(&words.iter().copied().map(F::from_u32).collect::<Vec<_>>())
            .ok_or_else(|| "invalid cached extension field value".into())
    };
    if cached.application_digest.len() != 8 || cached.application_digest.iter().any(|&word| word >= 2_130_706_433) {
        return Err("invalid cached application digest".into());
    }
    let point = cached
        .claim_point
        .iter()
        .map(|words| extension(words))
        .collect::<Result<Vec<_>, _>>()?;
    let info = rec_aggregation::LiftedExecutionInfo {
        application_digest: cached
            .application_digest
            .iter()
            .copied()
            .map(F::from_u32)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap(),
        child_bytecode_claim: Evaluation::new(backend::MultilinearPoint(point), extension(&cached.claim_value)?),
    };
    let (proof, milliseconds) = execution_from_cache(cached.execution)?;
    Ok(Some((
        rec_aggregation::LiftedExecutionProof { info, proof },
        milliseconds,
    )))
}

fn write_lift_cache(
    path: &Path,
    proof: &rec_aggregation::LiftedExecutionProof,
    proving_ms: f64,
) -> Result<(), Box<dyn Error>> {
    let cached = CachedLiftProof {
        execution: execution_cache_record(&proof.proof, proving_ms)?,
        application_digest: base_words(&proof.info.application_digest),
        claim_point: proof
            .info
            .child_bytecode_claim
            .point
            .0
            .iter()
            .map(|value| base_words(value.as_basis_coefficients_slice()))
            .collect(),
        claim_value: base_words(proof.info.child_bytecode_claim.value.as_basis_coefficients_slice()),
    };
    fs::create_dir_all(path.parent().ok_or("cache path has no parent")?)?;
    fs::write(path, serde_json::to_vec(&cached)?)?;
    Ok(())
}

impl Default for Profiles {
    fn default() -> Self {
        Self {
            direct: WhirExecutionProfile::security_100(1),
            lift: WhirExecutionProfile::security_100(4),
            node: WhirExecutionProfile::security_100(1),
            verifier_options: RecursiveVerifierOptions::default(),
            node_child_num_variables: None,
            lift_child_num_variables: None,
            fixed_child_shape: false,
            guest_extension_arithmetic: false,
            guest_transcript_blocks: false,
            terminal_keccak: false,
            terminal_public_memory: false,
            terminal_two_commitment: false,
            terminal_grouped_logup: false,
            terminal_num_variables: None,
        }
    }
}

fn main() {
    let timeout_seconds = std::env::var("LEANVM_PROVING_TIMEOUT_SECONDS")
        .map(|value| {
            value
                .parse::<u64>()
                .expect("LEANVM_PROVING_TIMEOUT_SECONDS must be an unsigned integer")
        })
        .unwrap_or(60);
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(Duration::from_millis(250));
            if let Some((label, started)) = *PROVING_PHASE.lock().unwrap()
                && timeout_seconds != 0
                && started.elapsed() > Duration::from_secs(timeout_seconds)
            {
                eprintln!("proving limit exceeded: {label} took more than {timeout_seconds} seconds");
                std::process::exit(124);
            }
        }
    });
    let result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run(timeout_seconds).map_err(|error| error.to_string()))
        .unwrap()
        .join()
        .unwrap();
    if let Err(error) = result {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn timed_proof<T>(
    label: &'static str,
    operation: impl FnOnce() -> Result<T, Box<dyn Error>>,
) -> Result<(T, f64), Box<dyn Error>> {
    eprintln!("starting {label}");
    let started = Instant::now();
    *PROVING_PHASE.lock().unwrap() = Some((label, started));
    let result = operation();
    *PROVING_PHASE.lock().unwrap() = None;
    let value = result?;
    let milliseconds = started.elapsed().as_secs_f64() * 1000.0;
    eprintln!("finished {label}: {milliseconds:.3} ms");
    Ok((value, milliseconds))
}

fn run(timeout_seconds: u64) -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let left_path = args
        .next()
        .map(PathBuf::from)
        .ok_or("expected left fixture directory")?;
    let right_path = args
        .next()
        .map(PathBuf::from)
        .ok_or("expected right fixture directory")?;
    let output = args.next().map(PathBuf::from).ok_or("expected output JSON path")?;
    let mut profiles: Profiles = args
        .next()
        .map(|path| -> Result<_, Box<dyn Error>> { Ok(serde_json::from_slice(&fs::read(path)?)?) })
        .transpose()?
        .unwrap_or_default();
    if args.next().is_some() {
        return Err("usage: leanvm-recursion-profile LEFT_FIXTURE RIGHT_FIXTURE OUTPUT_JSON [PROFILES_JSON]".into());
    }
    for profile in [&profiles.direct, &profiles.lift, &profiles.node] {
        profile.validate()?;
        if profile.security_bits < 100 {
            return Err("this experiment requires a backend target of at least 100 bits for every LeanVM layer".into());
        }
    }
    let profiling = std::env::var_os("LEANVM_VM_PROFILE").is_some();
    let terminal_hash = if profiles.terminal_keccak {
        ProofHashProfile::Keccak240
    } else {
        ProofHashProfile::Poseidon1
    };
    if profiles.terminal_public_memory && !profiles.terminal_keccak {
        return Err("the terminal public-memory profile requires Keccak".into());
    }
    if profiles.terminal_two_commitment && (!profiles.terminal_public_memory || !profiles.terminal_keccak) {
        return Err("the terminal two-commitment profile requires terminal public memory and Keccak".into());
    }
    if profiles.terminal_num_variables.is_some() && !profiles.terminal_two_commitment {
        return Err("terminal_num_variables requires the two-commitment terminal".into());
    }
    if profiles.terminal_grouped_logup && !profiles.terminal_two_commitment {
        return Err("grouped LogUp requires the terminal fixed-program layout".into());
    }
    let prove_fixed_node = if profiles.terminal_grouped_logup {
        rec_aggregation::prove_terminal_binary_node_grouped_logup_with_preprocessing
    } else {
        prove_terminal_binary_node_c1_v1_with_preprocessing
    };
    let verify_fixed_node = if profiles.terminal_grouped_logup {
        rec_aggregation::verify_terminal_binary_node_grouped_logup_with_preprocessing
    } else {
        verify_terminal_binary_node_c1_v1_with_preprocessing
    };
    let prove_node = if profiles.terminal_public_memory {
        prove_terminal_binary_node_with_profiles_and_hash
    } else {
        prove_binary_node_with_profiles_and_hash
    };
    let verify_node = if profiles.terminal_public_memory {
        verify_terminal_binary_node_with_profiles_and_hash
    } else {
        verify_binary_node_with_profiles_and_hash
    };
    let mut options = SparkGuestOptimizations::recommended();
    options.extension_arithmetic = profiles.guest_extension_arithmetic;
    options.transcript_blocks = profiles.guest_transcript_blocks;
    let fixtures = [
        SparkGuestFixture::from_directory(&left_path)?.with_fixed_sibling_storage()?,
        SparkGuestFixture::from_directory(&right_path)?.with_fixed_sibling_storage()?,
    ];
    let preparation = Instant::now();
    let child = fixtures[0].compile(&options)?.bytecode;
    let right_code = fixtures[1].compile(&options)?.bytecode;
    if child.hash() != right_code.hash() {
        return Err("the two fixtures compile to different verifier programs".into());
    }
    drop(right_code);
    let inputs = [fixtures[0].public_input()?, fixtures[1].public_input()?];
    if inputs[0] == inputs[1] {
        return Err("use two distinct application statements for the binary experiment".into());
    }
    let words = [
        fixtures[0].compact_words(&options)?,
        fixtures[1].compact_words(&options)?,
    ];
    let mutations = if std::env::var_os("LEANVM_VALIDATE_MUTATIONS").is_some() {
        validate_mutations(&fixtures[0], &left_path, &child, &words[0], &options)?
    } else {
        json!("not requested for this diagnostic run")
    };
    let witnesses = [
        fixtures[0].execution_witness(&child, &words[0], &options)?,
        fixtures[1].execution_witness(&child, &words[1], &options)?,
    ];
    let preparation_ms = preparation.elapsed().as_secs_f64() * 1000.0;
    let mut report = json!({
        "schema": "leanvm-withdrawal-recursion-experiment-v1",
        "measurement": "diagnostic wall time; compilation and input preparation reported separately",
        "profiles": profiles,
        "node_arity": 2,
        "distinct_child_statements": true,
        "vm_profiling": profiling,
        "effective_threads": system_info::num_threads(),
        "per_proving_operation_limit_seconds": timeout_seconds,
        "preparation_ms": preparation_ms,
        "applications": [application(&left_path)?, application(&right_path)?],
        "fixed_sibling_storage": true,
        "canonical_words_per_application": fixtures[0].canonical_words(),
        "compact_input_words_per_application": words[0].len(),
        "guest_mutations": mutations,
        "layers": [],
    });
    save(&output, &report)?;
    let mut direct = Vec::new();
    let mut direct_shapes = Vec::new();
    for i in 0..2 {
        let label = if i == 0 { "direct_left" } else { "direct_right" };
        let cache_path = direct_cache_path(&child, &inputs[i], &profiles.direct, profiling);
        let cached = cache_path.as_deref().map(read_direct_cache).transpose()?.flatten();
        let reused_proof = cached.is_some();
        let (proof, proving_ms) = if let Some(cached) = cached {
            eprintln!("reusing {label}; native verification is repeated, timing comes from cache");
            cached
        } else {
            timed_proof(label, || {
                Ok(
                    prove_execution_with_profile(&child, &inputs[i], &witnesses[i], &profiles.direct, profiling)
                        .map_err(|error| std::io::Error::other(error.to_string()))?,
                )
            })?
        };
        let started = Instant::now();
        let (_, raw) = verify_execution_with_profile(&child, &inputs[i], proof.proof.clone(), &profiles.direct)?;
        let verification_ms = started.elapsed().as_secs_f64() * 1000.0;
        direct_shapes.push(recursive_child_shape(&raw)?);
        if !reused_proof && let Some(path) = cache_path.as_deref() {
            write_direct_cache(path, &proof, proving_ms)?;
        }
        let mut entry = layer(label, &child, &proof, &raw, proving_ms, verification_ms)?;
        entry["reused_proof"] = json!(reused_proof);
        entry["proving_time_source"] = json!(if reused_proof {
            "original cached diagnostic"
        } else {
            "current diagnostic"
        });
        report["layers"].as_array_mut().unwrap().push(entry);
        save(&output, &report)?;
        direct.push(proof);
    }
    let direct_dimensions = report["layers"]
        .as_array()
        .unwrap()
        .iter()
        .map(|entry| entry["stacked_num_variables"].as_u64().unwrap() as usize)
        .collect::<Vec<_>>();
    if direct_dimensions.len() != 2 || direct_dimensions[0] != direct_dimensions[1] {
        return Err("direct children must have the same stacked dimension".into());
    }
    if direct_shapes.len() != 2 || direct_shapes[0] != direct_shapes[1] {
        return Err("direct children must have the same execution-proof dimensions".into());
    }
    if profiles
        .lift_child_num_variables
        .is_some_and(|dimension| dimension != direct_dimensions[0])
    {
        return Err("requested lift child dimension differs from actual direct proofs".into());
    }
    profiles.lift_child_num_variables = Some(direct_dimensions[0]);
    let lift_compilation_started = Instant::now();
    let lifted_code = if profiles.fixed_child_shape {
        compile_lifted_execution_bytecode_for_fixed_shape_with_options(
            &child,
            &profiles.direct,
            &profiles.verifier_options,
            &direct_shapes[0],
        )
    } else {
        compile_lifted_execution_bytecode_for_dimension_with_options(
            &child,
            &profiles.direct,
            &profiles.verifier_options,
            direct_dimensions[0],
        )
    };
    report["lift_compilation_ms"] = json!(lift_compilation_started.elapsed().as_secs_f64() * 1000.0);
    report["profiles"] = json!(profiles);
    drop(witnesses);
    drop(words);
    let mut lifts = Vec::new();
    let mut lift_shapes = Vec::new();
    for i in 0..2 {
        let label = if i == 0 { "lift_left" } else { "lift_right" };
        let cache_path = direct_cache_path(&lifted_code, &inputs[i], &profiles.lift, profiling)
            .map(|path| path.with_extension("lift.json"));
        let cached = cache_path.as_deref().map(read_lift_cache).transpose()?.flatten();
        let reused_proof = cached.is_some();
        let (proof, proving_ms) = if let Some(cached) = cached {
            eprintln!("reusing {label}; native verification is repeated, timing comes from cache");
            cached
        } else {
            timed_proof(label, || {
                Ok(lift_execution_proof_with_profiles(
                    &child,
                    &lifted_code,
                    &inputs[i],
                    &direct[i],
                    &profiles.direct,
                    &profiles.lift,
                    profiling,
                )?)
            })?
        };
        if proof.info.application_digest != inputs[i] {
            return Err("cached lift belongs to a different application statement".into());
        }
        let started = Instant::now();
        let verified = verify_lifted_execution_proof_with_profiles(
            &child,
            &lifted_code,
            &proof,
            &profiles.direct,
            &profiles.lift,
        )?;
        let verification_ms = started.elapsed().as_secs_f64() * 1000.0;
        lift_shapes.push(recursive_child_shape(&verified.raw_proof)?);
        if !reused_proof && let Some(path) = cache_path.as_deref() {
            write_lift_cache(path, &proof, proving_ms)?;
        }
        let mut entry = layer(
            label,
            &lifted_code,
            &proof.proof,
            &verified.raw_proof,
            proving_ms,
            verification_ms,
        )?;
        entry["reused_proof"] = json!(reused_proof);
        entry["proving_time_source"] = json!(if reused_proof {
            "original cached diagnostic"
        } else {
            "current diagnostic"
        });
        report["layers"].as_array_mut().unwrap().push(entry);
        save(&output, &report)?;
        lifts.push(proof);
    }
    let lift_dimensions = report["layers"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["layer"].as_str().is_some_and(|name| name.starts_with("lift_")))
        .map(|entry| entry["stacked_num_variables"].as_u64().unwrap() as usize)
        .collect::<Vec<_>>();
    if lift_dimensions.len() != 2 || lift_dimensions[0] != lift_dimensions[1] {
        return Err("lifted children must have the same stacked dimension".into());
    }
    if lift_shapes.len() != 2 || lift_shapes[0] != lift_shapes[1] {
        return Err("lifted children must have the same execution-proof dimensions".into());
    }
    if profiles
        .node_child_num_variables
        .is_some_and(|dimension| dimension != lift_dimensions[0])
    {
        return Err("requested node child dimension differs from actual lifted proofs".into());
    }
    profiles.node_child_num_variables = Some(lift_dimensions[0]);
    let node_compilation_started = Instant::now();
    let node_code = if profiles.fixed_child_shape && profiles.terminal_public_memory {
        compile_terminal_binary_node_bytecode_for_fixed_shape_with_options(
            &child,
            &lifted_code,
            &profiles.lift,
            &profiles.verifier_options,
            &lift_shapes[0],
        )
    } else if profiles.fixed_child_shape {
        compile_binary_node_bytecode_for_fixed_shape_with_options(
            &child,
            &lifted_code,
            &profiles.lift,
            &profiles.verifier_options,
            &lift_shapes[0],
        )
    } else if profiles.terminal_public_memory {
        compile_terminal_binary_node_bytecode_for_dimension_with_options(
            &child,
            &lifted_code,
            &profiles.lift,
            &profiles.verifier_options,
            lift_dimensions[0],
        )
    } else {
        compile_binary_node_bytecode_for_dimension_with_options(
            &child,
            &lifted_code,
            &profiles.lift,
            &profiles.verifier_options,
            lift_dimensions[0],
        )
    };
    report["node_compilation_ms"] = json!(node_compilation_started.elapsed().as_secs_f64() * 1000.0);
    report["profiles"] = json!(profiles);
    drop(direct);
    let terminal_c1_preprocessing = if profiles.terminal_two_commitment {
        let fixed_polynomial_started = Instant::now();
        let fixed_programs = if let Some(num_variables) = profiles.terminal_num_variables {
            terminal_c1_fixed_programs_for_dimension(&child, &lifted_code, &node_code, &profiles.node, num_variables)?
        } else {
            terminal_c1_fixed_programs(&child, &lifted_code, &node_code, &profiles.node)?
        };
        let fixed_polynomial_ms = fixed_polynomial_started.elapsed().as_secs_f64() * 1000.0;
        let fixed_commitment_started = Instant::now();
        let secondary_commitment = fixed_programs.preprocess_keccak240();
        let fixed_commitment_ms = fixed_commitment_started.elapsed().as_secs_f64() * 1000.0;
        let verifier_preprocessing = fixed_programs.verifier_preprocessing_with_root(secondary_commitment.root);
        report["terminal_c1_preprocessing"] = json!({
            "fixed_polynomial_ms": fixed_polynomial_ms,
            "fixed_commitment_ms": fixed_commitment_ms,
            "total_ms": fixed_polynomial_ms + fixed_commitment_ms,
            "timing_boundary": "application preprocessing outside online proving and native verification",
        });
        save(&output, &report)?;
        Some((
            fixed_programs,
            secondary_commitment,
            TerminalC1Export {
                preprocessing: verifier_preprocessing,
                fixed_polynomial_ms,
                fixed_commitment_ms,
            },
        ))
    } else {
        None
    };
    let (node, proving_ms, terminal_c1_export) =
        if let Some((fixed_programs, secondary_commitment, export)) = terminal_c1_preprocessing {
            let (node, proving_ms) = timed_proof(
                if profiles.terminal_grouped_logup {
                    "binary_root_grouped_logup"
                } else {
                    "binary_root_c1"
                },
                || {
                    Ok(prove_fixed_node(
                        &child,
                        &lifted_code,
                        &node_code,
                        [&lifts[0], &lifts[1]],
                        &profiles.direct,
                        &profiles.lift,
                        &profiles.node,
                        fixed_programs,
                        secondary_commitment,
                        profiling,
                    )?)
                },
            )?;
            (node, proving_ms, Some(export))
        } else {
            let (node, proving_ms) = timed_proof("binary_root", || {
                Ok(prove_node(
                    &child,
                    &lifted_code,
                    &node_code,
                    [&lifts[0], &lifts[1]],
                    &profiles.direct,
                    &profiles.lift,
                    &profiles.node,
                    terminal_hash,
                    profiling,
                )?)
            })?;
            (node, proving_ms, None)
        };
    let started = Instant::now();
    let verified = if let Some(export) = &terminal_c1_export {
        verify_fixed_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &profiles.node,
            &export.preprocessing,
        )?
    } else {
        verify_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &profiles.node,
            terminal_hash,
        )?
    };
    let verification_ms = started.elapsed().as_secs_f64() * 1000.0;
    report["layers"].as_array_mut().unwrap().push(layer(
        if profiles.terminal_grouped_logup {
            "binary_root_grouped_logup"
        } else if terminal_c1_export.is_some() {
            "binary_root_c1"
        } else {
            "binary_root"
        },
        &node_code,
        &node.proof,
        &verified.raw_proof,
        proving_ms,
        verification_ms,
    )?);
    if let Some(directory) = std::env::var_os("LEANVM_TERMINAL_EXPORT") {
        export_terminal(
            Path::new(&directory),
            [&child, &lifted_code, &node_code],
            &profiles,
            &node,
            &verified,
            report["layers"].as_array().unwrap().last().unwrap(),
            terminal_c1_export.as_ref(),
        )?;
        report["terminal_export"] = json!(
            "native proof, raw transcript, Merkle openings, fixed bytecode polynomials, and authenticated claims exported"
        );
    }
    let mut changed = node.clone();
    changed.info.application_root[0] += F::ONE;
    let changed_application_accepted = if let Some(export) = &terminal_c1_export {
        verify_fixed_node(
            &child,
            &lifted_code,
            &node_code,
            &changed,
            &profiles.lift,
            &profiles.node,
            &export.preprocessing,
        )
        .is_ok()
    } else {
        verify_node(
            &child,
            &lifted_code,
            &node_code,
            &changed,
            &profiles.lift,
            &profiles.node,
            terminal_hash,
        )
        .is_ok()
    };
    if changed_application_accepted {
        return Err("changed application root was accepted".into());
    }
    let mut changed_claim = node.clone();
    changed_claim.info.original_bytecode_claim.value += EF::ONE;
    let changed_claim_accepted = if let Some(export) = &terminal_c1_export {
        verify_fixed_node(
            &child,
            &lifted_code,
            &node_code,
            &changed_claim,
            &profiles.lift,
            &profiles.node,
            &export.preprocessing,
        )
        .is_ok()
    } else {
        verify_node(
            &child,
            &lifted_code,
            &node_code,
            &changed_claim,
            &profiles.lift,
            &profiles.node,
            terminal_hash,
        )
        .is_ok()
    };
    if changed_claim_accepted {
        return Err("changed original program evaluation was accepted".into());
    }
    let mut wrong_profile = profiles.node;
    wrong_profile.security_bits -= 1;
    let wrong_profile_accepted = if let Some(export) = &terminal_c1_export {
        verify_fixed_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &wrong_profile,
            &export.preprocessing,
        )
        .is_ok()
    } else {
        verify_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &wrong_profile,
            terminal_hash,
        )
        .is_ok()
    };
    if wrong_profile_accepted {
        return Err("wrong node profile was accepted".into());
    }
    let final_negative_check = if let Some(export) = &terminal_c1_export {
        let mut wrong_preprocessing = export.preprocessing.clone();
        wrong_preprocessing.expected_keccak240_root[0] += F::ONE;
        if verify_fixed_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &profiles.node,
            &wrong_preprocessing,
        )
        .is_ok()
        {
            return Err("wrong fixed-program commitment was accepted".into());
        }
        "wrong fixed-program commitment rejected"
    } else {
        let wrong_hash = if profiles.terminal_keccak {
            ProofHashProfile::Poseidon1
        } else {
            ProofHashProfile::Keccak240
        };
        if verify_node(
            &child,
            &lifted_code,
            &node_code,
            &node,
            &profiles.lift,
            &profiles.node,
            wrong_hash,
        )
        .is_ok()
        {
            return Err("wrong terminal hash profile was accepted".into());
        }
        "wrong terminal hash profile rejected"
    };
    let layers = report["layers"].as_array().unwrap();
    let total_proving_ms: f64 = layers.iter().map(|entry| entry["proving_ms"].as_f64().unwrap()).sum();
    report["total_leanvm_proving_ms"] = json!(total_proving_ms);
    report["native_verification"] = json!("passed at all five LeanVM proofs");
    report["negative_checks"] = json!([
        "changed application root rejected",
        "changed original program evaluation rejected",
        "wrong terminal profile rejected",
        final_negative_check,
    ]);
    report["complete"] = json!(true);
    save(&output, &report)?;
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

fn application(directory: &Path) -> Result<Value, Box<dyn Error>> {
    let manifest: Value = serde_json::from_slice(&fs::read(directory.join("full_zk_spark_manifest.json"))?)?;
    Ok(json!({
        "application": manifest["application"],
        "application_details": manifest["application_details"],
        "sample_index": manifest["sample_index"],
        "raw_shape": manifest["raw_shape"],
        "relation_digest": manifest["relation_digest"],
    }))
}

fn base_words(values: &[F]) -> Vec<u32> {
    values.iter().map(|value| value.as_canonical_u32()).collect()
}

fn evaluation_json(claim: &Evaluation<EF>) -> Value {
    json!({
        "point": claim.point.0.iter().map(|value| base_words(value.as_basis_coefficients_slice())).collect::<Vec<_>>(),
        "value": base_words(claim.value.as_basis_coefficients_slice()),
    })
}

fn round_json(round: &RoundConfig<EF>) -> Value {
    json!({
        "query_pow_bits": round.query_pow_bits,
        "folding_pow_bits": round.folding_pow_bits,
        "num_queries": round.num_queries,
        "ood_samples": round.ood_samples,
        "log_inv_rate": round.log_inv_rate,
        "num_variables": round.num_variables,
        "folding_factor": round.folding_factor,
        "domain_size": round.domain_size,
        "folded_domain_gen": round.folded_domain_gen.as_canonical_u32(),
    })
}

fn opening_batch_json(
    role: &str,
    round: &RoundConfig<EF>,
    raw_opening_offset: usize,
    leaf_is_base_field: bool,
) -> Value {
    let leaf_fields = (1usize << round.folding_factor)
        * if leaf_is_base_field {
            1
        } else {
            <EF as BasedVectorSpace<F>>::DIMENSION
        };
    json!({
        "role": role,
        "raw_opening_offset": raw_opening_offset,
        "num_queries": round.num_queries,
        "merkle_height": (round.domain_size >> round.folding_factor).ilog2(),
        "leaf_fields": leaf_fields,
        "leaf_field": if leaf_is_base_field { "base" } else { "extension-basis" },
        "round": round_json(round),
    })
}

fn terminal_c1_opening_batches(config: &WhirConfig<EF>, grouped: bool) -> Result<Vec<Value>, Box<dyn Error>> {
    let first = config
        .round_parameters
        .first()
        .ok_or("terminal C1 requires at least one WHIR round")?;
    let mut raw_opening_offset = 0;
    let mut batches = Vec::with_capacity(config.round_parameters.len() + if grouped { 3 } else { 2 });
    for role in ["primary_initial", "fixed_program_initial", "grouped_helper_initial"]
        .into_iter()
        .take(if grouped { 3 } else { 2 })
    {
        batches.push(opening_batch_json(role, first, raw_opening_offset, true));
        raw_opening_offset += first.num_queries;
    }
    for (round_index, round) in config.round_parameters.iter().enumerate().skip(1) {
        batches.push(opening_batch_json(
            &format!("continuation_{round_index}"),
            round,
            raw_opening_offset,
            false,
        ));
        raw_opening_offset += round.num_queries;
    }
    let final_round = config.final_round_config();
    batches.push(opening_batch_json(
        "continuation_final",
        &final_round,
        raw_opening_offset,
        false,
    ));
    Ok(batches)
}

fn export_terminal(
    directory: &Path,
    bytecodes: [&Bytecode; 3],
    profiles: &Profiles,
    node: &rec_aggregation::BinaryNodeProof,
    verified: &rec_aggregation::InnerVerified,
    measurement: &Value,
    terminal_c1: Option<&TerminalC1Export>,
) -> Result<(), Box<dyn Error>> {
    fs::create_dir_all(directory)?;
    let proof_file = if profiles.terminal_grouped_logup {
        "root-proof-grouped.postcard"
    } else if terminal_c1.is_some() {
        "root-proof-c1.postcard"
    } else {
        "root-proof.postcard"
    };
    let proof_bytes = postcard::to_allocvec(&node.proof.proof)?;
    fs::write(directory.join(proof_file), &proof_bytes)?;
    let mut programs = Vec::new();
    for (name, bytecode) in ["spark", "lift", "root"].into_iter().zip(bytecodes) {
        let file = format!("{name}-bytecode-mle.u32le");
        let fields = bytecode.instructions_multilinear();
        let bytes = fields
            .iter()
            .flat_map(|value| value.as_canonical_u32().to_le_bytes())
            .collect::<Vec<_>>();
        let sha256 = format!("{:x}", Sha256::digest(&bytes));
        fs::write(directory.join(&file), bytes)?;
        programs.push(json!({
            "program": name,
            "hash": base_words(bytecode.hash()),
            "log_instructions": bytecode.log_size(),
            "instructions": bytecode.unpadded_size(),
            "ending_pc": bytecode.ending_pc(),
            "starting_frame_memory": bytecode.starting_frame_memory(),
            "mle_num_variables": bytecode.cumulated_n_vars(),
            "mle_fields": fields.len(),
            "mle_file": file,
            "mle_sha256": sha256,
        }));
    }
    let n_vars = measurement["stacked_num_variables"]
        .as_u64()
        .ok_or("missing root dimension")? as usize;
    let config = WhirConfig::<EF>::new(&profiles.node.whir_config(), n_vars);
    let mut record = json!({
            "schema": if terminal_c1.is_some() { "leanvm-terminal-two-commitment-fixture-v1" } else { "leanvm-terminal-fixture-v1" },
            "native_verification": if terminal_c1.is_some() {
                "passed, including the integrated fixed-program commitment and all three bytecode claims"
            } else {
                "passed, including the root, lift, and original SPARK program evaluations"
            },
        "hash_backend": if profiles.terminal_keccak { ProofHashProfile::Keccak240.id() } else { ProofHashProfile::Poseidon1.id() },
            "base_field_modulus": 2130706433u32,
            "extension_degree": 5,
            "extension_polynomial": "X^5 + X^2 - 1",
            "profiles": profiles,
            "proof_file": proof_file,
            "proof_bytes": proof_bytes.len(),
            "proof_sha256": format!("{:x}", Sha256::digest(&proof_bytes)),
            "public_input": base_words(&verified.input_data_hash),
            "node_info": base_words(&verified.input_data),
            "application_root": base_words(&node.info.application_root),
            "fiat_shamir_cap": base_words(&profiles.node.fiat_shamir_domain_sep(bytecodes[2])),
            "bytecodes": programs,
            "bytecode_claims": {
                "spark": evaluation_json(&node.info.original_bytecode_claim),
                "lift": evaluation_json(&node.info.child_bytecode_claim),
                "root": evaluation_json(&verified.bytecode_evaluation),
            },
            "sorted_table_perm": verified.sorted_table_perm,
            "raw_transcript": base_words(&verified.raw_proof.transcript),
            "merkle_openings": verified.raw_proof.merkle_openings.iter().map(|opening| json!({
                "leaf_data": base_words(&opening.leaf_data),
                "path": opening.path.iter().map(|digest| base_words(digest)).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "whir": {
                "num_variables": config.num_variables,
                "commitment_ood_samples": config.commitment_ood_samples,
                "starting_log_inv_rate": config.starting_log_inv_rate,
                "starting_folding_pow_bits": config.starting_folding_pow_bits,
                "rs_domain_initial_reduction_factor": config.rs_domain_initial_reduction_factor,
                "rounds": config.round_parameters.iter().map(round_json).collect::<Vec<_>>(),
                "final_round": round_json(&config.final_round_config()),
                "final_sumcheck_rounds": config.final_sumcheck_rounds,
            },
            "measurement": measurement,
    });
    if let Some(c1) = terminal_c1 {
        record["mode"] = json!("terminal-c1-two-commitment-whir-v1");
        let secondary_statements = c1.preprocessing.public_statements(&node.info)?;
        let statement_public_memory_bindings = terminal_c1_statement_public_memory_bindings_for_dimension(
            bytecodes[0],
            bytecodes[1],
            c1.preprocessing.num_variables,
        )?;
        let execution_prefix = terminal_c1_execution_program_prefix(bytecodes[2], c1.preprocessing.num_variables)?;
        let statement_observation = two_commitment_statement_observation(&secondary_statements);
        let (static_descriptor_field_count, static_descriptor) = two_commitment_fiat_shamir_static_descriptor(
            c1.preprocessing.num_variables,
            c1.preprocessing.actual_data_len,
            &secondary_statements,
            &statement_public_memory_bindings,
            &execution_prefix,
            TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
        );
        record["fiat_shamir_cap"] = json!(base_words(&two_commitment_fiat_shamir_domain_sep(
            &profiles.node,
            bytecodes[2],
            c1.preprocessing.num_variables,
            c1.preprocessing.actual_data_len,
            &secondary_statements,
            &statement_public_memory_bindings,
            &execution_prefix,
            TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
        )));
        let opening_batches = terminal_c1_opening_batches(&config, profiles.terminal_grouped_logup)?;
        let expected_openings = opening_batches
            .iter()
            .map(|batch| batch["num_queries"].as_u64().unwrap() as usize)
            .sum::<usize>();
        if expected_openings != verified.raw_proof.merkle_openings.len() {
            return Err("terminal C1 raw opening count does not match its exported batch layout".into());
        }
        let statement_public_memory_offsets = statement_public_memory_bindings
            .iter()
            .map(|binding| binding.public_memory_offset)
            .collect::<Vec<_>>();
        let statement_public_memory_bindings_json = statement_public_memory_bindings
            .iter()
            .map(|binding| {
                json!({
                    "public_memory_offset": binding.public_memory_offset,
                    "point_prefix_len": binding.point_prefix.len(),
                    "point_prefix": binding
                        .point_prefix
                        .iter()
                        .map(|coordinate| base_words(coordinate.as_basis_coefficients_slice()))
                        .collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>();
        record["two_commitment_whir"] = json!({
            "protocol_mode_tag": TWO_COMMITMENT_WHIR_MODE_TAG,
            "fiat_shamir_cap_scope": "static protocol shape, statement structure, selectors, public memory offsets, exact point prefixes, and fixed bytecode",
            "two_commitment_batching_pow_bits": TERMINAL_C1_TWO_COMMITMENT_BATCHING_POW_BITS,
            "execution_bytecode_point_prefix": execution_prefix.iter().map(|value| base_words(value.as_basis_coefficients_slice())[0]).collect::<Vec<_>>(),
            "static_descriptor": {
                "field_count_before_padding": static_descriptor_field_count,
                "padded_field_count": static_descriptor.len(),
                "fields": base_words(&static_descriptor),
            },
            "secondary_statement_public_memory_offsets": statement_public_memory_offsets,
            "secondary_statement_public_memory_bindings": statement_public_memory_bindings_json,
            "statement_observation": {
                "tag": TWO_COMMITMENT_WHIR_STATEMENT_TAG,
                "field_count": statement_observation.len(),
                "fields": base_words(&statement_observation),
                "transcript_order": "after public input and public memory; before dimensions and both commitment roots",
            },
            "primary": {
                "polynomial": "terminal execution stack",
                "num_variables": config.num_variables,
                "actual_data_len": measurement["stacked_entries"],
            },
            "secondary": {
                "polynomial": "fixed bytecode MLE",
                "layout": ["spark", "lift", "root"],
                "program_dimensions": c1.preprocessing.program_dimensions,
                "num_variables": c1.preprocessing.num_variables,
                "actual_data_len": c1.preprocessing.actual_data_len,
                "trusted_root": base_words(&c1.preprocessing.expected_keccak240_root),
            },
            "opening_batches": opening_batches,
            "compact_execution_proof": {
                "file": proof_file,
                "bytes": proof_bytes.len(),
                "sha256": format!("{:x}", Sha256::digest(&proof_bytes)),
                "raw_transcript_fields": verified.raw_proof.transcript.len(),
                "raw_transcript_u32le_bytes": verified.raw_proof.transcript.len() * size_of::<u32>(),
                "raw_merkle_openings": verified.raw_proof.merkle_openings.len(),
            },
            "preprocessing": {
                "fixed_polynomial_ms": c1.fixed_polynomial_ms,
                "fixed_commitment_ms": c1.fixed_commitment_ms,
                "total_ms": c1.fixed_polynomial_ms + c1.fixed_commitment_ms,
                "timing_boundary": "outside online proving and native verification",
            },
        });
    }
    if profiles.terminal_grouped_logup {
        record["schema"] = json!("leanvm-terminal-grouped-logup-experiment-v1");
        record["mode"] = json!("terminal-grouped-logup-three-commitment-whir-v1");
        record["native_verification"] =
            json!("passed, including all eight root-bytecode claims and the carried spark/lift claims");
        record["grouped_mode_observation"] = json!(base_words(&lean_prover::grouped_logup_mode_observation()));
        record["grouped_mode_observation_order"] =
            json!("before public input, public memory, dynamic fixed-program claims, dimensions and first commitment");
        record["full_composition_security_established"] = json!(false);
        record["bytecode_claims"]["root_diagnostic_scope"] =
            json!("first of eight root evaluations; all eight are in the grouped transcript and authenticated by WHIR");
        let mut three = record.as_object_mut().unwrap().remove("two_commitment_whir").unwrap();
        three.as_object_mut().unwrap().remove("protocol_mode_tag");
        three
            .as_object_mut()
            .unwrap()
            .remove("two_commitment_batching_pow_bits");
        three["three_commitment_batching_pow_bits"] = json!(lean_prover::GROUPED_BATCHING_POW_BITS);
        three["helper"] = json!({ "polynomial": "grouped inverse products in five base-field coordinates", "num_variables": config.num_variables });
        three["statement_observation"]["transcript_order"] =
            json!("after public input and public memory; before dimensions and all three commitment roots");
        record["three_commitment_whir"] = three;
    }
    if profiles.terminal_public_memory {
        record["public_memory_region"] = json!({
            "domain": 0x50554d31u32,
            "start": 4096,
            "values": base_words(&verified.input_data),
        });
    }
    save(&directory.join("root-fixture.json"), &record)
}

fn validate_mutations(
    fixture: &SparkGuestFixture,
    directory: &Path,
    bytecode: &Bytecode,
    words: &[u32],
    options: &SparkGuestOptimizations,
) -> Result<Value, Box<dyn Error>> {
    fixture.validate_words(bytecode, words, options)?;
    let cases: Value = serde_json::from_slice(&fs::read(directory.join("full_zk_spark_mutations.json"))?)?;
    let mut results = Vec::new();
    for case in cases["cases"].as_array().ok_or("missing mutation cases")? {
        let mut changed = words.to_vec();
        let mut applied = false;
        for patch in case["patches"].as_array().ok_or("missing mutation patches")? {
            let original = patch["offset"].as_u64().ok_or("missing patch offset")? as usize;
            let canonical = fixture.normalized_offset(original)?;
            let Some(offset) = fixture.compact_offset(canonical, options)? else {
                continue;
            };
            let before = patch["before"].as_u64().ok_or("missing patch precondition")? as u32;
            let after = patch["after"].as_u64().ok_or("missing patch value")? as u32;
            if original == 8 {
                // The transport normalization changes total_words while the
                // mutation still changes that total by the original delta.
                changed[offset] = u32::try_from(i64::from(changed[offset]) + i64::from(after) - i64::from(before))?;
            } else {
                if changed[offset] != before {
                    return Err(format!("mutation precondition failed: {}", case["name"]).into());
                }
                changed[offset] = after;
            }
            applied = true;
        }
        if applied {
            if fixture.validate_words(bytecode, &changed, options).is_ok() {
                return Err(format!("mutation accepted: {}", case["name"]).into());
            }
            results.push(json!({"name": case["name"], "status": "rejected"}));
        } else {
            results.push(json!({"name": case["name"], "status": "field omitted from compact encoding"}));
        }
    }
    Ok(json!(results))
}

fn layer(
    name: &str,
    bytecode: &Bytecode,
    proof: &ExecutionProof,
    raw: &RawProof<F>,
    proving_ms: f64,
    verification_ms: f64,
) -> Result<Value, Box<dyn Error>> {
    let dims = raw.transcript[..2 + lean_vm::N_TABLES]
        .iter()
        .map(|value| value.as_canonical_u32() as usize)
        .collect::<Vec<_>>();
    let mut tables = BTreeMap::new();
    let mut table_entries = 0;
    let mut maximum_height = bytecode.code().len();
    for (i, table) in lean_vm::ALL_TABLES.iter().enumerate() {
        let rows = 1usize << dims[i + 2];
        let entries = rows * table.n_columns();
        table_entries += entries;
        maximum_height = maximum_height.max(rows);
        tables.insert(
            table.name(),
            json!({"log_rows": dims[i + 2], "rows": rows, "columns": table.n_columns(), "entries": entries}),
        );
    }
    let total = (2usize << dims[1]) + maximum_height + table_entries;
    let metadata = proof.metadata.as_ref().ok_or("missing execution metadata")?;
    Ok(json!({
        "layer": name,
        "proving_ms": proving_ms,
        "verification_ms": verification_ms,
        "proof_bytes": postcard::to_allocvec(&proof.proof)?.len(),
        "process_peak_rss_bytes": system_info::peak_rss_bytes(),
        "bytecode_instructions": bytecode.unpadded_size(),
        "bytecode_padded_instructions": bytecode.code().len(),
        "bytecode_hash": bytecode.hash().iter().map(|value| value.as_canonical_u32()).collect::<Vec<_>>(),
        "raw": {"execution_rows": metadata.cycles, "extension_rows": metadata.n_extension_ops, "poseidon_calls": metadata.n_poseidons, "memory_cells": metadata.memory},
        "log_memory": dims[1],
        "tables": tables,
        "stacked_entries": total,
        "stacked_num_variables": total.next_power_of_two().ilog2(),
        "profiling_report": metadata.profiling_report,
        "native_verification": "passed",
    }))
}

fn recursive_child_shape(raw: &RawProof<F>) -> Result<RecursiveChildShape, Box<dyn Error>> {
    Ok(RecursiveChildShape::from_verified_raw_proof(raw)?)
}

fn save(path: &Path, value: &Value) -> Result<(), Box<dyn Error>> {
    if let Some(parent) = path.parent().filter(|parent| !parent.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    let mut text = serde_json::to_string_pretty(value)?;
    text.push('\n');
    fs::write(path, text)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_profile_defaults_to_the_legacy_terminal_mode() {
        let mut encoded = serde_json::to_value(Profiles::default()).unwrap();
        encoded.as_object_mut().unwrap().remove("terminal_two_commitment");
        let decoded: Profiles = serde_json::from_value(encoded).unwrap();
        assert!(!decoded.terminal_two_commitment);
    }

    #[test]
    fn grouped_opening_layout_authenticates_three_initial_roots() {
        let profiles: Profiles = serde_json::from_str(include_str!("../../profiles/terminal_grouped.json")).unwrap();
        let config = WhirConfig::<EF>::new(&profiles.node.whir_config(), 23);
        let batches = terminal_c1_opening_batches(&config, true).unwrap();
        assert_eq!(
            batches
                .iter()
                .map(|batch| batch["num_queries"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            vec![25, 25, 25, 15, 12, 10]
        );
        assert_eq!(
            batches
                .iter()
                .map(|batch| batch["raw_opening_offset"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            vec![0, 25, 50, 75, 90, 102]
        );
        assert_eq!(batches[2]["role"], "grouped_helper_initial");
        assert!(batches[..3].iter().all(|batch| batch["leaf_field"] == "base"));
        assert!(
            batches[3..]
                .iter()
                .all(|batch| batch["leaf_field"] == "extension-basis")
        );
    }

    #[test]
    fn terminal_c1_opening_layout_duplicates_only_the_initial_commitment_batch() {
        let profile = WhirExecutionProfile::security_100(1);
        let config = WhirConfig::<EF>::new(&profile.whir_config(), 23);
        let batches = terminal_c1_opening_batches(&config, false).unwrap();

        assert_eq!(batches.len(), config.round_parameters.len() + 2);
        assert_eq!(batches[0]["role"], "primary_initial");
        assert_eq!(batches[1]["role"], "fixed_program_initial");
        assert_eq!(batches[0]["round"], batches[1]["round"]);
        assert_eq!(batches[0]["leaf_field"], "base");
        assert_eq!(batches[1]["leaf_field"], "base");
        assert!(
            batches
                .iter()
                .skip(2)
                .all(|batch| batch["leaf_field"] == "extension-basis")
        );

        let mut expected_offset = 0;
        for batch in batches {
            assert_eq!(batch["raw_opening_offset"], expected_offset);
            expected_offset += batch["num_queries"].as_u64().unwrap();
        }
    }
}
