//! Diagnostic fixed-program WHIR openings for a generated terminal root fixture.
use std::{
    error::Error,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use backend::{
    ArenaVec, BasedVectorSpace, ChallengeSampler, Evaluation, FSProver, FSVerifier, MleOwned, MultilinearPoint,
    PrimeCharacteristicRing, PrimeField32, Proof, ProofError, ProofHashProfile, ProverState, RawProof, RoundConfig,
    SparseStatement, VerifierState, WhirConfig, Witness, get_poseidon16, poseidon_hash_slice, poseidon16_compress_pair,
};
use lean_prover::WhirExecutionProfile;
use lean_vm::{EF, F};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const ORACLE_DOMAIN: u32 = 0x46424f31; // Domain tag for fixed bytecode oracle commitments.

fn words(values: &[F]) -> Vec<u32> {
    values.iter().map(|v| v.as_canonical_u32()).collect()
}

fn fields(value: &Value) -> Result<Vec<F>, Box<dyn Error>> {
    value
        .as_array()
        .ok_or("expected field array")?
        .iter()
        .map(|v| {
            let n = v.as_u64().ok_or("expected unsigned field value")?;
            if n >= 2_130_706_433 {
                return Err("noncanonical field value".into());
            }
            Ok(F::from_u32(n as u32))
        })
        .collect()
}

fn evaluation(value: &Value, n_vars: usize) -> Result<Evaluation<EF>, Box<dyn Error>> {
    let point = value["point"]
        .as_array()
        .ok_or("missing evaluation point")?
        .iter()
        .map(|v| {
            let v = fields(v)?;
            if v.len() != 5 {
                return Err("extension length mismatch".into());
            }
            EF::from_basis_coefficients_slice(&v).ok_or_else(|| "invalid extension coefficients".into())
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    if point.len() != n_vars {
        return Err("evaluation dimension mismatch".into());
    }
    let value = fields(&value["value"])?;
    if value.len() != 5 {
        return Err("extension length mismatch".into());
    }
    Ok(Evaluation::new(
        point,
        EF::from_basis_coefficients_slice(&value).ok_or("invalid extension coefficients")?,
    ))
}

fn capacity(hash: &[F; 8], profile: &WhirExecutionProfile) -> [F; 8] {
    let parameters = [
        ORACLE_DOMAIN as usize,
        profile.security_bits,
        profile.grinding_bits,
        profile.first_folding_factor,
        profile.subsequent_folding_factor,
        profile.rs_domain_initial_reduction_factor,
        profile.max_num_variables_to_send_coeffs,
        profile.log_inv_rate,
    ]
    .map(F::from_usize);
    poseidon16_compress_pair(hash, &parameters)
}

fn statement_prefix(index: usize, root: &[F; 8], claim: &Evaluation<EF>, context: &[F; 8]) -> Vec<F> {
    let mut result = vec![F::from_usize(index), F::from_usize(claim.point.len()), F::ONE];
    result.resize(8, F::ZERO);
    result.extend_from_slice(root);
    result.extend_from_slice(context);
    for element in claim.point.iter().chain(std::iter::once(&claim.value)) {
        result.extend_from_slice(element.as_basis_coefficients_slice());
    }
    result.resize(result.len().next_multiple_of(8), F::ZERO);
    result
}

fn verify_oracle(
    config: &WhirConfig<EF>,
    proof: Proof<F>,
    cap: [F; 8],
    root: [F; 8],
    prefix: &[F],
    claim: &Evaluation<EF>,
    hash_profile: ProofHashProfile,
) -> Result<RawProof<F>, ProofError> {
    let mut verifier =
        VerifierState::<EF, _>::new_with_hash_profile(proof, get_poseidon16().clone(), cap, hash_profile)?;
    verifier.observe_scalars(prefix);
    let commitment = config.parse_commitment::<F>(&mut verifier)?;
    if commitment.root != root {
        return Err(ProofError::InvalidProof);
    }
    config.verify::<F>(
        &mut verifier,
        &commitment,
        vec![SparseStatement::dense(claim.point.clone(), claim.value)],
    )?;
    verifier.check_fully_consumed()?;
    Ok(verifier.into_raw_proof())
}

fn round_json(round: &RoundConfig<EF>) -> Value {
    json!({
        "query_pow_bits": round.query_pow_bits, "folding_pow_bits": round.folding_pow_bits,
        "num_queries": round.num_queries, "ood_samples": round.ood_samples,
        "log_inv_rate": round.log_inv_rate, "num_variables": round.num_variables,
        "folding_factor": round.folding_factor, "domain_size": round.domain_size,
        "folded_domain_gen": round.folded_domain_gen.as_canonical_u32(),
    })
}

fn config_json(config: &WhirConfig<EF>) -> Value {
    json!({
        "num_variables": config.num_variables, "commitment_ood_samples": config.commitment_ood_samples,
        "starting_log_inv_rate": config.starting_log_inv_rate, "starting_folding_pow_bits": config.starting_folding_pow_bits,
        "rs_domain_initial_reduction_factor": config.rs_domain_initial_reduction_factor,
        "rounds": config.round_parameters.iter().map(round_json).collect::<Vec<_>>(),
        "final_round": round_json(&config.final_round_config()), "final_sumcheck_rounds": config.final_sumcheck_rounds,
    })
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args().skip(1);
    let first = args
        .next()
        .ok_or("usage: leanvm-fixed-bytecode-oracles ROOT_FIXTURE OUTPUT_DIR [PROFILE_JSON] [poseidon|keccak240]; or --describe PROFILE_JSON [N_VARS...]")?;
    if first == "--describe" {
        let profile: WhirExecutionProfile =
            serde_json::from_slice(&fs::read(args.next().ok_or("missing profile JSON")?)?)?;
        profile.validate_for_hash(ProofHashProfile::Keccak240)?;
        let mut dimensions = args.map(|arg| arg.parse::<usize>()).collect::<Result<Vec<_>, _>>()?;
        if dimensions.is_empty() {
            dimensions = vec![21, 22];
        }
        let mut configurations = Vec::new();
        for n_vars in dimensions {
            if n_vars > 22 {
                return Err("fixed oracle dimension exceeds 22".into());
            }
            profile.validate_for_n_vars(n_vars)?;
            configurations.push(config_json(&WhirConfig::<EF>::new(&profile.whir_config(), n_vars)));
        }
        println!(
            "{}",
            serde_json::to_string_pretty(&json!({
                "profile": profile, "hash_backend": ProofHashProfile::Keccak240.id(), "configurations": configurations,
            }))?
        );
        return Ok(());
    }
    let manifest = PathBuf::from(first);
    let output = PathBuf::from(args.next().ok_or("missing output directory")?);
    if output.exists() {
        return Err("output directory already exists".into());
    }
    let profile = if let Some(path) = args.next() {
        serde_json::from_slice::<WhirExecutionProfile>(&fs::read(path)?)?
    } else {
        WhirExecutionProfile {
            security_bits: 100,
            grinding_bits: 20,
            first_folding_factor: 5,
            subsequent_folding_factor: 4,
            rs_domain_initial_reduction_factor: 4,
            max_num_variables_to_send_coeffs: 3,
            log_inv_rate: 3,
        }
    };
    profile.validate().map_err(|e| format!("invalid oracle profile: {e}"))?;
    let hash_profile = match args.next().as_deref().unwrap_or("keccak240") {
        "poseidon" => ProofHashProfile::Poseidon1,
        "keccak240" => ProofHashProfile::Keccak240,
        _ => return Err("unsupported hash profile".into()),
    };
    profile
        .validate_for_hash(hash_profile)
        .map_err(|e| format!("invalid oracle hash profile: {e}"))?;
    if args.next().is_some() {
        return Err("too many arguments".into());
    }
    let manifest_bytes = fs::read(&manifest)?;
    let fixture: Value = serde_json::from_slice(&manifest_bytes)?;
    if fixture["schema"] != "leanvm-terminal-fixture-v1" {
        return Err("unsupported root fixture".into());
    }
    let context: [F; 8] = fields(&fixture["public_input"])?
        .try_into()
        .map_err(|_| "public input length")?;
    let directory = manifest.parent().unwrap_or(Path::new("."));
    fs::create_dir_all(&output)?;
    let mut reports = Vec::new();
    for (index, name) in ["spark", "lift", "root"].into_iter().enumerate() {
        let metadata = fixture["bytecodes"]
            .as_array()
            .ok_or("missing bytecodes")?
            .iter()
            .find(|m| m["program"] == name)
            .ok_or("missing fixed program")?;
        let file = metadata["mle_file"].as_str().ok_or("missing fixed polynomial file")?;
        if Path::new(file).file_name().and_then(|v| v.to_str()) != Some(file) {
            return Err("invalid polynomial filename".into());
        }
        let data = fs::read(directory.join(file))?;
        let digest = format!("{:x}", Sha256::digest(&data));
        if metadata["mle_sha256"].as_str() != Some(&digest) {
            return Err("fixed program SHA256 mismatch".into());
        }
        if data.len() % 4 != 0 {
            return Err("invalid polynomial byte length".into());
        }
        let values = data
            .chunks_exact(4)
            .map(|bytes| {
                let n = u32::from_le_bytes(bytes.try_into().unwrap());
                if n >= 2_130_706_433 {
                    return Err("noncanonical polynomial value");
                }
                Ok(F::from_u32(n))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let n_vars = metadata["mle_num_variables"]
            .as_u64()
            .ok_or("missing polynomial dimension")? as usize;
        if n_vars > 22 || values.len() != 1usize << n_vars {
            return Err("fixed polynomial must have at most 22 variables and exact length".into());
        }
        profile
            .validate_for_n_vars(n_vars)
            .map_err(|e| format!("invalid oracle dimension: {e}"))?;
        let hash: [F; 8] = fields(&metadata["hash"])?.try_into().map_err(|_| "hash length")?;
        let setup = Instant::now();
        if poseidon_hash_slice(&values) != hash {
            return Err("fixed program Poseidon identity mismatch".into());
        }
        let polynomial = MleOwned::<EF>::Base(ArenaVec::from_slice(&values));
        let config = WhirConfig::<EF>::new(&profile.whir_config(), n_vars);
        let (prover_data, root) =
            config.build_commitment_data_with_hash_profile(&polynomial, values.len(), hash_profile);
        let preprocessing_ms = setup.elapsed().as_secs_f64() * 1000.0;
        let proving = Instant::now();
        let claim = evaluation(&fixture["bytecode_claims"][name], n_vars)?;
        if polynomial.evaluate(&claim.point) != claim.value {
            return Err("root requested a false fixed program evaluation".into());
        }
        let cap = capacity(&hash, &profile);
        let prefix = statement_prefix(index, &root, &claim, &context);
        let mut prover = ProverState::<EF, _>::new_with_hash_profile(get_poseidon16().clone(), cap, hash_profile);
        prover.observe_scalars(&prefix);
        prover.add_base_scalars(&root);
        let ood_points = prover.sample_vec(config.commitment_ood_samples);
        let ood_answers = ood_points
            .iter()
            .map(|&p| polynomial.evaluate(&MultilinearPoint::expand_from_univariate(p, n_vars)))
            .collect::<Vec<_>>();
        if !ood_answers.is_empty() {
            prover.add_extension_scalars(&ood_answers);
        }
        let witness = Witness {
            prover_data,
            ood_points,
            ood_answers,
        };
        config.prove(
            &mut prover,
            vec![SparseStatement::dense(claim.point.clone(), claim.value)],
            witness,
            &polynomial.by_ref(),
        );
        let proof = prover.into_proof();
        let proving_ms = proving.elapsed().as_secs_f64() * 1000.0;
        let verifying = Instant::now();
        let raw = verify_oracle(&config, proof.clone(), cap, root, &prefix, &claim, hash_profile)?;
        let verifying_ms = verifying.elapsed().as_secs_f64() * 1000.0;
        let mut changed = claim.clone();
        changed.value += EF::ONE;
        let changed_prefix = statement_prefix(index, &root, &changed, &context);
        if verify_oracle(
            &config,
            proof.clone(),
            cap,
            root,
            &changed_prefix,
            &changed,
            hash_profile,
        )
        .is_ok()
        {
            return Err("changed evaluation accepted".into());
        }
        let mut wrong_root = root;
        wrong_root[0] += F::ONE;
        if verify_oracle(&config, proof.clone(), cap, wrong_root, &prefix, &claim, hash_profile).is_ok() {
            return Err("changed trusted root accepted".into());
        }
        let encoded = postcard::to_allocvec(&proof)?;
        let proof_name = format!("{name}-oracle.postcard");
        fs::write(output.join(&proof_name), &encoded)?;
        let record = json!({
            "program": name, "program_index": index, "program_hash": words(&hash),
            "mle_sha256": digest, "num_variables": n_vars, "commitment": words(&root),
            "capacity": words(&cap), "statement_prefix": words(&prefix),
            "claim": fixture["bytecode_claims"][name], "context": words(&context),
            "hash_backend": hash_profile.id(), "profile": profile,
            "proof_file": proof_name, "proof_bytes": encoded.len(),
            "preprocessing_ms": preprocessing_ms, "proving_ms": proving_ms, "verifying_ms": verifying_ms,
            "native_verification": "passed", "changed_evaluation_rejected": true, "changed_commitment_rejected": true,
            "raw_transcript": words(&raw.transcript),
            "merkle_openings": raw.merkle_openings.iter().map(|opening| json!({
                "leaf_data": words(&opening.leaf_data), "path": opening.path.iter().map(|digest| words(digest)).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
            "whir": config_json(&config),
        });
        fs::write(
            output.join(format!("{name}-oracle.json")),
            serde_json::to_vec_pretty(&record)?,
        )?;
        println!(
            "{name}: setup {preprocessing_ms:.1}ms, opening {proving_ms:.1}ms, verify {verifying_ms:.2}ms, {} bytes",
            encoded.len()
        );
        reports.push(json!({"program": name, "preprocessing_ms": preprocessing_ms, "proving_ms": proving_ms, "verifying_ms": verifying_ms, "proof_bytes": encoded.len(), "commitment": words(&root), "program_hash": words(&hash), "num_variables": n_vars, "whir": record["whir"]}));
    }
    fs::write(
        output.join("summary.json"),
        serde_json::to_vec_pretty(&json!({
            "schema": "leanvm-fixed-bytecode-oracles-v1", "root_fixture_sha256": format!("{:x}", Sha256::digest(&manifest_bytes)),
            "hash_backend": hash_profile.id(), "profile": profile, "oracles": reports,
            "timing_boundary": "preprocessing includes fixed-program identity hashing and first commitment; opening includes requested-claim decoding/validation, transcript preparation, fresh OOD evaluations, and WHIR proving; setup is reusable for the selected fixed program and profile; input decoding, serialization, and negative tests excluded",
        }))?,
    )?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
