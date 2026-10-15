//! One WHIR commitment authenticating the three fixed programs in a terminal root.
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

const ORACLE_DOMAIN: u32 = 0x46424331; // Domain tag for a combined fixed-program commitment.

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

fn statement_prefix(dimensions: &[usize; 3], root: &[F; 8], claims: &[Evaluation<EF>], context: &[F; 8]) -> Vec<F> {
    let n_vars = claims[0].point.len();
    let mut prefix = vec![
        F::from_u32(ORACLE_DOMAIN),
        F::from_usize(claims.len()),
        F::from_usize(n_vars),
        F::from_usize(dimensions[0]),
        F::from_usize(dimensions[1]),
        F::from_usize(dimensions[2]),
        F::ZERO,
        F::ZERO,
    ];
    prefix.extend_from_slice(root);
    prefix.extend_from_slice(context);
    for claim in claims {
        for value in claim.point.iter().chain(std::iter::once(&claim.value)) {
            prefix.extend_from_slice(value.as_basis_coefficients_slice());
        }
        prefix.resize(prefix.len().next_multiple_of(8), F::ZERO);
    }
    prefix
}

fn verify_combined(
    config: &WhirConfig<EF>,
    proof: Proof<F>,
    cap: [F; 8],
    root: [F; 8],
    dimensions: &[usize; 3],
    claims: &[Evaluation<EF>],
    context: &[F; 8],
) -> Result<RawProof<F>, ProofError> {
    if claims.len() != 3 || claims.iter().any(|claim| claim.point.len() != config.num_variables) {
        return Err(ProofError::InvalidProof);
    }
    let mut verifier = VerifierState::<EF, _>::new_with_hash_profile(
        proof,
        get_poseidon16().clone(),
        cap,
        ProofHashProfile::Keccak240,
    )?;
    verifier.observe_scalars(&statement_prefix(dimensions, &root, claims, context));
    let commitment = config.parse_commitment::<F>(&mut verifier)?;
    if commitment.root != root {
        return Err(ProofError::InvalidProof);
    }
    config.verify::<F>(
        &mut verifier,
        &commitment,
        claims
            .iter()
            .map(|claim| SparseStatement::dense(claim.point.clone(), claim.value))
            .collect(),
    )?;
    verifier.check_fully_consumed()?;
    Ok(verifier.into_raw_proof())
}

fn prefix_challenge(cap: [F; 8], prefix: &[F]) -> EF {
    let mut prover =
        ProverState::<EF, _>::new_with_hash_profile(get_poseidon16().clone(), cap, ProofHashProfile::Keccak240);
    prover.observe_scalars(prefix);
    prover.sample_vec(1)[0]
}

fn claim_json(claim: &Evaluation<EF>) -> Value {
    json!({"point": claim.point.iter().map(|x| words(x.as_basis_coefficients_slice())).collect::<Vec<_>>(),
        "value": words(claim.value.as_basis_coefficients_slice())})
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
    let manifest = PathBuf::from(
        args.next()
            .ok_or("usage: leanvm-combined-bytecode-oracle ROOT_FIXTURE OUTPUT_DIR PROFILE_JSON")?,
    );
    let output = PathBuf::from(args.next().ok_or("missing output directory")?);
    let profile: WhirExecutionProfile = serde_json::from_slice(&fs::read(args.next().ok_or("missing profile JSON")?)?)?;
    if args.next().is_some() || output.exists() {
        return Err("extra arguments or output already exists".into());
    }
    profile.validate_for_hash(ProofHashProfile::Keccak240)?;
    let manifest_bytes = fs::read(&manifest)?;
    let fixture: Value = serde_json::from_slice(&manifest_bytes)?;
    if fixture["schema"] != "leanvm-terminal-fixture-v1" {
        return Err("unsupported root fixture".into());
    }
    let context: [F; 8] = fields(&fixture["public_input"])?
        .try_into()
        .map_err(|_| "public input length")?;
    let directory = manifest.parent().unwrap_or(Path::new("."));
    let mut dimensions = [0usize; 3];
    let mut program_hashes = Vec::new();
    let mut data = Vec::new();
    let mut claims = Vec::new();
    let mut programs = Vec::new();
    let mut identity_ms = 0.0;
    for (index, name) in ["spark", "lift", "root"].into_iter().enumerate() {
        let metadata = fixture["bytecodes"]
            .as_array()
            .ok_or("missing bytecodes")?
            .iter()
            .find(|m| m["program"] == name)
            .ok_or("missing fixed program")?;
        let file = metadata["mle_file"].as_str().ok_or("missing MLE file")?;
        if Path::new(file).file_name().and_then(|x| x.to_str()) != Some(file) {
            return Err("invalid polynomial filename".into());
        }
        let bytes = fs::read(directory.join(file))?;
        let sha = format!("{:x}", Sha256::digest(&bytes));
        if metadata["mle_sha256"].as_str() != Some(&sha) || bytes.len() % 4 != 0 {
            return Err("polynomial file mismatch".into());
        }
        let values = bytes
            .chunks_exact(4)
            .map(|bytes| {
                let n = u32::from_le_bytes(bytes.try_into().unwrap());
                if n >= 2_130_706_433 {
                    return Err("noncanonical polynomial value");
                }
                Ok(F::from_u32(n))
            })
            .collect::<Result<Vec<_>, _>>()?;
        dimensions[index] = metadata["mle_num_variables"].as_u64().ok_or("missing dimension")? as usize;
        if dimensions[index] > 22 || values.len() != 1usize << dimensions[index] {
            return Err("invalid program dimension".into());
        }
        let hash: [F; 8] = fields(&metadata["hash"])?.try_into().map_err(|_| "hash length")?;
        let start = Instant::now();
        if poseidon_hash_slice(&values) != hash {
            return Err("program identity mismatch".into());
        }
        identity_ms += start.elapsed().as_secs_f64() * 1000.0;
        program_hashes.extend_from_slice(&hash);
        data.extend_from_slice(&values);
        claims.push(evaluation(&fixture["bytecode_claims"][name], dimensions[index])?);
        programs.push(
            json!({"program": name, "hash": words(&hash), "mle_sha256": sha, "num_variables": dimensions[index]}),
        );
    }
    // The first program occupies the lower half; the other two occupy the upper quarters.
    if dimensions[0] != dimensions[1] + 1 || dimensions[1] != dimensions[2] {
        return Err("combined layout requires dimensions [n,n-1,n-1]".into());
    }
    let n_vars = dimensions[0] + 1;
    profile.validate_for_n_vars(n_vars)?;
    if data.len() != 1usize << n_vars {
        return Err("combined polynomial length".into());
    }
    for (index, claim) in claims.iter_mut().enumerate() {
        let mut point = if index == 0 {
            vec![EF::ZERO]
        } else {
            vec![EF::ONE, if index == 1 { EF::ZERO } else { EF::ONE }]
        };
        point.extend_from_slice(&claim.point);
        claim.point = MultilinearPoint(point);
    }
    let start = Instant::now();
    let identity = poseidon_hash_slice(&program_hashes);
    let cap = capacity(&identity, &profile);
    let polynomial = MleOwned::<EF>::Base(ArenaVec::from_slice(&data));
    let config = WhirConfig::<EF>::new(&profile.whir_config(), n_vars);
    let (prover_data, root) =
        config.build_commitment_data_with_hash_profile(&polynomial, data.len(), ProofHashProfile::Keccak240);
    let preprocessing_ms = identity_ms + start.elapsed().as_secs_f64() * 1000.0;
    let prefix = statement_prefix(&dimensions, &root, &claims, &context);
    let start = Instant::now();
    for claim in &claims {
        if polynomial.evaluate(&claim.point) != claim.value {
            return Err("incorrect combined program evaluation or coordinate embedding".into());
        }
    }
    let mut prover =
        ProverState::<EF, _>::new_with_hash_profile(get_poseidon16().clone(), cap, ProofHashProfile::Keccak240);
    prover.observe_scalars(&prefix);
    prover.add_base_scalars(&root);
    let ood_points = prover.sample_vec(config.commitment_ood_samples);
    let ood_answers = ood_points
        .iter()
        .map(|&point| polynomial.evaluate(&MultilinearPoint::expand_from_univariate(point, n_vars)))
        .collect::<Vec<_>>();
    if !ood_answers.is_empty() {
        prover.add_extension_scalars(&ood_answers);
    }
    config.prove(
        &mut prover,
        claims
            .iter()
            .map(|claim| SparseStatement::dense(claim.point.clone(), claim.value))
            .collect(),
        Witness {
            prover_data,
            ood_points,
            ood_answers,
        },
        &polynomial.by_ref(),
    );
    let proof = prover.into_proof();
    let proving_ms = start.elapsed().as_secs_f64() * 1000.0;
    let start = Instant::now();
    let raw = verify_combined(&config, proof.clone(), cap, root, &dimensions, &claims, &context)?;
    let verifying_ms = start.elapsed().as_secs_f64() * 1000.0;
    let mut negatives = Vec::new();
    for index in 0..3 {
        for point in [false, true] {
            let mut changed = claims.clone();
            if point {
                changed[index].point[n_vars - 1] += EF::ONE;
            } else {
                changed[index].value += EF::ONE;
            }
            if verify_combined(&config, proof.clone(), cap, root, &dimensions, &changed, &context).is_ok() {
                return Err("changed claim accepted".into());
            }
            negatives.push(format!(
                "claim {index} {} rejected",
                if point { "point" } else { "value" }
            ));
        }
    }
    let mut swapped = claims.clone();
    swapped.swap(0, 1);
    if verify_combined(&config, proof.clone(), cap, root, &dimensions, &swapped, &context).is_ok() {
        return Err("reordered claims accepted".into());
    }
    negatives.push("reordered claims rejected".into());
    let mut wrong_root = root;
    wrong_root[0] += F::ONE;
    if verify_combined(&config, proof.clone(), cap, wrong_root, &dimensions, &claims, &context).is_ok() {
        return Err("changed root accepted".into());
    }
    negatives.push("changed commitment rejected".into());
    let mut wrong_context = context;
    wrong_context[0] += F::ONE;
    if verify_combined(&config, proof.clone(), cap, root, &dimensions, &claims, &wrong_context).is_ok() {
        return Err("changed context accepted".into());
    }
    negatives.push("changed context rejected".into());
    let mut wrong_dims = dimensions;
    wrong_dims[0] += 1;
    if verify_combined(&config, proof.clone(), cap, root, &wrong_dims, &claims, &context).is_ok() {
        return Err("changed dimensions accepted".into());
    }
    negatives.push("changed dimensions rejected".into());
    let challenge = prefix_challenge(cap, &prefix);
    for index in 0..prefix.len() {
        let mut changed = prefix.clone();
        changed[index] += F::ONE;
        if prefix_challenge(cap, &changed) == challenge {
            return Err("statement field does not affect challenge".into());
        }
    }
    let encoded = postcard::to_allocvec(&proof)?;
    let record = json!({
        "schema": "leanvm-combined-bytecode-oracle-v1", "root_fixture_sha256": format!("{:x}",Sha256::digest(&manifest_bytes)),
        "programs": programs, "program_dimensions": dimensions, "num_variables": n_vars, "combined_program_hash": words(&identity),
        "capacity": words(&cap), "commitment": words(&root), "context": words(&context), "statement_prefix": words(&prefix),
        "claims": claims.iter().map(claim_json).collect::<Vec<_>>(), "hash_backend": ProofHashProfile::Keccak240.id(), "profile": profile,
        "whir": config_json(&config), "preprocessing_ms": preprocessing_ms, "proving_ms": proving_ms, "verifying_ms": verifying_ms,
        "proof_bytes": encoded.len(), "native_verification": "passed", "negative_checks": negatives,
        "challenge_sensitivity_fields": prefix.len(), "prefix_challenge": words(challenge.as_basis_coefficients_slice()),
        "raw_transcript": words(&raw.transcript), "merkle_openings": raw.merkle_openings.iter().map(|opening| json!({
            "leaf_data": words(&opening.leaf_data), "path": opening.path.iter().map(|digest| words(digest)).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "timing_boundary": "setup includes program identity authentication and combined commitment; online includes three requested evaluations, fresh OOD and one batched WHIR proof; input decoding, serialization, verification and negatives excluded",
    });
    fs::create_dir_all(&output)?;
    fs::write(output.join("combined-oracle.postcard"), encoded)?;
    fs::write(output.join("combined-oracle.json"), serde_json::to_vec_pretty(&record)?)?;
    println!(
        "combined: setup {preprocessing_ms:.1}ms, prove {proving_ms:.1}ms, verify {verifying_ms:.2}ms; {n_vars} variables; all negatives passed"
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
