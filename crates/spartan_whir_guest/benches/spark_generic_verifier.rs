use backend::PrimeField32;
use criterion::{BatchSize, Criterion, SamplingMode};
use lean_prover::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use serde_json::json;
use spartan_whir_guest::{FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE, SparkGuestFixture, SparkGuestOptimizations};
use std::{
    hint::black_box,
    time::{Duration, Instant},
};

fn bench(c: &mut Criterion) {
    let variant = std::env::var("SPARK_GUEST_VARIANT").unwrap_or_else(|_| "control".into());
    let mut options = SparkGuestOptimizations::recommended();
    match variant.as_str() {
        "control" => {
            options.query_permutation = false;
            options.unroll_powers = false;
            options.block_query_powers = false;
        }
        "query_permutation" => {
            options.query_permutation = true;
            options.unroll_powers = false;
            options.block_query_powers = false;
        }
        "combined" => {
            options.query_permutation = true;
            options.unroll_powers = true;
            options.block_query_powers = true;
        }
        _ => panic!("SPARK_GUEST_VARIANT must be control, query_permutation, or combined"),
    }
    let directory = std::env::var("SPARK_GUEST_FIXTURE_DIR").ok();
    let external = directory
        .as_ref()
        .map(|path| SparkGuestFixture::from_directory(std::path::Path::new(path)).unwrap());
    let fixture = external
        .as_ref()
        .unwrap_or_else(|| SparkGuestFixture::embedded().unwrap());
    let compile_start = Instant::now();
    let compiled = fixture.compile(&options).unwrap();
    let compile_elapsed = compile_start.elapsed();
    let preparation_start = Instant::now();
    let bytecode = &compiled.bytecode;
    let public_input = fixture.public_input().unwrap();
    let words = fixture.compact_words(&options).unwrap();
    let witness = fixture.execution_witness(bytecode, &words, &options).unwrap();
    let preparation_elapsed = preparation_start.elapsed();
    let config = default_whir_config(FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE);
    let checked = prove_execution(bytecode, &public_input, &witness, &config, false).unwrap();
    verify_execution(bytecode, &public_input, checked.proof.clone()).unwrap();
    eprintln!(
        "{}",
        json!({
            "benchmark": "spark_generic_verifier",
            "variant": variant,
            "fixture_directory": directory,
            "workload": "One fixed authenticated inner proof; repeated outer proofs use the same program and statement.",
            "effective_threads": system_info::num_threads(),
            "input_bytes": words.len() * 4,
            "compilation_ms": compile_elapsed.as_secs_f64() * 1000.0,
            "input_and_witness_preparation_ms": preparation_elapsed.as_secs_f64() * 1000.0,
            "bytecode_hash": bytecode.hash().iter().map(|value| value.as_canonical_u32()).collect::<Vec<_>>(),
            "instructions": bytecode.unpadded_size(),
            "proof_bytes": postcard::to_allocvec(&checked.proof).unwrap().len(),
            "native_verification": "passed",
        })
    );

    let mut proving = c.benchmark_group("spark_generic_verifier_proving");
    proving
        .sample_size(10)
        .warm_up_time(Duration::from_secs(10))
        .measurement_time(Duration::from_secs(180))
        .sampling_mode(SamplingMode::Flat);
    proving.bench_function(&variant, |b| {
        b.iter_batched(
            || (),
            |_| {
                black_box(
                    prove_execution(
                        black_box(bytecode),
                        black_box(&public_input),
                        black_box(&witness),
                        black_box(&config),
                        false,
                    )
                    .unwrap(),
                )
            },
            BatchSize::PerIteration,
        )
    });
    proving.finish();

    let mut serialization = c.benchmark_group("spark_generic_verifier_serialization");
    serialization
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10));
    serialization.bench_function(&variant, |b| {
        b.iter_batched(
            || (),
            |_| black_box(postcard::to_allocvec(black_box(&checked.proof)).unwrap()),
            BatchSize::PerIteration,
        )
    });
    serialization.finish();

    let mut verification = c.benchmark_group("spark_generic_verifier_native_verification");
    verification
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10));
    verification.bench_function(&variant, |b| {
        b.iter_batched(
            || checked.proof.clone(),
            |proof| black_box(verify_execution(black_box(bytecode), black_box(&public_input), proof).unwrap()),
            BatchSize::PerIteration,
        )
    });
    verification.finish();
}

fn main() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let mut criterion = Criterion::default().configure_from_args();
            bench(&mut criterion);
            criterion.final_summary();
        })
        .unwrap()
        .join()
        .unwrap();
}
