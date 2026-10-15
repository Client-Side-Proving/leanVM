use criterion::{BatchSize, Criterion, SamplingMode};
use spartan_whir_guest::{
    SparkGuestOptimizations, compact_full_zk_spark_words, compile_full_zk_spark_poseidon1_guest_with_optimizations,
    full_zk_spark_poseidon1_public_input, full_zk_spark_poseidon1_words, prove_full_zk_spark_poseidon1_guest,
};
use std::{hint::black_box, time::Duration};

fn bench(c: &mut Criterion) {
    let public_input = full_zk_spark_poseidon1_public_input().unwrap();
    let original = full_zk_spark_poseidon1_words().unwrap();
    let options = SparkGuestOptimizations::recommended();
    // Warm the embedded layout cache before measuring repeated client encoding.
    let _ = compact_full_zk_spark_words(&original, &options).unwrap();
    let mut encoding = c.benchmark_group("spark_guest_input_encoding");
    encoding
        .sample_size(50)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10));
    encoding.bench_function("optimized", |b| {
        b.iter_batched(
            || (),
            |_| black_box(compact_full_zk_spark_words(black_box(&original), black_box(&options)).unwrap()),
            BatchSize::PerIteration,
        )
    });
    encoding.finish();
    let mut group = c.benchmark_group("spark_guest_execution_proof");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(10))
        .measurement_time(Duration::from_secs(180))
        .sampling_mode(SamplingMode::Flat);
    for (name, options) in [
        ("baseline", SparkGuestOptimizations::default()),
        ("optimized", SparkGuestOptimizations::recommended()),
    ] {
        let compiled = compile_full_zk_spark_poseidon1_guest_with_optimizations(&options).unwrap();
        let words = if options.uses_compact_input() {
            compact_full_zk_spark_words(&original, &options).unwrap()
        } else {
            original.clone()
        };
        let check = prove_full_zk_spark_poseidon1_guest(&compiled.bytecode, &public_input, &words).unwrap();
        eprintln!("verified {name}: {} bytes", check.serialized_proof_bytes);
        group.bench_function(name, |b| {
            b.iter_batched(
                || (),
                |_| {
                    black_box(
                        prove_full_zk_spark_poseidon1_guest(
                            black_box(&compiled.bytecode),
                            black_box(&public_input),
                            black_box(&words),
                        )
                        .unwrap(),
                    )
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
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
