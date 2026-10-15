# Spartan-WHIR verifier guest

#### Scope

This crate implements two fixed Spartan-WHIR verifier guests and the LeanVM programs that lift and aggregate their execution proofs:

- the M1 `spartan-whir-poseidon2-quintic-no-zk-direct-control-v1` correctness profile;
- the M3 `spartan-whir-poseidon1-quintic-full-zk-spark-leanvm-v1` production profile.

Both guests expose an eight-element statement digest as the LeanVM public input. Their proof decoders, verifying data, hash profiles, privacy modes, and matrix-closing modes are separate entrypoints.

An execution proof produced directly from either verifier guest proves one Spartan-WHIR verification. The lift program recursively verifies that execution proof and commits to its application digest and fixed guest-bytecode claim. The binary node recursively verifies two lifted proofs and computes an ordered Poseidon1 application root. The binary node is currently specialized to two lifted proofs of one fixed guest; it is not a same-type node for an arbitrary-depth tree.

The guest verifies the Spartan outer and inner sumchecks, evaluates the fixed DirectSparse matrices, binds the witness evaluation claim, and verifies the Poseidon2 WHIR opening and pruned Merkle proof. Poseidon2 width-16 and width-24 permutations use ordinary LeanVM base-field instructions. Quintic extension arithmetic uses LeanVM's extension-operation precompile. The guest does not call the Poseidon1 precompile.

The control is a fixed no-ZK correctness profile. It has a fixed seven-bit query domain and its recorded transcript reaches 14 distinct queries after 14 draws without taking KoalaBear's rejection branch.

The production guest verifies a full-ZK proof for the 2,048-byte SHA-256 application under the selected Poseidon1 and SPARK profile. It replays the masked outer and inner Spartan sumchecks, SPARK products, authenticated fixed and read-table WHIR openings, branch transcript tags and seals, the hiding-WHIR relation reductions, all 117 logical mask relations represented by seven physical mask columns, the reveal commitment, and the source and mask base-case openings. Raw width-16 Poseidon1 permutations use LeanVM's existing `poseidon16` precompile.

#### Inputs and fixed data

The private input is `testdata/control_guest_input.words`, encoded as 498 canonical little-endian `u32` field words. The host requires exactly 1,992 bytes and rejects non-canonical words. The guest checks every fixed tag and length in the control schema and consumes the entire fixed array.

The zkDSL compiler embeds the control R1CS matrices, Poseidon2 constants, Spartan and WHIR domain separators, and folded-domain generator from `testdata/control_guest_constants.json`. `testdata/control_statement.json` supplies the statement-digest preimage and expected public input. These files originate from the deterministic M0 exporter in the sibling `spartan-whir` checkout. The copied fixture manifest records artifact hashes, and the tests check the guest input, constants, statement, and Rust transcript trace against that manifest.

The production input is `testdata/full_zk_spark_poseidon1/full_zk_spark_guest_input.words`. Its canonical encoding occupies 527,387 words and is zero-padded to the fixed 1,048,576-word witness, or 4,194,304 bytes. The versioned header fixes Poseidon1, the quintic extension, and SPARK. The host rejects non-canonical words; the guest checks tags, lengths and the proof profile. Padding lies outside the canonical input consumed by the guest. Fixed verifier data comes from `full_zk_spark_guest_constants.json`.

`full_zk_spark_manifest.json` records the proof shape, transcript size, and artifact hashes.

#### Optimized SPARK guest

`SparkGuestOptimizations::recommended()` selects the measured verifier changes and compact input. Compile it with `compile_full_zk_spark_poseidon1_guest_with_optimizations` and prepare its witness with `compact_full_zk_spark_words`. The CLI accepts `recommended` after its mode:

```bash
RAYON_NUM_THREADS=12 cargo run --release -p spartan_whir_guest \
  --bin leanvm-full-zk-spark-poseidon1 -- execute recommended
RAYON_NUM_THREADS=12 cargo run --release -p spartan_whir_guest \
  --bin leanvm-full-zk-spark-poseidon1 -- validate recommended
```

The selected `same_height` and `all_free_basis` fixture occupies 477,059 compact words (1,908,236 bytes), including the instance and header. Verification takes 15,794,726 cycles and 19,035,621 memory cells. The padded memory table is `2^25`; execution, extension and Poseidon tables are `2^24`, `2^20` and `2^17`. The ordinary and recommended guests have separate compiled identities and matching lift/node profiles. Use `leanvm-binary-node prove-optimized` to prove and verify the recommended guest, its lift, and a binary node.

The compact input omits fresh hiding rows, initial SPARK zeros and repeated tails, row lengths, and derived SPARK fields. Existing equations assign omitted values, and both carried and fresh Merkle roots remain checked. Query-bit reuse and shared Merkle traversal reduce ordinary instructions. Structured row folding reduces extension operations. The recommended query sampler validates a sorted permutation of transcript draws and preserves their rejection, deduplication, stopping, and transcript semantics. Bounded power-table unrolling and blocks of eight query-power updates reduce loop overhead. These guest changes use the existing VM constraints; the selected native mask packing is a separate configuration change.

Run `SPARK_GUEST_VARIANT=combined cargo bench -p spartan_whir_guest --bench spark_generic_verifier` for complete execution-proof generation, serialization, and native verification. `SPARK_GUEST_VARIANT=control` disables the three generic guest optimizations; `SPARK_GUEST_FIXTURE_DIR` selects an external fixture. The CLI selection `control` applies the same options. Benchmark output is local; record the latest relevant result in this README.

#### Fresh-mask batching and fixture selection

`SparkGuestFixture::from_directory` loads the canonical input, named word layout, fixed verifier constants, and public statement from an exported fixture directory. The compiler derives offsets and hiding mask-group order from the layout and exported configuration. Hiding schedules support one or more code switches, variable folding factors and final source dimensions, and up to four OOD samples per round; plain WHIR also supports up to four initial OOD samples. The reveal commitment pads an odd digest layer with zero digests, matching the native Merkle implementation. Context and relation separators are consumed at their exported lengths. The `extension_arithmetic` option uses existing quintic extension instructions for addition, subtraction and scaling. The `transcript_blocks` option absorbs slices by complete Poseidon rate blocks and samples each quintic challenge in one operation while preserving every duplex boundary. Both options default to false, including in `recommended()`; the diagnostic binary accepts them by name. Each exported WHIR query count is checked against the requested count capped by its folded domain, including the separate fixed-audit configuration. Direct guest Merkle boundaries are derived from the checked fixed-profile input. Compact input lengths are computed from the fields retained by the selected options.

The `separate` configuration uses one fresh root and one query set per carried mask group. The `same_height` configuration groups masks by domain size in first-occurrence order. For the selected packed profile, groups 0 and 3 share a two-column fresh tree, groups 1 and 5 share another two-column tree, and groups 2, 4, and 6 share a three-column tree. Each tree uses 88 distinct queries. Logical mask coefficients and covectors are flattened in chronological order; the application free basis represents each cubic inner mask by its two free coefficients. Every carried root is authenticated separately. Fresh roots and the fresh-side claim are observed before the blinding challenge, and the blinded reveal digest is observed before query sampling. Version 2 framing carries separate vectors for carried and grouped fresh openings; version 1 carries one pair per group.

Pass a fixture directory after the optimization selection to compile, execute, validate, or prove that fixture. The binary-node CLI accepts the fixture directory after its mode:

```bash
RAYON_NUM_THREADS=12 cargo run --release -p spartan_whir_guest \
  --bin leanvm-full-zk-spark-poseidon1 -- execute recommended /path/to/fixture
RAYON_NUM_THREADS=12 cargo run --release -p spartan_whir_guest \
  --bin leanvm-full-zk-spark-poseidon1 -- prove recommended /path/to/fixture
cargo run --release -p spartan_whir_guest \
  --bin leanvm-binary-node -- compile-optimized /path/to/fixture
```

Each compiled fixture has its own guest identity and corresponding lift and binary-node identities. The application must select the expected compiled verifier and statement digest. The embedded fixture selects `same_height` and `all_free_basis`.

#### Commands

Run the control verifier and its rejection cases:

```bash
cargo test --release -p spartan_whir_guest --test control_guest
```

Emit machine-readable compiler, execution, and direct execution-proof measurements:

```bash
cargo run --release -p spartan_whir_guest --bin leanvm-m1-control -- compile
cargo run --release -p spartan_whir_guest --bin leanvm-m1-control -- execute
cargo run --release -p spartan_whir_guest --bin leanvm-m1-control -- prove
```

The `prove` mode generates a LeanVM execution proof and verifies it with LeanVM's native verifier before reporting success.

Run the selected production guest and its 17 rejection cases:

```bash
cargo test --release -p spartan_whir_guest --test full_zk_spark_poseidon1
```

Emit production compiler, execution, and verified direct execution-proof measurements:

```bash
cargo run --release -p spartan_whir_guest --bin leanvm-full-zk-spark-poseidon1 -- compile
cargo run --release -p spartan_whir_guest --bin leanvm-full-zk-spark-poseidon1 -- execute
cargo run --release -p spartan_whir_guest --bin leanvm-full-zk-spark-poseidon1 -- prove
```

Compile the production lift and binary-node programs, run the small control proof chain, or run the complete production proof chain:

```bash
cargo run --release -p spartan_whir_guest --bin leanvm-binary-node -- compile-production
cargo run --release -p spartan_whir_guest --bin leanvm-binary-node -- smoke-control
RAYON_NUM_THREADS=12 cargo run --release -p spartan_whir_guest --bin leanvm-binary-node -- prove-production
```

The production command proves the Spartan verifier guest before the lift and node. The refreshed recommended chain used 17,800,314,880 bytes of peak resident memory in one release correctness run.

#### Terminal fixture generation

The recursive GKR verifier constrains an inverse for each top-level denominator before computing its quotient. Zero denominators are rejected even when the prover supplies the quotient and inverse as witness values. Native Rust and the Python reference verifier reject the same case.

WHIR continuation rounds keep the carried sumcheck claim at coefficient one and assign the new OOD and query claims coefficients `gamma, gamma^2, ...`. Native proving, recursive verification, reference Python verification, and terminal verification use these coefficients in both the claimed sum and final weight evaluation. The client plain-WHIR verifier guest follows the same rule. Explicit LeanVM profiles use domain tag `0x57500002`; earlier client and LeanVM proof artifacts require regeneration after the corresponding protocol corrections.

Generate two distinct Privacy Pools client fixtures and record their current sources, including the patched WHIR dependency, with:

```bash
RAYON_NUM_THREADS=12 RUSTFLAGS='-C target-cpu=native -C debuginfo=0' \
python3 script/run_client_fixtures.py ../spartan-whir /path/to/client-setup.json \
  benchmark-results/client-current --cargo-offline
```

The client runner fixes same-height fresh-mask batching and AllFreeBasis mask packing, builds the locked client exporter, and generates samples zero and one. Its output directory must be new. Each client proof is natively verified by the exporter; each exported artifact is checked against its manifest.

Generate a complete terminal fixture from two distinct exported client statements with:

```bash
RAYON_NUM_THREADS=12 RUSTFLAGS='-C target-cpu=native -C debuginfo=0' \
python3 script/run_terminal_fixture.py \
  /path/to/left-client-fixture /path/to/right-client-fixture \
  benchmark-results/terminal-current /path/to/profiles.json \
  --cargo-offline
```

Run this command from the LeanVM repository root. The output directory must be new. The runner checks client artifact hashes, builds the current locked Rust sources, generates and verifies both direct proofs, both lifts and the terminal root, and runs guest and terminal mutation checks. It records the LeanVM upstream base and branch HEAD, source fingerprints, compiler identity, executable fingerprint, profile inputs, proof digest and compiled program digests. If the client directories share a parent containing `client-source-provenance.json`, it also checks the recorded client generation sources and manifests. Source and input fingerprints must remain unchanged throughout generation.

The output contains `report.json`, `proving.log`, `source-provenance.json` and `native/root-fixture.json` with its proof and program files. The Solidity fixture generator requires this provenance when generating a terminal contract. Use its `--validate-only --require-current-source` options to check an exported fixture against the current sources before regeneration.

Poseidon grinding performs one fresh duplex after each successful positive work check. The native prover and verifier, recursive verifier and Python reference use the same transition, so subsequent folding challenges and query indices use fresh output. Zero-bit checks remain no-ops. The selected terminal uses Keccak and retains its existing work-word consumption. Regenerate the recursive programs and their proofs after transcript changes; these unpublished artifacts use the existing protocol versions.

The profiles JSON selects the direct, lift and node WHIR schedules independently. `profiles/terminal_grouped.json` supplies the selected Privacy Pools configuration: all three backend parameters are 100, with direct/lift/root grinding budgets of 22/24/28 bits. `terminal_grouped_logup` selects grouped LogUp with execution, fixed-program and helper commitments. `profiles/terminal_c1.json` retains the two-commitment C1 alternative with the same WHIR schedules. `security_bits` is the WHIR component target; a complete-chain security claim requires the corresponding composition analysis. `terminal_num_variables` optionally sets the C1 fixed-program polynomial dimension. Larger dimensions append zeros to the three concatenated programs and prepend zero coordinates to their authenticated evaluation points. The chosen dimension must match the actual root execution polynomial; a mismatch rejects. Omitting it retains the minimum dimension containing the programs.

`leanvm-recursion-profile` accepts backend targets of at least 100 bits within the supported profile range. Its `LEANVM_PROVING_TIMEOUT_SECONDS` setting defaults to 60 seconds per proving operation; zero disables the deadline. The fixture runner defaults to zero and records its selected deadline. Diagnostic proving times exclude compilation and input preparation.

Regenerate the production fixture from the sibling Spartan-WHIR checkout with explicit fresh-mask batching and mask packing:

```bash
cd ../spartan-whir
RAYON_NUM_THREADS=1 \
SPARK_FRESH_MASK_BATCHING=same_height \
SPARK_MASK_PACKING=all_free_basis \
SHA256_BENCH_WORKDIR=target/sha256-optimized-cache \
cargo run --release --features poseidon1 --bin leanvm-full-zk-spark-fixture -- \
  ../leanVM/crates/spartan_whir_guest/testdata/full_zk_spark_poseidon1
```

#### M1 direct execution-proof measurement

A single release correctness run on 2026-09-08 used an Apple M4 Pro with 12 effective threads and 48 GB RAM. Timings are diagnostic elapsed wall-clock measurements. Peak resident memory is the process high-water mark.

| Metric | Result |
| --- | ---: |
| Private input | 1,992 bytes |
| Compiled instructions | 31,634 |
| Padded instructions | 32,768 (`2^15`) |
| Encoded bytecode | 2,097,152 bytes |
| Bytecode hash | `[1149119812, 1179494583, 1833541235, 1131995724, 1046226380, 2126602932, 1884057627, 1560757135]` |
| Compilation | 188.41 ms, 86,245,376-byte peak RSS |
| Execution | 492,816 cycles, 145,424,384-byte peak RSS |
| Memory | 492,329 cells, padded to 524,288 |
| Direct proof generation | 550.04 ms |
| Direct proof verification | 25.72 ms |
| Serialized direct-proof payload | 311,352 bytes |
| Complete proof command peak RSS | 956,694,528 bytes |

The complete proof and native verification passed. The control suite checks its copied manifest, transcript primitives, execution, and all nine mutation cases. Re-run the commands after changes to the compiler, guest, fixed constants, or LeanVM proving system.

#### M3 execution measurements

The selected production profile uses a 121-bit outer LeanVM target, `log_inv_rate = 1`, first folding factor 9, subsequent folding factor 5, and initial Reed-Solomon domain reduction factor 5. The ordinary guest was compiled and executed on 2026-09-08 on the same Apple M4 Pro:

| Metric | Result |
| --- | ---: |
| Private input | 527,683 canonical words; 1,048,576 padded words; 4,194,304 bytes |
| Compiled instructions | 342,948 |
| Padded instructions | 524,288 (`2^19`) |
| Encoded bytecode | 33,554,432 bytes |
| Bytecode hash | `[1534503473, 1407084828, 1333006516, 825060992, 99491416, 196542472, 1516752633, 1481584606]` |
| Execution | 31,396,643 cycles |
| Memory | 34,342,869 cells, padded to 67,108,864 |
| Execution table | 31,396,643 rows, padded to 33,554,432 (`2^25`) |
| Extension-operation table | 728,944 rows, padded to 1,048,576 (`2^20`) |
| Poseidon1 table | 71,675 rows, padded to 131,072 (`2^17`) |

The ordinary fixture, all 17 mutation checks, and a complete execution proof with native verification passed. Its one-run execution proof occupied 719,245 bytes. The recommended guest also passed all 17 mutations and the complete recursive chain below. Existing API and JSON names containing `RootProofResult` or `root_proof` refer to the direct guest execution proof.

#### Lift and binary node

The lift program fixes the Spartan verifier guest's Fiat-Shamir domain separator in its bytecode, verifies one direct execution proof, reduces the guest-bytecode evaluation to one valid claim, and hashes that claim together with the application digest into its public input. The binary node fixes the lift program's domain separator, verifies two lifted proofs, reduces their bytecode evaluations to one valid claim, and hashes an ordered pair of application digests under the `NOD1` domain into its public input.

The recommended production programs compile to these fixed sizes:

| Program | Instructions | Padded instructions | Encoded bytecode |
| --- | ---: | ---: | ---: |
| Spartan verifier guest | 334,313 | 524,288 (`2^19`) | 33,554,432 bytes |
| Lifted execution verifier | 171,074 | 262,144 (`2^18`) | 16,777,216 bytes |
| Two-child binary node | 171,356 | 262,144 (`2^18`) | 16,777,216 bytes |

A 12-thread correctness run on 2026-09-08 supplied the same valid lifted proof in both ordered child slots. The recommended guest proof occupied 731,388 bytes, the lift 448,325 bytes, and the binary node 610,714 bytes. Native verification passed at every layer and changed application claims were rejected.

The recursive verifier supports the production proof's 64-chunk base-field Merkle leaves and first folding factor 9. The tests compile the ordinary and recommended guest, lift, and node programs and check their supported size limits.

#### Security accounting

The inner Spartan-WHIR proof uses a 116-bit Johnson-bound configuration. The outer LeanVM proof uses a 121-bit Johnson-bound configuration. Applying a union bound gives failure probability at most `2^-116 + 2^-121`, or about 115.956 bits before hash assumptions. The fixed guest recomputes the application digest from all 256 SHA-256 statement bits and exposes only that eight-element digest as the LeanVM public input.

#### Acceptance tests

The M1 release suite checks successful execution, successful LeanVM execution-proof generation and verification, and rejection after changing the public input, witness commitment, outer sumcheck, outer claim, inner sumcheck, witness evaluation, WHIR opening, encoding version, or final input length.

The M3 suite checks the fixture hashes, successful production execution, and rejection after changing the application public input, application mask commitment, SPARK product sumcheck, fixed opening, read opening, masked relation claim, relation sumcheck, code-switch commitment, code-switch opening, mask reveal, mask opening, source opening, version tag, hash-profile tag, matrix-closing tag, canonical length, or trailing input. The Rust Poseidon1 profile suite separately rejects changes to authenticated fixed and read commitments and checks raw permutation, challenger, leaf-hash, and node-compression parity.

#### Exported withdrawal fixtures

`SparkGuestFixture::from_directory` accepts the exported Privacy Pools withdrawal relation and its supported WHIR geometry. `with_fixed_sibling_storage` reserves the maximum pruned binary Merkle frontier for each configured opening, giving distinct proof samples identical layout offsets and compiled bytecode. The actual sibling counts remain verified; padding does not enter the Fiat–Shamir transcript.

`leanvm-recursion-profile LEFT_FIXTURE RIGHT_FIXTURE OUTPUT_JSON [PROFILES_JSON]` measures two distinct application proofs, their lifts, and a binary root, with native verification at every layer. Its JSON profiles select direct, lift, and node WHIR parameters, the three recursive algebra options, and optional `node_child_num_variables`. The driver requires backend targets of at least 100 bits. Its per-operation timeout defaults to 60 seconds and can be disabled with `LEANVM_PROVING_TIMEOUT_SECONDS=0`; the fixture runner disables it by default. `LEANVM_VALIDATE_MUTATIONS=1` enables the exported mutation suite; `LEANVM_VM_PROFILE=1` records function profiles.

The `withdrawal_recursion` Criterion target takes `LEANVM_WITHDRAWAL_FIXTURES` as a JSON list of absolute fixture directories and `LEANVM_RECURSION_CASES` as an absolute JSON case-file path. Each case contains a name and the same profiles/options as the diagnostic driver. It validates distinct statements and a complete proof chain before timing, then rotates the corpus and binary-child order. Compilation, input preparation, and validation are outside the samples.
