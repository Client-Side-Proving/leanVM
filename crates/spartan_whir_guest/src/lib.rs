mod direct_layout;
mod query_config;
mod spark_fixture;
mod spark_fixture_normalize;
pub use spark_fixture::SparkGuestFixture;

use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::time::{Duration, Instant};

use backend::integers::QuotientMap;
use backend::{ArenaVec, PrimeCharacteristicRing, arena_vec};
use include_dir::{Dir, include_dir};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_prover::{default_whir_config, get_execution_trace, verify_execution::verify_execution};
use lean_vm::{
    Bytecode, ExecutionMetadata, ExecutionWitness, F, Hints, PUBLIC_INPUT_LEN, TableT, try_execute_bytecode,
};
use serde::Deserialize;
use serde_json::Value;

pub const CONTROL_GUEST_WORDS: usize = CONTROL_WORD_BYTES.len() / 4;
pub const CONTROL_GUEST_INPUT_BYTES: usize = CONTROL_GUEST_WORDS * 4;
pub const CONTROL_ROOT_LOG_INV_RATE: usize = 2;
pub const PREAMBLE_MEMORY_LEN: usize = 21;
pub const POSEIDON1_PRIMITIVE_WORDS: usize = 91;
pub const POSEIDON1_PRIMITIVE_PREAMBLE_MEMORY_LEN: usize = PUBLIC_INPUT_LEN;
pub const FULL_ZK_DIRECT_POSEIDON1_WORDS: usize = FULL_ZK_DIRECT_POSEIDON1_WORD_BYTES.len() / 4;
pub const FULL_ZK_DIRECT_POSEIDON1_INPUT_BYTES: usize = FULL_ZK_DIRECT_POSEIDON1_WORDS * 4;
pub const FULL_ZK_DIRECT_POSEIDON1_PREAMBLE_MEMORY_LEN: usize = PREAMBLE_MEMORY_LEN;
pub const FULL_ZK_DIRECT_POSEIDON1_ROOT_LOG_INV_RATE: usize = 2;
pub const FULL_ZK_DIRECT_POSEIDON2_WORDS: usize = FULL_ZK_DIRECT_POSEIDON2_WORD_BYTES.len() / 4;
pub const FULL_ZK_DIRECT_POSEIDON2_INPUT_BYTES: usize = FULL_ZK_DIRECT_POSEIDON2_WORDS * 4;
pub const FULL_ZK_DIRECT_POSEIDON2_PREAMBLE_MEMORY_LEN: usize = PREAMBLE_MEMORY_LEN;
pub const FULL_ZK_DIRECT_POSEIDON2_ROOT_LOG_INV_RATE: usize = 2;
pub const FULL_ZK_SPARK_POSEIDON1_WORDS: usize = 1_048_576;
pub const FULL_ZK_SPARK_POSEIDON1_INPUT_BYTES: usize = FULL_ZK_SPARK_POSEIDON1_WORDS * 4;
pub const FULL_ZK_SPARK_POSEIDON1_PREAMBLE_MEMORY_LEN: usize = 29;
pub const FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE: usize = 1;

const CONTROL_WORD_BYTES: &[u8] = include_bytes!("../testdata/control_guest_input.words");
const CONTROL_STATEMENT_JSON: &str = include_str!("../testdata/control_statement.json");
const CONTROL_CONSTANTS_JSON: &str = include_str!("../testdata/control_guest_constants.json");
const FULL_ZK_DIRECT_POSEIDON1_WORD_BYTES: &[u8] =
    include_bytes!("../testdata/full_zk_direct_poseidon1/full_zk_direct_guest_input.words");
const FULL_ZK_DIRECT_POSEIDON1_STATEMENT_JSON: &str =
    include_str!("../testdata/full_zk_direct_poseidon1/full_zk_direct_statement.json");
const FULL_ZK_DIRECT_POSEIDON1_CONSTANTS_JSON: &str =
    include_str!("../testdata/full_zk_direct_poseidon1/full_zk_direct_guest_constants.json");
const FULL_ZK_DIRECT_POSEIDON2_WORD_BYTES: &[u8] =
    include_bytes!("../testdata/full_zk_direct_poseidon2/full_zk_direct_guest_input.words");
const FULL_ZK_DIRECT_POSEIDON2_STATEMENT_JSON: &str =
    include_str!("../testdata/full_zk_direct_poseidon2/full_zk_direct_statement.json");
const FULL_ZK_DIRECT_POSEIDON2_CONSTANTS_JSON: &str =
    include_str!("../testdata/full_zk_direct_poseidon2/full_zk_direct_guest_constants.json");
const FULL_ZK_SPARK_POSEIDON1_WORD_BYTES: &[u8] =
    include_bytes!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_input.words");
const FULL_ZK_SPARK_POSEIDON1_STATEMENT_JSON: &str =
    include_str!("../testdata/full_zk_spark_poseidon1/full_zk_spark_statement.json");
const FULL_ZK_SPARK_POSEIDON1_CONSTANTS_JSON: &str =
    include_str!("../testdata/full_zk_spark_poseidon1/full_zk_spark_guest_constants.json");
static EMBEDDED_ZKDSL: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

#[derive(Debug)]
pub enum GuestError {
    InvalidWordBytes { trailing: usize },
    InvalidWordCount { expected: usize, actual: usize },
    NonCanonicalWord { index: usize, value: u32 },
    Fixture(String),
    Vm(String),
    Proof(String),
}

impl Display for GuestError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidWordBytes { trailing } => {
                write!(formatter, "control input has {trailing} trailing bytes")
            }
            Self::InvalidWordCount { expected, actual } => {
                write!(formatter, "expected {expected} control words, got {actual}")
            }
            Self::NonCanonicalWord { index, value } => {
                write!(formatter, "control word {index} is not canonical: {value}")
            }
            Self::Fixture(error) => write!(formatter, "invalid control fixture: {error}"),
            Self::Vm(error) => write!(formatter, "LeanVM execution failed: {error}"),
            Self::Proof(error) => write!(formatter, "LeanVM proof failed: {error}"),
        }
    }
}

impl std::error::Error for GuestError {}

#[derive(Debug, Deserialize)]
struct Statement {
    digest: Vec<u32>,
    digest_preimage: Vec<u32>,
}

#[derive(Debug)]
pub struct CompileResult {
    pub bytecode: Bytecode,
    pub elapsed: Duration,
}

#[derive(Debug)]
pub struct RootProofResult {
    pub proof: ExecutionProof,
    pub proving_elapsed: Duration,
    pub verification_elapsed: Duration,
    pub serialized_proof_bytes: usize,
}

#[derive(Debug)]
pub struct TableMetrics {
    pub name: &'static str,
    pub non_padded_rows: usize,
    pub log_n_rows: usize,
    pub padded_rows: usize,
}

#[derive(Debug)]
pub struct ExecutionReport {
    pub metadata: ExecutionMetadata,
    pub padded_memory_cells: usize,
    pub tables: Vec<TableMetrics>,
}

pub fn control_words() -> Result<Vec<u32>, GuestError> {
    decode_word_bytes(CONTROL_WORD_BYTES)
}

pub fn full_zk_direct_poseidon1_words() -> Result<Vec<u32>, GuestError> {
    decode_word_bytes(FULL_ZK_DIRECT_POSEIDON1_WORD_BYTES)
}

pub fn full_zk_direct_poseidon2_words() -> Result<Vec<u32>, GuestError> {
    decode_word_bytes(FULL_ZK_DIRECT_POSEIDON2_WORD_BYTES)
}

pub fn full_zk_spark_poseidon1_words() -> Result<Vec<u32>, GuestError> {
    decode_word_bytes(FULL_ZK_SPARK_POSEIDON1_WORD_BYTES)
}

pub fn poseidon1_primitive_words() -> Vec<u32> {
    let mut words = (0..23).map(|index| (index * index + 17) as u32).collect::<Vec<_>>();
    words.extend([
        454_253_751,
        1_906_113_756,
        377_596_994,
        792_299_923,
        2_053_520_120,
        1_687_138_493,
        1_335_122_479,
        1_913_328_900,
        336_914_164,
        269_792_076,
        241_800_815,
        850_435_158,
    ]);
    words.extend(1..=24);
    words.extend([
        521_167_832,
        1_294_533_855,
        1_414_095_283,
        607_223_733,
        1_119_062_695,
        178_801_552,
        1_289_018_264,
        713_205_468,
    ]);
    words.extend(100..108);
    words.extend(200..208);
    words.extend([
        1_447_100_179,
        963_179_731,
        1_376_818_832,
        157_084_832,
        1_605_343_738,
        1_715_972_436,
        1_200_644_159,
        263_182_536,
    ]);
    debug_assert_eq!(words.len(), POSEIDON1_PRIMITIVE_WORDS);
    words
}

pub fn decode_word_bytes(bytes: &[u8]) -> Result<Vec<u32>, GuestError> {
    if !bytes.len().is_multiple_of(4) {
        return Err(GuestError::InvalidWordBytes {
            trailing: bytes.len() % 4,
        });
    }
    Ok(bytes
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("four-byte chunk")))
        .collect())
}

pub fn control_public_input() -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
    let statement: Statement =
        serde_json::from_str(CONTROL_STATEMENT_JSON).map_err(|error| GuestError::Fixture(error.to_string()))?;
    if statement.digest.len() != PUBLIC_INPUT_LEN {
        return Err(GuestError::Fixture(format!(
            "expected {PUBLIC_INPUT_LEN} digest words, got {}",
            statement.digest.len()
        )));
    }
    let mut digest = [F::ZERO; PUBLIC_INPUT_LEN];
    for (index, (&word, output)) in statement.digest.iter().zip(&mut digest).enumerate() {
        *output = F::from_canonical_checked(word).ok_or(GuestError::NonCanonicalWord { index, value: word })?;
    }
    Ok(digest)
}

pub fn full_zk_direct_poseidon1_public_input() -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
    public_input_from_statement(FULL_ZK_DIRECT_POSEIDON1_STATEMENT_JSON)
}

pub fn full_zk_direct_poseidon2_public_input() -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
    public_input_from_statement(FULL_ZK_DIRECT_POSEIDON2_STATEMENT_JSON)
}

pub fn full_zk_spark_poseidon1_public_input() -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
    public_input_from_statement(FULL_ZK_SPARK_POSEIDON1_STATEMENT_JSON)
}

fn public_input_from_statement(json: &str) -> Result<[F; PUBLIC_INPUT_LEN], GuestError> {
    let statement: Statement = serde_json::from_str(json).map_err(|error| GuestError::Fixture(error.to_string()))?;
    if statement.digest.len() != PUBLIC_INPUT_LEN {
        return Err(GuestError::Fixture(format!(
            "expected {PUBLIC_INPUT_LEN} digest words, got {}",
            statement.digest.len()
        )));
    }
    let mut digest = [F::ZERO; PUBLIC_INPUT_LEN];
    for (index, (&word, output)) in statement.digest.iter().zip(&mut digest).enumerate() {
        *output = F::from_canonical_checked(word).ok_or(GuestError::NonCanonicalWord { index, value: word })?;
    }
    Ok(digest)
}

pub fn compile_control_guest() -> Result<CompileResult, GuestError> {
    let constants: Value =
        serde_json::from_str(CONTROL_CONSTANTS_JSON).map_err(|error| GuestError::Fixture(error.to_string()))?;
    let statement: Statement =
        serde_json::from_str(CONTROL_STATEMENT_JSON).map_err(|error| GuestError::Fixture(error.to_string()))?;
    let mut replacements = BTreeMap::new();
    // The fixed query geometry is unchanged, but transcript-derived positions
    // determine the number of siblings and the final sumcheck's word offset.
    let words = control_words()?;
    let sibling_count = *words
        .get(163)
        .ok_or_else(|| GuestError::Fixture("control opening is missing its sibling count".to_string()))?
        as usize;
    if sibling_count > 14 * 7 || 164 + sibling_count * 8 + 14 != words.len() {
        return Err(GuestError::Fixture(
            "control Merkle opening has an invalid fixed layout".to_string(),
        ));
    }
    replacements.insert("CONTROL_WORDS_PLACEHOLDER".to_string(), words.len().to_string());
    replacements.insert("WHIR_SIBLING_COUNT_PLACEHOLDER".to_string(), sibling_count.to_string());
    insert_flattened_json(
        &mut replacements,
        "POSEIDON16_EXTERNAL_INITIAL_PLACEHOLDER",
        &constants["poseidon2"]["width_16"]["external_initial"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON16_INTERNAL_PLACEHOLDER",
        &constants["poseidon2"]["width_16"]["internal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON16_EXTERNAL_FINAL_PLACEHOLDER",
        &constants["poseidon2"]["width_16"]["external_final"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON16_INTERNAL_DIAGONAL_PLACEHOLDER",
        &constants["poseidon2"]["width_16"]["internal_diagonal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON24_EXTERNAL_INITIAL_PLACEHOLDER",
        &constants["poseidon2"]["width_24"]["external_initial"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON24_INTERNAL_PLACEHOLDER",
        &constants["poseidon2"]["width_24"]["internal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON24_EXTERNAL_FINAL_PLACEHOLDER",
        &constants["poseidon2"]["width_24"]["external_final"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON24_INTERNAL_DIAGONAL_PLACEHOLDER",
        &constants["poseidon2"]["width_24"]["internal_diagonal"],
    )?;
    insert_json(
        &mut replacements,
        "SPARTAN_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["spartan_domain_separator"],
    )?;
    insert_json(
        &mut replacements,
        "WHIR_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["whir_domain_separator"],
    )?;
    for matrix in ["a", "b", "c"] {
        let entries = constants["canonical_shape"][matrix]["entries"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture(format!("matrix {matrix} entries are not an array")))?;
        for (field, suffix) in [("row", "ROWS"), ("column", "COLUMNS"), ("value", "VALUES")] {
            let values = entries.iter().map(|entry| entry[field].clone()).collect::<Vec<_>>();
            replacements.insert(
                format!("MATRIX_{}_{}_PLACEHOLDER", matrix.to_ascii_uppercase(), suffix),
                serde_json::to_string(&values).map_err(|error| GuestError::Fixture(error.to_string()))?,
            );
        }
    }
    replacements.insert(
        "WHIR_FOLDED_DOMAIN_GENERATOR_PLACEHOLDER".to_string(),
        constants["whir"]["folded_domain_generator"].to_string(),
    );
    let statement_prefix = statement
        .digest_preimage
        .get(..statement.digest_preimage.len().saturating_sub(1))
        .ok_or_else(|| GuestError::Fixture("statement preimage is empty".to_string()))?;
    replacements.insert(
        "STATEMENT_PREFIX_PLACEHOLDER".to_string(),
        serde_json::to_string(statement_prefix).map_err(|error| GuestError::Fixture(error.to_string()))?,
    );

    let source = ProgramSource::Embedded {
        entry: "main.py".to_string(),
        dir: &EMBEDDED_ZKDSL,
    };
    let start = Instant::now();
    replacements
        .entry("OPT_EXTENSION_ARITHMETIC_VALUE".into())
        .or_insert_with(|| "0".into());
    replacements
        .entry("OPT_TRANSCRIPT_BLOCKS_VALUE".into())
        .or_insert_with(|| "0".into());
    let bytecode = compile_program_with_flags(&source, CompilationFlags { replacements });
    Ok(CompileResult {
        bytecode,
        elapsed: start.elapsed(),
    })
}

pub fn compile_full_zk_direct_poseidon1_guest() -> Result<CompileResult, GuestError> {
    let constants: Value = serde_json::from_str(FULL_ZK_DIRECT_POSEIDON1_CONSTANTS_JSON)
        .map_err(|error| GuestError::Fixture(error.to_string()))?;
    if query_config::positions(&constants)? != [18] {
        return Err(GuestError::Fixture("unsupported Direct query positions".to_string()));
    }
    let mut replacements = direct_layout::replacements(&full_zk_direct_poseidon1_words()?)?;
    insert_json(
        &mut replacements,
        "FULL_ZK_CONTEXT_PREFIX_PLACEHOLDER",
        &constants["context_prefix"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_RELATION_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["relation_domain_separator"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_MASK_DOMAIN_GENERATOR_PLACEHOLDER",
        &constants["external_mask_groups"][0]["shape"]["domain_generator"],
    )?;
    replacements.insert(
        "FULL_ZK_SOURCE_DOMAIN_GENERATOR_PLACEHOLDER".to_string(),
        constants["source_code"]["domain_generator"].to_string(),
    );

    for matrix in ["a", "b", "c"] {
        let entries = constants["canonical_shape"][matrix]["entries"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture(format!("matrix {matrix} entries are not an array")))?;
        for (field, suffix) in [("row", "ROWS"), ("column", "COLUMNS"), ("value", "VALUES")] {
            let values = entries.iter().map(|entry| entry[field].clone()).collect::<Vec<_>>();
            replacements.insert(
                format!("FULL_ZK_MATRIX_{}_{}_PLACEHOLDER", matrix.to_ascii_uppercase(), suffix),
                serde_json::to_string(&values).map_err(|error| GuestError::Fixture(error.to_string()))?,
            );
        }
    }

    let source = ProgramSource::Embedded {
        entry: "full_zk_direct_poseidon1.py".to_string(),
        dir: &EMBEDDED_ZKDSL,
    };
    let start = Instant::now();
    replacements
        .entry("OPT_EXTENSION_ARITHMETIC_VALUE".into())
        .or_insert_with(|| "0".into());
    replacements
        .entry("OPT_TRANSCRIPT_BLOCKS_VALUE".into())
        .or_insert_with(|| "0".into());
    let bytecode = compile_program_with_flags(&source, CompilationFlags { replacements });
    Ok(CompileResult {
        bytecode,
        elapsed: start.elapsed(),
    })
}

pub fn compile_full_zk_direct_poseidon2_guest() -> Result<CompileResult, GuestError> {
    let constants: Value = serde_json::from_str(FULL_ZK_DIRECT_POSEIDON2_CONSTANTS_JSON)
        .map_err(|error| GuestError::Fixture(error.to_string()))?;
    if query_config::positions(&constants)? != [18] {
        return Err(GuestError::Fixture("unsupported Direct query positions".to_string()));
    }
    let poseidon_constants: Value =
        serde_json::from_str(CONTROL_CONSTANTS_JSON).map_err(|error| GuestError::Fixture(error.to_string()))?;
    let mut replacements = direct_layout::replacements(&full_zk_direct_poseidon2_words()?)?;
    insert_json(
        &mut replacements,
        "FULL_ZK_CONTEXT_PREFIX_PLACEHOLDER",
        &constants["context_prefix"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_RELATION_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["relation_domain_separator"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_MASK_DOMAIN_GENERATOR_PLACEHOLDER",
        &constants["external_mask_groups"][0]["shape"]["domain_generator"],
    )?;
    replacements.insert(
        "FULL_ZK_SOURCE_DOMAIN_GENERATOR_PLACEHOLDER".to_string(),
        constants["source_code"]["domain_generator"].to_string(),
    );

    for matrix in ["a", "b", "c"] {
        let entries = constants["canonical_shape"][matrix]["entries"]
            .as_array()
            .ok_or_else(|| GuestError::Fixture(format!("matrix {matrix} entries are not an array")))?;
        for (field, suffix) in [("row", "ROWS"), ("column", "COLUMNS"), ("value", "VALUES")] {
            let values = entries.iter().map(|entry| entry[field].clone()).collect::<Vec<_>>();
            replacements.insert(
                format!("FULL_ZK_MATRIX_{}_{}_PLACEHOLDER", matrix.to_ascii_uppercase(), suffix),
                serde_json::to_string(&values).map_err(|error| GuestError::Fixture(error.to_string()))?,
            );
        }
    }

    insert_flattened_json(
        &mut replacements,
        "POSEIDON16_EXTERNAL_INITIAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_16"]["external_initial"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON16_INTERNAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_16"]["internal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON16_EXTERNAL_FINAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_16"]["external_final"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON16_INTERNAL_DIAGONAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_16"]["internal_diagonal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON24_EXTERNAL_INITIAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_24"]["external_initial"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON24_INTERNAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_24"]["internal"],
    )?;
    insert_flattened_json(
        &mut replacements,
        "POSEIDON24_EXTERNAL_FINAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_24"]["external_final"],
    )?;
    insert_json(
        &mut replacements,
        "POSEIDON24_INTERNAL_DIAGONAL_PLACEHOLDER",
        &poseidon_constants["poseidon2"]["width_24"]["internal_diagonal"],
    )?;

    let source = ProgramSource::Embedded {
        entry: "full_zk_direct_poseidon2.py".to_string(),
        dir: &EMBEDDED_ZKDSL,
    };
    let start = Instant::now();
    replacements
        .entry("OPT_EXTENSION_ARITHMETIC_VALUE".into())
        .or_insert_with(|| "0".into());
    replacements
        .entry("OPT_TRANSCRIPT_BLOCKS_VALUE".into())
        .or_insert_with(|| "0".into());
    let bytecode = compile_program_with_flags(&source, CompilationFlags { replacements });
    Ok(CompileResult {
        bytecode,
        elapsed: start.elapsed(),
    })
}

/// Independently selectable verifier experiments. They keep the inner proof and WHIR schedule fixed.
#[derive(Clone, Debug, Default)]
pub struct SparkGuestOptimizations {
    pub fresh_relation: bool,
    pub fresh_rows: bool,
    pub structured_rows: bool,
    pub row_counts: bool,
    pub derived_fields: bool,
    pub query_product: bool,
    pub radix_prefix: bool,
    pub query_permutation: bool,
    pub unroll_powers: bool,
    pub block_query_powers: bool,
    pub horner_cubic: bool,
    pub eq_precompile: bool,
    pub factor_eq_endpoints: bool,
    pub merkle_query_bits: bool,
    pub paired_merkle: bool,
    /// Use extension instructions for addition, subtraction, and base scaling.
    pub extension_arithmetic: bool,
    /// Absorb transcript slices by full rate blocks, preserving duplex boundaries.
    pub transcript_blocks: bool,
}

impl SparkGuestOptimizations {
    /// Measured combination with compact rows and fewer verifier operations.
    pub fn recommended() -> Self {
        Self {
            fresh_relation: true,
            fresh_rows: true,
            structured_rows: true,
            query_product: true,
            radix_prefix: true,
            query_permutation: true,
            unroll_powers: true,
            block_query_powers: true,
            horner_cubic: true,
            eq_precompile: true,
            factor_eq_endpoints: true,
            merkle_query_bits: true,
            paired_merkle: true,
            extension_arithmetic: false,
            transcript_blocks: false,
            row_counts: true,
            derived_fields: true,
        }
    }

    pub fn uses_compact_input(&self) -> bool {
        self.fresh_rows || self.structured_rows || self.row_counts || self.derived_fields
    }
}

pub fn compile_full_zk_spark_poseidon1_guest() -> Result<CompileResult, GuestError> {
    compile_full_zk_spark_poseidon1_guest_with_optimizations(&SparkGuestOptimizations::default())
}

pub fn compile_full_zk_spark_poseidon1_guest_with_optimizations(
    options: &SparkGuestOptimizations,
) -> Result<CompileResult, GuestError> {
    SparkGuestFixture::embedded()?.compile(options)
}

fn compile_spark_fixture(
    fixture: &SparkGuestFixture,
    options: &SparkGuestOptimizations,
) -> Result<CompileResult, GuestError> {
    let constants = &fixture.constants;
    let statement: Statement =
        serde_json::from_value(fixture.statement.clone()).map_err(|error| GuestError::Fixture(error.to_string()))?;
    if statement.digest_preimage.len() < 34 {
        return Err(GuestError::Fixture(format!(
            "expected at least 34 statement-prefix words, got {}",
            statement.digest_preimage.len()
        )));
    }

    let mut replacements = BTreeMap::new();
    for (name, enabled) in [
        ("OPT_FRESH_RELATION_VALUE", options.fresh_relation),
        ("OPT_FRESH_ROWS_VALUE", options.fresh_rows),
        ("OPT_STRUCTURED_ROWS_VALUE", options.structured_rows),
        ("OPT_COMPACT_INPUT_VALUE", options.uses_compact_input()),
        ("OPT_ROW_COUNTS_VALUE", options.row_counts),
        ("OPT_QUERY_PRODUCT_VALUE", options.query_product),
        ("OPT_RADIX_PREFIX_VALUE", options.radix_prefix),
        ("OPT_QUERY_PERMUTATION_VALUE", options.query_permutation),
        ("OPT_UNROLL_POWERS_VALUE", options.unroll_powers),
        ("OPT_BLOCK_QUERY_POWERS_VALUE", options.block_query_powers),
        ("SPARK_HORNER_CUBIC_PLACEHOLDER", options.horner_cubic),
        ("SPARK_EQ_PRECOMPILE_PLACEHOLDER", options.eq_precompile),
        ("SPARK_FACTOR_EQ_ENDPOINTS_PLACEHOLDER", options.factor_eq_endpoints),
        ("OPT_MERKLE_BITS_VALUE", options.merkle_query_bits),
        ("OPT_MERKLE_PAIRED_VALUE", options.paired_merkle),
        ("OPT_EXTENSION_ARITHMETIC_VALUE", options.extension_arithmetic),
        ("OPT_TRANSCRIPT_BLOCKS_VALUE", options.transcript_blocks),
    ] {
        replacements.insert(name.to_string(), usize::from(enabled).to_string());
    }

    fixture.insert_layout_replacements(&mut replacements)?;
    let offsets: Vec<usize> = fixture
        .retained_ranges(options)?
        .iter()
        .map(|range| range.start)
        .collect();
    replacements.insert(
        "FRESH_ROW_HINT_OFFSETS_PLACEHOLDER".to_string(),
        serde_json::to_string(&offsets).unwrap(),
    );
    insert_json(
        &mut replacements,
        "FULL_ZK_CONTEXT_PREFIX_PLACEHOLDER",
        &constants["common"]["context_prefix"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_RELATION_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["common"]["relation_domain_separator"],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_FIXED_VALUE_ROOT_PLACEHOLDER",
        &constants["fixed_commitments"]["value"]["cap"][0],
    )?;
    insert_json(
        &mut replacements,
        "FULL_ZK_STATEMENT_PREFIX_PLACEHOLDER",
        &Value::Array(
            statement.digest_preimage[..34]
                .iter()
                .copied()
                .map(Value::from)
                .collect(),
        ),
    )?;
    insert_json(
        &mut replacements,
        "PLAIN_A_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["fixed_value_whir"]["domain_separator"],
    )?;
    insert_json(
        &mut replacements,
        "PLAIN_B_DOMAIN_SEPARATOR_PLACEHOLDER",
        &constants["read_whir"][1]["domain_separator"],
    )?;
    for matrix in ["A", "B", "C"] {
        for field in ["ROWS", "COLUMNS", "VALUES"] {
            replacements.insert(format!("FULL_ZK_MATRIX_{matrix}_{field}_PLACEHOLDER"), "[]".to_string());
        }
    }

    let source = ProgramSource::Embedded {
        entry: "full_zk_spark_poseidon1.py".to_string(),
        dir: &EMBEDDED_ZKDSL,
    };
    let start = Instant::now();
    replacements
        .entry("OPT_EXTENSION_ARITHMETIC_VALUE".into())
        .or_insert_with(|| "0".into());
    replacements
        .entry("OPT_TRANSCRIPT_BLOCKS_VALUE".into())
        .or_insert_with(|| "0".into());
    let bytecode = compile_program_with_flags(&source, CompilationFlags { replacements });
    Ok(CompileResult {
        bytecode,
        elapsed: start.elapsed(),
    })
}

pub fn compile_poseidon1_primitives_guest() -> CompileResult {
    let source = ProgramSource::Embedded {
        entry: "poseidon1_primitives.py".to_string(),
        dir: &EMBEDDED_ZKDSL,
    };
    let start = Instant::now();
    let bytecode = compile_program_with_flags(
        &source,
        CompilationFlags {
            replacements: BTreeMap::from([
                ("OPT_EXTENSION_ARITHMETIC_VALUE".into(), "0".into()),
                ("OPT_TRANSCRIPT_BLOCKS_VALUE".into(), "0".into()),
            ]),
        },
    );
    CompileResult {
        bytecode,
        elapsed: start.elapsed(),
    }
}

fn insert_json(replacements: &mut BTreeMap<String, String>, name: &str, value: &Value) -> Result<(), GuestError> {
    replacements.insert(
        name.to_string(),
        serde_json::to_string(value).map_err(|error| GuestError::Fixture(error.to_string()))?,
    );
    Ok(())
}

fn insert_flattened_json(
    replacements: &mut BTreeMap<String, String>,
    name: &str,
    value: &Value,
) -> Result<(), GuestError> {
    let rows = value
        .as_array()
        .ok_or_else(|| GuestError::Fixture(format!("{name} is not an array")))?;
    let mut flattened = Vec::new();
    for row in rows {
        let row = row
            .as_array()
            .ok_or_else(|| GuestError::Fixture(format!("{name} contains a non-array row")))?;
        flattened.extend(row.iter().cloned());
    }
    replacements.insert(
        name.to_string(),
        serde_json::to_string(&flattened).map_err(|error| GuestError::Fixture(error.to_string()))?,
    );
    Ok(())
}

pub fn execution_witness(bytecode: &Bytecode, words: &[u32]) -> Result<ExecutionWitness, GuestError> {
    execution_witness_with_hint(bytecode, "proof_words", words, CONTROL_GUEST_WORDS, PREAMBLE_MEMORY_LEN)
}

pub fn full_zk_direct_poseidon1_execution_witness(
    bytecode: &Bytecode,
    words: &[u32],
) -> Result<ExecutionWitness, GuestError> {
    execution_witness_with_hint(
        bytecode,
        "full_zk_words",
        words,
        FULL_ZK_DIRECT_POSEIDON1_WORDS,
        FULL_ZK_DIRECT_POSEIDON1_PREAMBLE_MEMORY_LEN,
    )
}

pub fn full_zk_direct_poseidon2_execution_witness(
    bytecode: &Bytecode,
    words: &[u32],
) -> Result<ExecutionWitness, GuestError> {
    execution_witness_with_hint(
        bytecode,
        "full_zk_words",
        words,
        FULL_ZK_DIRECT_POSEIDON2_WORDS,
        FULL_ZK_DIRECT_POSEIDON2_PREAMBLE_MEMORY_LEN,
    )
}

fn spark_guest_retained_ranges(options: &SparkGuestOptimizations) -> Result<Vec<std::ops::Range<usize>>, GuestError> {
    SparkGuestFixture::embedded()?.retained_ranges(options)
}

/// Removes values derived by the guest and unused input padding when compact input is enabled.
pub fn compact_full_zk_spark_words(words: &[u32], options: &SparkGuestOptimizations) -> Result<Vec<u32>, GuestError> {
    if words.len() != FULL_ZK_SPARK_POSEIDON1_WORDS {
        return Err(GuestError::InvalidWordCount {
            expected: FULL_ZK_SPARK_POSEIDON1_WORDS,
            actual: words.len(),
        });
    }
    if !options.uses_compact_input() {
        return Ok(words.to_vec());
    }
    let mut compact = Vec::new();
    for range in spark_guest_retained_ranges(options)? {
        compact.extend_from_slice(&words[range]);
    }
    Ok(compact)
}

pub fn full_zk_spark_compact_offset(
    offset: usize,
    options: &SparkGuestOptimizations,
) -> Result<Option<usize>, GuestError> {
    if !options.uses_compact_input() {
        return Ok((offset < FULL_ZK_SPARK_POSEIDON1_WORDS).then_some(offset));
    }
    let mut cursor = 0;
    for range in spark_guest_retained_ranges(options)? {
        if range.contains(&offset) {
            return Ok(Some(cursor + offset - range.start));
        }
        cursor += range.len();
    }
    Ok(None)
}

pub fn full_zk_spark_poseidon1_execution_witness(
    bytecode: &Bytecode,
    words: &[u32],
) -> Result<ExecutionWitness, GuestError> {
    let fixture = SparkGuestFixture::embedded()?;
    for flags in 0usize..16 {
        let options = SparkGuestOptimizations {
            fresh_rows: flags & 1 != 0,
            structured_rows: flags & 2 != 0,
            row_counts: flags & 4 != 0,
            derived_fields: flags & 8 != 0,
            ..SparkGuestOptimizations::default()
        };
        let expected = if options.uses_compact_input() {
            fixture.retained_ranges(&options)?.iter().map(|range| range.len()).sum()
        } else {
            FULL_ZK_SPARK_POSEIDON1_WORDS
        };
        if words.len() == expected {
            return fixture.execution_witness(bytecode, words, &options);
        }
    }
    Err(GuestError::InvalidWordCount {
        expected: FULL_ZK_SPARK_POSEIDON1_WORDS,
        actual: words.len(),
    })
}

fn execution_witness_with_hint(
    bytecode: &Bytecode,
    hint_name: &'static str,
    words: &[u32],
    expected_words: usize,
    preamble_memory_len: usize,
) -> Result<ExecutionWitness, GuestError> {
    if words.len() != expected_words {
        return Err(GuestError::InvalidWordCount {
            expected: expected_words,
            actual: words.len(),
        });
    }
    let mut fields = ArenaVec::with_capacity(words.len());
    for (index, &word) in words.iter().enumerate() {
        fields.push(F::from_canonical_checked(word).ok_or(GuestError::NonCanonicalWord { index, value: word })?);
    }
    let mut hints = Hints::default();
    hints.insert(bytecode, hint_name, arena_vec![fields]);
    Ok(ExecutionWitness {
        preamble_memory_len,
        hints,
        min_table_log_n_rows: BTreeMap::new(),
    })
}

pub fn execute_poseidon1_primitives_guest(bytecode: &Bytecode, words: &[u32]) -> Result<ExecutionReport, GuestError> {
    let witness = execution_witness_with_hint(
        bytecode,
        "primitive_words",
        words,
        POSEIDON1_PRIMITIVE_WORDS,
        POSEIDON1_PRIMITIVE_PREAMBLE_MEMORY_LEN,
    )?;
    let public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    let result = try_execute_bytecode(bytecode, &public_input, &witness, false)
        .map_err(|error| GuestError::Vm(error.to_string()))?;
    let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
    let tables = trace
        .traces
        .iter()
        .map(|(table, table_trace)| TableMetrics {
            name: table.name(),
            non_padded_rows: table_trace.non_padded_n_rows,
            log_n_rows: table_trace.log_n_rows,
            padded_rows: 1usize << table_trace.log_n_rows,
        })
        .collect();
    Ok(ExecutionReport {
        metadata: trace.metadata,
        padded_memory_cells: trace.memory.len(),
        tables,
    })
}

pub fn execute_control_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionMetadata, GuestError> {
    execute_control_guest_report(bytecode, public_input, words).map(|report| report.metadata)
}

pub fn execute_control_guest_report(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionReport, GuestError> {
    let witness = execution_witness(bytecode, words)?;
    let result = try_execute_bytecode(bytecode, public_input, &witness, false)
        .map_err(|error| GuestError::Vm(error.to_string()))?;
    let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
    let tables = trace
        .traces
        .iter()
        .map(|(table, table_trace)| TableMetrics {
            name: table.name(),
            non_padded_rows: table_trace.non_padded_n_rows,
            log_n_rows: table_trace.log_n_rows,
            padded_rows: 1usize << table_trace.log_n_rows,
        })
        .collect();
    Ok(ExecutionReport {
        metadata: trace.metadata,
        padded_memory_cells: trace.memory.len(),
        tables,
    })
}

pub fn execute_full_zk_direct_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionMetadata, GuestError> {
    execute_full_zk_direct_poseidon1_guest_report(bytecode, public_input, words).map(|report| report.metadata)
}

pub fn execute_full_zk_direct_poseidon1_guest_report(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionReport, GuestError> {
    let witness = full_zk_direct_poseidon1_execution_witness(bytecode, words)?;
    let result = try_execute_bytecode(bytecode, public_input, &witness, false)
        .map_err(|error| GuestError::Vm(error.to_string()))?;
    let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
    let tables = trace
        .traces
        .iter()
        .map(|(table, table_trace)| TableMetrics {
            name: table.name(),
            non_padded_rows: table_trace.non_padded_n_rows,
            log_n_rows: table_trace.log_n_rows,
            padded_rows: 1usize << table_trace.log_n_rows,
        })
        .collect();
    Ok(ExecutionReport {
        metadata: trace.metadata,
        padded_memory_cells: trace.memory.len(),
        tables,
    })
}

pub fn execute_full_zk_direct_poseidon2_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionMetadata, GuestError> {
    execute_full_zk_direct_poseidon2_guest_report(bytecode, public_input, words).map(|report| report.metadata)
}

pub fn execute_full_zk_direct_poseidon2_guest_report(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionReport, GuestError> {
    let witness = full_zk_direct_poseidon2_execution_witness(bytecode, words)?;
    let result = try_execute_bytecode(bytecode, public_input, &witness, false)
        .map_err(|error| GuestError::Vm(error.to_string()))?;
    let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
    let tables = trace
        .traces
        .iter()
        .map(|(table, table_trace)| TableMetrics {
            name: table.name(),
            non_padded_rows: table_trace.non_padded_n_rows,
            log_n_rows: table_trace.log_n_rows,
            padded_rows: 1usize << table_trace.log_n_rows,
        })
        .collect();
    Ok(ExecutionReport {
        metadata: trace.metadata,
        padded_memory_cells: trace.memory.len(),
        tables,
    })
}

pub fn execute_full_zk_spark_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionMetadata, GuestError> {
    execute_full_zk_spark_poseidon1_guest_report(bytecode, public_input, words).map(|report| report.metadata)
}

pub fn validate_full_zk_spark_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<(), GuestError> {
    let witness = full_zk_spark_poseidon1_execution_witness(bytecode, words)?;
    try_execute_bytecode(bytecode, public_input, &witness, false).map_err(|error| GuestError::Vm(error.to_string()))?;
    Ok(())
}

pub fn execute_full_zk_spark_poseidon1_guest_report(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<ExecutionReport, GuestError> {
    profile_full_zk_spark_poseidon1_guest(bytecode, public_input, words, false)
}

pub fn profile_full_zk_spark_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
    profiling: bool,
) -> Result<ExecutionReport, GuestError> {
    let witness = full_zk_spark_poseidon1_execution_witness(bytecode, words)?;
    let result = try_execute_bytecode(bytecode, public_input, &witness, profiling)
        .map_err(|error| GuestError::Vm(error.to_string()))?;
    let trace = get_execution_trace(bytecode, result, &witness.min_table_log_n_rows);
    let tables = trace
        .traces
        .iter()
        .map(|(table, table_trace)| TableMetrics {
            name: table.name(),
            non_padded_rows: table_trace.non_padded_n_rows,
            log_n_rows: table_trace.log_n_rows,
            padded_rows: 1usize << table_trace.log_n_rows,
        })
        .collect();
    Ok(ExecutionReport {
        metadata: trace.metadata,
        padded_memory_cells: trace.memory.len(),
        tables,
    })
}

pub fn prove_control_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<RootProofResult, GuestError> {
    let witness = execution_witness(bytecode, words)?;
    let proving_start = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(CONTROL_ROOT_LOG_INV_RATE),
        false,
    )
    .map_err(|error| GuestError::Proof(error.to_string()))?;
    let proving_elapsed = proving_start.elapsed();
    let serialized_proof_bytes = postcard::to_allocvec(&proof.proof)
        .map_err(|error| GuestError::Proof(error.to_string()))?
        .len();
    let verification_start = Instant::now();
    verify_execution(bytecode, public_input, proof.proof.clone())
        .map_err(|error| GuestError::Proof(error.to_string()))?;
    Ok(RootProofResult {
        proof,
        proving_elapsed,
        verification_elapsed: verification_start.elapsed(),
        serialized_proof_bytes,
    })
}

pub fn prove_full_zk_direct_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<RootProofResult, GuestError> {
    let witness = full_zk_direct_poseidon1_execution_witness(bytecode, words)?;
    let proving_start = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(FULL_ZK_DIRECT_POSEIDON1_ROOT_LOG_INV_RATE),
        false,
    )
    .map_err(|error| GuestError::Proof(error.to_string()))?;
    let proving_elapsed = proving_start.elapsed();
    let serialized_proof_bytes = postcard::to_allocvec(&proof.proof)
        .map_err(|error| GuestError::Proof(error.to_string()))?
        .len();
    let verification_start = Instant::now();
    verify_execution(bytecode, public_input, proof.proof.clone())
        .map_err(|error| GuestError::Proof(error.to_string()))?;
    Ok(RootProofResult {
        proof,
        proving_elapsed,
        verification_elapsed: verification_start.elapsed(),
        serialized_proof_bytes,
    })
}

pub fn prove_full_zk_direct_poseidon2_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<RootProofResult, GuestError> {
    let witness = full_zk_direct_poseidon2_execution_witness(bytecode, words)?;
    let proving_start = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(FULL_ZK_DIRECT_POSEIDON2_ROOT_LOG_INV_RATE),
        false,
    )
    .map_err(|error| GuestError::Proof(error.to_string()))?;
    let proving_elapsed = proving_start.elapsed();
    let serialized_proof_bytes = postcard::to_allocvec(&proof.proof)
        .map_err(|error| GuestError::Proof(error.to_string()))?
        .len();
    let verification_start = Instant::now();
    verify_execution(bytecode, public_input, proof.proof.clone())
        .map_err(|error| GuestError::Proof(error.to_string()))?;
    Ok(RootProofResult {
        proof,
        proving_elapsed,
        verification_elapsed: verification_start.elapsed(),
        serialized_proof_bytes,
    })
}

pub fn prove_full_zk_spark_poseidon1_guest(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    words: &[u32],
) -> Result<RootProofResult, GuestError> {
    let witness = full_zk_spark_poseidon1_execution_witness(bytecode, words)?;
    let proving_start = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(FULL_ZK_SPARK_POSEIDON1_ROOT_LOG_INV_RATE),
        false,
    )
    .map_err(|error| GuestError::Proof(error.to_string()))?;
    let proving_elapsed = proving_start.elapsed();
    let serialized_proof_bytes = postcard::to_allocvec(&proof.proof)
        .map_err(|error| GuestError::Proof(error.to_string()))?
        .len();
    let verification_start = Instant::now();
    verify_execution(bytecode, public_input, proof.proof.clone())
        .map_err(|error| GuestError::Proof(error.to_string()))?;
    Ok(RootProofResult {
        proof,
        proving_elapsed,
        verification_elapsed: verification_start.elapsed(),
        serialized_proof_bytes,
    })
}
