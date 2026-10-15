use backend::*;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    GRINDING_BITS, MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, WhirExecutionProfile, default_whir_config,
};
use lean_vm::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::OnceLock;
use sub_protocols::{
    N_VARS_TO_SEND_GKR_COEFFS, compute_total_logup_log_size, min_stacked_n_vars, total_whir_statements,
};
use tracing::instrument;
use xmss::{LOG_LIFETIME, PUBLIC_PARAM_LEN_FE, RANDOMNESS_LEN_FE, TARGET_SUM, V, W, XMSS_DIGEST_LEN};

use crate::bytecode_claims::bytecode_reduction_sumcheck_proof_size;
use crate::single_message_aggregation::TWEAK_TABLE_SIZE_FE_PADDED;

// preamble memory layout: see `build_preamble_memory` in utils.py:
// [000.. (ZERO_VEC_LEN)][10000000 (fiat-shamir domain sep)][10000 (one in extension field)][111... (NUM_REPEATED_ONES)][tweak table]
/// Algebraically equivalent recursive-verifier implementations for paired measurements.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecursiveVerifierOptions {
    pub horner_evaluation: bool,
    pub fft_poseidon_mds: bool,
    #[serde(default)]
    pub extension_subtractions: bool,
}

/// Exact dimensions of an execution proof consumed by a recursive verifier.
///
/// The proof still carries these values in its transcript. A verifier compiled
/// for this shape checks the transcript values before using compiled constants.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct RecursiveChildShape {
    pub log_memory: usize,
    pub table_log_heights: [usize; N_TABLES],
}

pub const ZERO_VEC_LEN: usize = 16;
pub const NUM_REPEATED_ONES: usize = 32;
pub const PREAMBLE_MEMORY_LEN: usize =
    ZERO_VEC_LEN + DIGEST_LEN + DIMENSION + NUM_REPEATED_ONES + TWEAK_TABLE_SIZE_FE_PADDED;

pub(crate) const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
pub(crate) const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;

static BYTECODE: OnceLock<Bytecode> = OnceLock::new();

pub fn get_aggregation_bytecode() -> &'static Bytecode {
    BYTECODE
        .get()
        .unwrap_or_else(|| panic!("call init_aggregation_bytecode() first"))
}

pub fn try_get_aggregation_bytecode() -> Option<&'static Bytecode> {
    BYTECODE.get()
}

pub fn init_aggregation_bytecode() {
    BYTECODE.get_or_init(compile_main_program_self_referential);
}

static EMBEDDED_ZK_DSL: include_dir::Dir<'_> = include_dir::include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

pub const MAX_RECURSIONS: usize = 16;
pub const MAX_XMSS_AGGREGATED: usize = 1 << 15; // TODO increase (we would need a bigger minimal memory size, totally doable)
pub const MAX_XMSS_DUPLICATES: usize = 1 << 15; // ...same

pub(crate) const SINGLE_MESSAGE_FLAG: usize = 1;
pub(crate) const MULTI_MESSAGE_FLAG: usize = 0;

pub(crate) const BYTECODE_CLAIM_OFFSET: usize = DIGEST_LEN;
/// Single-message component data: pubkeys_hash | message | merkle_chunks | tweaks_hash.
pub(crate) const COMPONENT_DATA_SIZE: usize = DIGEST_LEN + DIGEST_LEN + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN; // pubkeys_hash + hashed message + merkle chunks + tweaks_hash

pub(crate) fn bytecode_claim_size_padded(program_log_size: usize) -> usize {
    let bytecode_point_n_vars = program_log_size + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    ((bytecode_point_n_vars + 1) * DIMENSION).next_multiple_of(DIGEST_LEN)
}

pub(crate) fn initial_fiat_shamir_cap_offset(program_log_size: usize) -> usize {
    BYTECODE_CLAIM_OFFSET + bytecode_claim_size_padded(program_log_size)
}

pub(crate) fn component_data_offset(program_log_size: usize) -> usize {
    initial_fiat_shamir_cap_offset(program_log_size) + DIGEST_LEN
}

pub(crate) fn single_message_input_data_size_padded(program_log_size: usize) -> usize {
    component_data_offset(program_log_size) + COMPONENT_DATA_SIZE
}

fn compile_main_program(program_log_size: usize, bytecode_zero_eval: F) -> Bytecode {
    let replacements = build_replacements(program_log_size, bytecode_zero_eval);

    let source = ProgramSource::Embedded {
        entry: "main.py".to_string(),
        dir: &EMBEDDED_ZK_DSL,
    };
    compile_program_with_flags(&source, CompilationFlags { replacements })
}

#[instrument(skip_all)]
fn compile_main_program_self_referential() -> Bytecode {
    let mut log_size_guess = 18;
    let bytecode_zero_eval = F::ZERO;
    for _ in 0..10 {
        let bytecode = compile_main_program(log_size_guess, bytecode_zero_eval);
        let actual_log_size = bytecode.log_size();
        assert_eq!(bytecode.ending_pc(), (1 << actual_log_size) - 1);
        assert_eq!(bytecode_zero_eval, bytecode.instructions_multilinear()[0]);
        if actual_log_size == log_size_guess {
            return bytecode;
        }
        eprintln!(
            "Wrong guess at `compile_main_program_self_referential` (log_size {log_size_guess}->{actual_log_size})"
        );
        log_size_guess = actual_log_size;
    }
    panic!("`compile_main_program_self_referential` did not converge");
}

pub(crate) fn build_replacements(log_inner_bytecode: usize, bytecode_zero_eval: F) -> BTreeMap<String, String> {
    build_replacements_with_profile(
        log_inner_bytecode,
        bytecode_zero_eval,
        None,
        RecursiveVerifierOptions::default(),
    )
}

fn build_replacements_with_profile(
    log_inner_bytecode: usize,
    bytecode_zero_eval: F,
    profile: Option<&WhirExecutionProfile>,
    options: RecursiveVerifierOptions,
) -> BTreeMap<String, String> {
    build_replacements_for_dimension(log_inner_bytecode, bytecode_zero_eval, profile, options, None)
}

fn build_replacements_for_dimension(
    log_inner_bytecode: usize,
    bytecode_zero_eval: F,
    profile: Option<&WhirExecutionProfile>,
    options: RecursiveVerifierOptions,
    child_num_variables: Option<usize>,
) -> BTreeMap<String, String> {
    if let Some(profile) = profile {
        profile.validate().expect("invalid recursive child profile");
    }
    let fixed_config = child_num_variables.map(|n_vars| {
        let profile = profile.expect("a fixed child dimension requires an explicit profile");
        profile
            .validate_for_n_vars(n_vars)
            .expect("invalid recursive child dimension");
        assert!(
            n_vars >= min_stacked_n_vars(log_inner_bytecode),
            "child dimension is smaller than the minimum stack for its bytecode"
        );
        WhirConfig::<EF>::new(&profile.whir_config(), n_vars)
    });
    let first_fold = profile.map_or(WHIR_INITIAL_FOLDING_FACTOR, |p| p.first_folding_factor);
    let subsequent_fold = profile.map_or(WHIR_SUBSEQUENT_FOLDING_FACTOR, |p| p.subsequent_folding_factor);
    let rs_reduction = profile.map_or(RS_DOMAIN_INITIAL_REDUCTION_FACTOR, |p| {
        p.rs_domain_initial_reduction_factor
    });
    let final_threshold = profile.map_or(MAX_NUM_VARIABLES_TO_SEND_COEFFS, |p| p.max_num_variables_to_send_coeffs);
    let grinding_bits = profile.map_or(GRINDING_BITS, |p| p.grinding_bits);
    let min_rate = profile.map_or(MIN_WHIR_LOG_INV_RATE, |p| p.log_inv_rate);
    let max_rate = profile.map_or(MAX_WHIR_LOG_INV_RATE, |p| p.log_inv_rate);
    let domain_reduction = first_fold.min(rs_reduction + subsequent_fold);
    let ending_pc = (1 << log_inner_bytecode) - 1;
    let min_stacked = child_num_variables.unwrap_or_else(|| {
        min_stacked_n_vars(log_inner_bytecode).max(profile.map_or(0, |_| first_fold + final_threshold + 1))
    });

    let mut replacements = BTreeMap::new();
    replacements.insert(
        "EXTENSION_SUBTRACTIONS_PLACEHOLDER".to_string(),
        usize::from(options.extension_subtractions).to_string(),
    );
    replacements.insert(
        "UNIVARIATE_EVAL_HORNER_PLACEHOLDER".to_string(),
        usize::from(options.horner_evaluation).to_string(),
    );
    replacements.insert(
        "MIN_FINAL_WHIR_VARS_PLACEHOLDER".to_string(),
        fixed_config
            .as_ref()
            .map_or(final_threshold.saturating_sub(subsequent_fold - 1), |config| {
                config.final_sumcheck_rounds
            })
            .to_string(),
    );
    replacements.insert(
        "MAX_FINAL_WHIR_VARS_PLACEHOLDER".to_string(),
        fixed_config
            .as_ref()
            .map_or(final_threshold, |config| config.final_sumcheck_rounds)
            .to_string(),
    );
    replacements.insert(
        "WHIR_MERKLE_HEIGHT_DISPATCH_PLACEHOLDER".to_string(),
        merkle_height_dispatch(fixed_config.as_ref()),
    );

    replacements.insert(
        "WHIR_DOMAIN_REDUCTION_PLACEHOLDER".to_string(),
        domain_reduction.to_string(),
    );
    let mut all_valid_dimensions = vec![];
    let mut all_potential_num_queries = vec![];
    let mut all_potential_query_grinding = vec![];
    let mut all_potential_num_oods = vec![];
    let mut all_potential_folding_grinding = vec![];
    let mut max_stacked_by_rate = vec![];
    let mut too_much_grinding = false;
    for log_inv_rate in min_rate..=max_rate {
        let max_n_vars = child_num_variables.unwrap_or(F::TWO_ADICITY + domain_reduction - log_inv_rate);
        max_stacked_by_rate.push(max_n_vars.to_string());
        let whir_config_builder =
            profile.map_or_else(|| default_whir_config(log_inv_rate), WhirExecutionProfile::whir_config);

        let mut valid_dimensions_for_rate = vec![];
        let mut queries_for_rate = vec![];
        let mut query_grinding_for_rate = vec![];
        let mut oods_for_rate = vec![];
        let mut folding_grinding_for_rate = vec![];
        for n_vars in min_stacked..=max_n_vars {
            valid_dimensions_for_rate.push(
                usize::from(profile.is_none_or(|profile| profile.validate_for_n_vars(n_vars).is_ok())).to_string(),
            );
            let cfg = WhirConfig::<EF>::new(&whir_config_builder, n_vars);
            if cfg.max_folding_pow_bits() > grinding_bits {
                too_much_grinding = true;
            }

            let mut num_queries = vec![];
            let mut query_grinding_bits = vec![];
            let mut oods = vec![cfg.commitment_ood_samples];
            let mut folding_grinding = vec![cfg.starting_folding_pow_bits];
            for round in &cfg.round_parameters {
                num_queries.push(round.num_queries);
                query_grinding_bits.push(round.query_pow_bits);
                oods.push(round.ood_samples);
                folding_grinding.push(round.folding_pow_bits);
            }
            num_queries.push(cfg.final_queries);
            query_grinding_bits.push(cfg.final_query_pow_bits);

            queries_for_rate.push(format!(
                "[{}]",
                num_queries.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(", ")
            ));
            query_grinding_for_rate.push(format!(
                "[{}]",
                query_grinding_bits
                    .iter()
                    .map(|q| q.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            oods_for_rate.push(format!(
                "[{}]",
                oods.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", ")
            ));
            folding_grinding_for_rate.push(format!(
                "[{}]",
                folding_grinding
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        all_valid_dimensions.push(format!("[{}]", valid_dimensions_for_rate.join(", ")));
        all_potential_num_queries.push(format!("[{}]", queries_for_rate.join(", ")));
        all_potential_query_grinding.push(format!("[{}]", query_grinding_for_rate.join(", ")));
        all_potential_num_oods.push(format!("[{}]", oods_for_rate.join(", ")));
        all_potential_folding_grinding.push(format!("[{}]", folding_grinding_for_rate.join(", ")));
    }
    replacements.insert(
        "WHIR_VALID_DIMENSIONS_PLACEHOLDER".to_string(),
        format!("[{}]", all_valid_dimensions.join(", ")),
    );
    replacements.insert(
        "MAX_STACKED_N_VARS_BY_RATE_PLACEHOLDER".to_string(),
        format!("[{}]", max_stacked_by_rate.join(", ")),
    );
    if too_much_grinding {
        tracing::info!("Warning: Too much grinding for WHIR folding"); // TODO
    }
    replacements.insert(
        "WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER".to_string(),
        rs_reduction.to_string(),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_QUERIES_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_queries.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_QUERY_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_query_grinding.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_oods.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_FOLDING_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_folding_grinding.join(", ")),
    );
    replacements.insert("MIN_STACKED_N_VARS_PLACEHOLDER".to_string(), min_stacked.to_string());

    // VM recursion parameters (different from WHIR)
    replacements.insert("N_TABLES_PLACEHOLDER".to_string(), N_TABLES.to_string());
    let zero_table_values = format!("[{}]", ["0"; N_TABLES].join(", "));
    for key in [
        "FIXED_TABLE_LOG_HEIGHTS_PLACEHOLDER",
        "FIXED_TABLE_HEIGHTS_PLACEHOLDER",
        "FIXED_GKR_TABLE_BASE_OFFSETS_PLACEHOLDER",
        "FIXED_STACKED_TABLE_BASE_OFFSETS_PLACEHOLDER",
    ] {
        replacements.insert(key.to_string(), zero_table_values.clone());
    }
    for key in [
        "FIXED_CHILD_SHAPE_PLACEHOLDER",
        "FIXED_WHIR_LOG_INV_RATE_PLACEHOLDER",
        "FIXED_LOG_MEMORY_PLACEHOLDER",
        "FIXED_LOG_MAX_TABLE_HEIGHT_PLACEHOLDER",
        "FIXED_LOG_N_CYCLES_PLACEHOLDER",
        "FIXED_LOG_BYTECODE_PADDED_PLACEHOLDER",
        "FIXED_STACKED_N_VARS_PLACEHOLDER",
        "FIXED_LOGUP_GKR_N_VARS_PLACEHOLDER",
        "FIXED_GKR_ACTIVE_LEN_PLACEHOLDER",
    ] {
        replacements.insert(key.to_string(), "0".to_string());
    }
    replacements.insert(
        "MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        MIN_LOG_N_ROWS_PER_TABLE.to_string(),
    );
    let mut max_log_n_rows_per_table = MAX_LOG_N_ROWS_PER_TABLE.to_vec();
    max_log_n_rows_per_table.sort_by_key(|(table, _)| table.index());
    max_log_n_rows_per_table.dedup();
    assert_eq!(max_log_n_rows_per_table.len(), N_TABLES);
    replacements.insert("MIN_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(), min_rate.to_string());
    replacements.insert("MAX_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(), max_rate.to_string());
    replacements.insert(
        "MAX_NUM_VARIABLES_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        final_threshold.to_string(),
    );
    replacements.insert(
        "LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        N_VARS_TO_SEND_GKR_COEFFS.to_string(),
    );
    replacements.insert(
        "WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        first_fold.to_string(),
    );
    replacements.insert(
        "WHIR_SUBSEQUENT_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        subsequent_fold.to_string(),
    );
    replacements.insert(
        "MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        format!(
            "[{}]",
            max_log_n_rows_per_table
                .iter()
                .map(|(_, v)| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    replacements.insert(
        "MIN_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MIN_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MAX_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_BUS_WIDTH_PLACEHOLDER".to_string(),
        (1 << LOG_MAX_BUS_WIDTH).to_string(),
    );
    replacements.insert(
        "LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_MEMORY_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_BYTECODE_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOG_GUEST_BYTECODE_LEN_PLACEHOLDER".to_string(),
        log_inner_bytecode.to_string(),
    );
    replacements.insert("COL_PC_PLACEHOLDER".to_string(), EXEC_COL_PC.to_string());
    let bytecode_point_n_vars = log_inner_bytecode + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    replacements.insert(
        "BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER".to_string(),
        bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars).to_string(),
    );

    let mut one_buses_domseps = vec![];
    let mut one_buses_data_cols = vec![];
    let mut one_buses_data_offsets = vec![];
    let mut one_buses_new_cols = vec![];
    let mut num_cols_air = vec![];
    let mut n_air_columns = vec![];
    let mut n_air_shift_columns = vec![];
    let mut n_air_constraints = vec![];
    let mut one_buses_all_cols = vec![];
    for table in ALL_TABLES {
        let mut table_domseps = vec![];
        let mut table_data_cols = vec![];
        let mut table_data_offsets = vec![];
        let mut table_new_cols = vec![];
        let mut seen_cols: HashSet<ColIndex> = HashSet::new();
        for bus in table.bus_interactions() {
            if !matches!(bus.multiplicity, BusMultiplicity::One) {
                continue;
            }
            let BusData::Constant(domsep) = bus.domainsep else {
                panic!("Multiplicity::One bus domsep must be a constant");
            };
            let mut data_cols = vec![];
            let mut data_offsets = vec![];
            let mut new_cols = vec![];
            for entry in &bus.data {
                let (col, ofs) = match entry {
                    BusData::Column(c) => (*c, 0),
                    BusData::ColumnPlusConstant(c, o) => (*c, *o),
                    BusData::Constant(_) => panic!("Multiplicity::One bus data must be a column"),
                };
                data_cols.push(col);
                data_offsets.push(ofs);
                if seen_cols.insert(col) {
                    new_cols.push(col);
                }
            }
            table_domseps.push(domsep.to_string());
            table_data_cols.push(format!(
                "[{}]",
                data_cols.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
            table_data_offsets.push(format!(
                "[{}]",
                data_offsets.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
            table_new_cols.push(format!(
                "[{}]",
                new_cols.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
        }
        one_buses_domseps.push(format!("[{}]", table_domseps.join(", ")));
        one_buses_data_cols.push(format!("[{}]", table_data_cols.join(", ")));
        one_buses_data_offsets.push(format!("[{}]", table_data_offsets.join(", ")));
        one_buses_new_cols.push(format!("[{}]", table_new_cols.join(", ")));

        let mut sorted_seen: Vec<ColIndex> = seen_cols.iter().copied().collect();
        sorted_seen.sort();
        one_buses_all_cols.push(format!(
            "[{}]",
            sorted_seen.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
        ));

        num_cols_air.push(table.n_columns().to_string());
        n_air_columns.push(table.n_columns().to_string());
        n_air_shift_columns.push(table.n_shift_columns().to_string());
        n_air_constraints.push(table.n_constraints().to_string());
    }
    let max_num_cols_air = ALL_TABLES.iter().map(|t| t.n_columns()).max().unwrap();
    replacements.insert("MAX_NUM_COLS_AIR_PLACEHOLDER".to_string(), max_num_cols_air.to_string());
    replacements.insert(
        "ONE_BUSES_ALL_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_all_cols.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_DOMSEPS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_domseps.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_DATA_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_data_cols.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_DATA_OFFSETS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_data_offsets.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_NEW_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_new_cols.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_AIR_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_air.join(", ")),
    );
    replacements.insert(
        "EXECUTION_TABLE_INDEX_PLACEHOLDER".to_string(),
        Table::execution().index().to_string(),
    );
    replacements.insert(
        "TOTAL_NUM_AIR_CONSTRAINTS_PLACEHOLDER".to_string(),
        total_air_constraints().to_string(),
    );
    replacements.insert(
        "N_AIR_CONSTRAINTS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_constraints.join(", ")),
    );
    let mut air_alpha_offsets = Vec::with_capacity(n_air_constraints.len());
    let mut cumul: usize = 0;
    for s in &n_air_constraints {
        air_alpha_offsets.push(cumul.to_string());
        cumul += s.parse::<usize>().unwrap();
    }
    replacements.insert(
        "AIR_ALPHA_OFFSETS_PLACEHOLDER".to_string(),
        format!("[{}]", air_alpha_offsets.join(", ")),
    );
    replacements.insert(
        "MAX_AIR_FULL_DEGREE_PLACEHOLDER".to_string(),
        (ALL_TABLES.iter().map(|t| t.degree_air()).max().unwrap() + 1).to_string(),
    );
    replacements.insert(
        "N_AIR_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_columns.join(", ")),
    );
    replacements.insert(
        "N_AIR_SHIFT_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_shift_columns.join(", ")),
    );
    replacements.insert(
        "EVALUATE_AIR_FUNCTIONS_PLACEHOLDER".to_string(),
        all_air_evals_in_zk_dsl(options.fft_poseidon_mds),
    );
    replacements.insert(
        "N_INSTRUCTION_COLUMNS_PLACEHOLDER".to_string(),
        N_INSTRUCTION_COLUMNS.to_string(),
    );
    replacements.insert(
        "TOTAL_WHIR_STATEMENTS_PLACEHOLDER".to_string(),
        total_whir_statements().to_string(),
    );
    replacements.insert("STARTING_PC_PLACEHOLDER".to_string(), STARTING_PC.to_string());
    replacements.insert("ENDING_PC_PLACEHOLDER".to_string(), ending_pc.to_string());

    // XMSS-specific replacements
    replacements.insert("V_PLACEHOLDER".to_string(), V.to_string());
    replacements.insert("W_PLACEHOLDER".to_string(), W.to_string());
    replacements.insert("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string());
    replacements.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string());
    replacements.insert("MESSAGE_LEN_PLACEHOLDER".to_string(), DIGEST_LEN.to_string()); // the hashed message is one digest
    replacements.insert("RANDOMNESS_LEN_PLACEHOLDER".to_string(), RANDOMNESS_LEN_FE.to_string());
    replacements.insert(
        "PUBLIC_PARAM_LEN_FE_PLACEHOLDER".to_string(),
        PUBLIC_PARAM_LEN_FE.to_string(),
    );
    replacements.insert(
        "MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER".to_string(),
        MERKLE_LEVELS_PER_CHUNK_FOR_SLOT.to_string(),
    );
    replacements.insert("XMSS_DIGEST_LEN_PLACEHOLDER".to_string(), XMSS_DIGEST_LEN.to_string());

    replacements.insert(
        "SINGLE_MESSAGE_FLAG_PLACEHOLDER".to_string(),
        SINGLE_MESSAGE_FLAG.to_string(),
    );
    replacements.insert(
        "MULTI_MESSAGE_FLAG_PLACEHOLDER".to_string(),
        MULTI_MESSAGE_FLAG.to_string(),
    );
    replacements.insert(
        "MAX_XMSS_AGGREGATED_PLACEHOLDER".to_string(),
        MAX_XMSS_AGGREGATED.to_string(),
    );
    replacements.insert(
        "MAX_XMSS_DUPLICATES_PLACEHOLDER".to_string(),
        MAX_XMSS_DUPLICATES.to_string(),
    );
    replacements.insert("MAX_RECURSIONS_PLACEHOLDER".to_string(), MAX_RECURSIONS.to_string());

    // Bytecode zero eval
    replacements.insert(
        "BYTECODE_ZERO_EVAL_PLACEHOLDER".to_string(),
        bytecode_zero_eval.as_canonical_u64().to_string(),
    );
    replacements.insert("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string());
    replacements.insert(
        "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
        NUM_REPEATED_ONES.to_string(),
    );

    replacements
}

fn format_usize_array(values: &[usize]) -> String {
    format!(
        "[{}]",
        values.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
    )
}

impl RecursiveChildShape {
    /// Read the execution dimensions from a proof after native verification.
    pub fn from_verified_raw_proof(proof: &RawProof<F>) -> Result<Self, ProofError> {
        if proof.transcript.len() < 2 + N_TABLES {
            return Err(ProofError::InvalidProof);
        }
        let dimensions = proof.transcript[..2 + N_TABLES]
            .iter()
            .map(|value| value.as_canonical_u32() as usize)
            .collect::<Vec<_>>();
        Ok(Self {
            log_memory: dimensions[1],
            table_log_heights: std::array::from_fn(|index| dimensions[index + 2]),
        })
    }

    fn fixed_replacements(
        &self,
        inner_bytecode: &Bytecode,
        profile: &WhirExecutionProfile,
    ) -> (usize, BTreeMap<String, String>) {
        profile.validate().expect("invalid recursive child profile");
        assert!(
            (MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&self.log_memory),
            "fixed child memory dimension is out of range"
        );
        assert!(
            inner_bytecode.log_size() <= self.log_memory,
            "fixed child memory dimension is smaller than its bytecode"
        );

        let mut table_dimensions = BTreeMap::new();
        for (index, table) in ALL_TABLES.iter().copied().enumerate() {
            let log_height = self.table_log_heights[index];
            assert!(
                (MIN_LOG_N_ROWS_PER_TABLE..=max_log_n_rows_per_table(&table)).contains(&log_height),
                "fixed child table dimension is out of range"
            );
            table_dimensions.insert(table, log_height);
        }
        let sorted_tables = sort_tables_by_height(&table_dimensions);
        let log_max_table_height = sorted_tables[0].1;
        assert!(
            log_max_table_height <= self.log_memory,
            "fixed child table is larger than its memory domain"
        );

        let table_heights = std::array::from_fn::<_, N_TABLES, _>(|index| 1usize << self.table_log_heights[index]);
        let log_bytecode_padded = inner_bytecode.log_size().max(log_max_table_height);
        let mut gkr_active_len = (1usize << self.log_memory) + (1usize << log_bytecode_padded);
        let mut stacked_active_len = (2usize << self.log_memory) + (1usize << log_bytecode_padded);
        let mut gkr_table_base_offsets = [0usize; N_TABLES];
        let mut stacked_table_base_offsets = [0usize; N_TABLES];
        for (table, log_height) in &sorted_tables {
            let index = table.index();
            let rows = 1usize << log_height;
            gkr_table_base_offsets[index] = gkr_active_len;
            stacked_table_base_offsets[index] = stacked_active_len;
            let one_bus_count = table
                .bus_interactions()
                .into_iter()
                .filter(|bus| matches!(bus.multiplicity, BusMultiplicity::One))
                .count();
            assert_eq!(
                one_bus_count + 1,
                table.bus_interactions().len(),
                "recursive verifier expects one column-multiplicity bus per table"
            );
            gkr_active_len += rows * (one_bus_count + 1);
            stacked_active_len += rows * table.n_columns();
        }
        let stacked_n_vars = log2_ceil_usize(stacked_active_len);
        profile
            .validate_for_n_vars(stacked_n_vars)
            .expect("fixed child shape has invalid WHIR geometry");
        let logup_gkr_n_vars = log2_ceil_usize(gkr_active_len);
        assert_eq!(
            logup_gkr_n_vars,
            compute_total_logup_log_size(self.log_memory, log_bytecode_padded, &sorted_tables,),
            "fixed child GKR dimension must match the native verifier"
        );

        let mut replacements = BTreeMap::new();
        for (key, value) in [
            ("FIXED_CHILD_SHAPE_PLACEHOLDER", 1),
            ("FIXED_WHIR_LOG_INV_RATE_PLACEHOLDER", profile.log_inv_rate),
            ("FIXED_LOG_MEMORY_PLACEHOLDER", self.log_memory),
            ("FIXED_LOG_MAX_TABLE_HEIGHT_PLACEHOLDER", log_max_table_height),
            (
                "FIXED_LOG_N_CYCLES_PLACEHOLDER",
                self.table_log_heights[Table::execution().index()],
            ),
            ("FIXED_LOG_BYTECODE_PADDED_PLACEHOLDER", log_bytecode_padded),
            ("FIXED_STACKED_N_VARS_PLACEHOLDER", stacked_n_vars),
            ("FIXED_LOGUP_GKR_N_VARS_PLACEHOLDER", logup_gkr_n_vars),
            ("FIXED_GKR_ACTIVE_LEN_PLACEHOLDER", gkr_active_len),
        ] {
            replacements.insert(key.to_string(), value.to_string());
        }
        for (key, values) in [
            ("FIXED_TABLE_LOG_HEIGHTS_PLACEHOLDER", self.table_log_heights.as_slice()),
            ("FIXED_TABLE_HEIGHTS_PLACEHOLDER", table_heights.as_slice()),
            (
                "FIXED_GKR_TABLE_BASE_OFFSETS_PLACEHOLDER",
                gkr_table_base_offsets.as_slice(),
            ),
            (
                "FIXED_STACKED_TABLE_BASE_OFFSETS_PLACEHOLDER",
                stacked_table_base_offsets.as_slice(),
            ),
        ] {
            replacements.insert(key.to_string(), format_usize_array(values));
        }
        (stacked_n_vars, replacements)
    }
}

pub(crate) fn compile_recursive_entry(
    entry: &str,
    inner_bytecode: &Bytecode,
    extra_replacements: BTreeMap<String, String>,
) -> Bytecode {
    compile_recursive_entry_with_profile(entry, inner_bytecode, extra_replacements, None)
}

pub(crate) fn compile_recursive_entry_with_profile(
    entry: &str,
    inner_bytecode: &Bytecode,
    extra_replacements: BTreeMap<String, String>,
    profile: Option<&WhirExecutionProfile>,
) -> Bytecode {
    compile_recursive_entry_with_options(
        entry,
        inner_bytecode,
        extra_replacements,
        profile,
        RecursiveVerifierOptions::default(),
    )
}

pub(crate) fn compile_recursive_entry_with_options(
    entry: &str,
    inner_bytecode: &Bytecode,
    extra_replacements: BTreeMap<String, String>,
    profile: Option<&WhirExecutionProfile>,
    options: RecursiveVerifierOptions,
) -> Bytecode {
    compile_recursive_entry_for_dimension(entry, inner_bytecode, extra_replacements, profile, options, None)
}

pub(crate) fn compile_recursive_entry_for_dimension(
    entry: &str,
    inner_bytecode: &Bytecode,
    extra_replacements: BTreeMap<String, String>,
    profile: Option<&WhirExecutionProfile>,
    options: RecursiveVerifierOptions,
    child_num_variables: Option<usize>,
) -> Bytecode {
    let bytecode_zero_eval = inner_bytecode.instructions_multilinear()[0];
    let mut replacements = build_replacements_for_dimension(
        inner_bytecode.log_size(),
        bytecode_zero_eval,
        profile,
        options,
        child_num_variables,
    );
    replacements.insert(
        "ENDING_PC_PLACEHOLDER".to_string(),
        inner_bytecode.ending_pc().to_string(),
    );
    replacements.insert(
        "NODE_INFO_ALLOCATION_PLACEHOLDER".to_string(),
        "Array(NODE_INFO_SIZE)".to_string(),
    );
    replacements.insert("NODE_INFO_ADDRESS_FUNCTION_PLACEHOLDER".to_string(), String::new());
    replacements.insert(
        "NODE_INFO_PUBLIC_OUTPUT_PLACEHOLDER".to_string(),
        "slice_hash(node_info, NODE_INFO_NUM_CHUNKS, pub_mem)".to_string(),
    );
    replacements.extend(extra_replacements);
    compile_program_with_flags(
        &ProgramSource::Embedded {
            entry: entry.to_string(),
            dir: &EMBEDDED_ZK_DSL,
        },
        CompilationFlags { replacements },
    )
}

pub(crate) fn compile_recursive_entry_for_fixed_shape(
    entry: &str,
    inner_bytecode: &Bytecode,
    mut extra_replacements: BTreeMap<String, String>,
    profile: &WhirExecutionProfile,
    options: RecursiveVerifierOptions,
    child_shape: &RecursiveChildShape,
) -> Bytecode {
    let (child_num_variables, fixed_replacements) = child_shape.fixed_replacements(inner_bytecode, profile);
    extra_replacements.extend(fixed_replacements);
    compile_recursive_entry_for_dimension(
        entry,
        inner_bytecode,
        extra_replacements,
        Some(profile),
        options,
        Some(child_num_variables),
    )
}

fn merkle_height_dispatch(config: Option<&WhirConfig<EF>>) -> String {
    let call = |height: &str| {
        format!(
            "decompose_and_verify_merkle_batch_with_height(num_queries, sampled, root, {height}, num_chunks, stir_points, answers)"
        )
    };
    let Some(config) = config else {
        return format!("match_range(height, range(0, 25), lambda h: {})", call("h"));
    };
    let mut heights = config
        .round_parameters
        .iter()
        .chain(std::iter::once(&config.final_round_config()))
        .map(|round| round.domain_size.ilog2() as usize - round.folding_factor)
        .collect::<Vec<_>>();
    heights.sort_unstable();
    heights.dedup();
    let mut dispatch = heights
        .iter()
        .enumerate()
        .map(|(index, height)| {
            let branch = if index == 0 { "if" } else { "elif" };
            format!("{branch} height == {height}:\n        {}", call(&height.to_string()))
        })
        .collect::<Vec<_>>();
    dispatch
        .push("else:\n        assert False, \"unsupported Merkle height for the fixed child dimension\"".to_string());
    dispatch.join("\n    ")
}

fn all_air_evals_in_zk_dsl(fft_poseidon_mds: bool) -> String {
    let mut res = String::new();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {});
    res += &air_eval_in_zk_dsl(ExtensionOpPrecompile::<false> {});
    if fft_poseidon_mds {
        res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false, true> {});
    } else {
        res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false> {});
    }
    res
}

const AIR_INNER_VALUES_VAR: &str = "inner_evals";

struct AirCodegenCtx {
    expr_cache: HashMap<SymbolicNodeRef<F>, String>,
    consts_cache: HashMap<Vec<u32>, String>,
    ef_const_cache: HashMap<u32, String>,
    ctr: Counter,
}

impl AirCodegenCtx {
    fn new() -> Self {
        Self {
            expr_cache: HashMap::new(),
            consts_cache: HashMap::new(),
            ef_const_cache: HashMap::new(),
            ctr: Counter::new(),
        }
    }

    fn write_base_constants(&mut self, values: &[u32], res: &mut String) -> String {
        if let Some(name) = self.consts_cache.get(values) {
            return name.clone();
        }
        let name = format!("bc_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = Array({})", name, values.len()));
        for (i, &c) in values.iter().enumerate() {
            res.push_str(&format!("\n    {}[{}] = {}", name, i, c));
        }
        self.consts_cache.insert(values.to_vec(), name.clone());
        name
    }

    fn write_embedded_constant(&mut self, c: u32, res: &mut String) -> String {
        if let Some(name) = self.ef_const_cache.get(&c) {
            return name.clone();
        }
        let name = format!("aux_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = embed_in_ef({})", name, c));
        self.ef_const_cache.insert(c, name.clone());
        name
    }
}

fn air_eval_in_zk_dsl<T: TableT>(table: T) -> String
where
    T::ExtraData: Default,
{
    let (constraints, bus_multiplicity, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
    // `bus_data`'s last entry is the domainsep (logup domain separation).
    let (bus_domainsep, bus_real_data) = bus_data.split_last().unwrap();
    let mut ctx = AirCodegenCtx::new();

    let mut res = format!(
        "def evaluate_air_constraints_table_{}({}, air_alpha_powers, logup_beta_eq_poly):\n",
        table.table().index(),
        AIR_INNER_VALUES_VAR
    );

    let n_constraints = constraints.len();
    res += &format!("\n    constraints_buf = Array(DIM * {})", n_constraints);
    for (index, constraint) in constraints.iter().enumerate() {
        let dest = format!("constraints_buf + {} * DIM", index);
        eval_air_constraint(*constraint, Some(&dest), &mut ctx, &mut res);
    }

    // first: bus data
    let multiplicity = eval_air_constraint(bus_multiplicity, None, &mut ctx, &mut res);
    res += &format!("\n    buff = Array(DIM * {})", bus_real_data.len());
    for (i, data) in bus_real_data.iter().enumerate() {
        let data_str = eval_air_constraint(*data, None, &mut ctx, &mut res);
        res += &format!("\n    copy_ef({}, buff + DIM * {})", data_str, i);
    }
    let domainsep_str = eval_air_constraint(*bus_domainsep, None, &mut ctx, &mut res);
    // bus_res = sum(buff[i] * logup_beta_eq_poly[i]) + disc * logup_beta_eq_poly.last()
    res += "\n    bus_res_init = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(buff, logup_beta_eq_poly, bus_res_init, {})",
        bus_real_data.len()
    );
    res += &format!(
        "\n    bus_res: Mut = add_extension_ret(mul_extension_ret({}, logup_beta_eq_poly + {} * DIM), bus_res_init)",
        domainsep_str,
        (1 << LOG_MAX_BUS_WIDTH) - 1
    );
    // `air_alpha_powers` is the slice [alpha^offset, alpha^{offset+1}, …] for this table.
    // Multiplicity → slot 0, bus fingerprint → slot 1, remaining AIR constraints → slot 2+.
    res += "\n    bus_res = mul_extension_ret(bus_res, air_alpha_powers + DIM)";
    res += &format!(
        "\n    weighted_multiplicity = mul_extension_ret(air_alpha_powers, {})",
        multiplicity
    );
    res += "\n    sum: Mut = add_extension_ret(bus_res, weighted_multiplicity)";

    res += "\n    weighted_constraints = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(air_alpha_powers + 2 * DIM, constraints_buf, weighted_constraints, {})",
        n_constraints
    );
    res += "\n    sum = add_extension_ret(sum, weighted_constraints)";

    res += "\n    return sum";
    res += "\n";
    res
}

fn eval_air_constraint(
    expr: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let v = match expr {
        SymbolicExpression::Constant(c) => ctx.write_embedded_constant(c.as_canonical_u32(), res),
        SymbolicExpression::Variable(v) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v.index),
        SymbolicExpression::Operation(idx) => {
            if let Some(v) = ctx.expr_cache.get(&idx) {
                v.clone()
            } else if let Some(v) = try_emit_dot_product_be(idx, dest, ctx, res) {
                ctx.expr_cache.insert(idx, v.clone());
                return v;
            } else {
                let node = *idx;
                let v = match node.op {
                    SymbolicOperation::Neg => {
                        let a = eval_air_constraint(node.lhs, None, ctx, res);
                        let v = format!("aux_{}", ctx.ctr.get_next());
                        res.push_str(&format!("\n    {} = opposite_extension_ret({})", v, a));
                        v
                    }
                    _ => eval_air_binary_op(node.op, node.lhs, node.rhs, dest, ctx, res),
                };
                ctx.expr_cache.insert(idx, v.clone());
                v
            }
        }
    };
    if let Some(d) = dest
        && v != d
    {
        res.push_str(&format!("\n    copy_ef({}, {})", v, d));
    }
    v
}

/// Detect `0 + c0*x0 + c1*x1 + ... + cn*xn` in the expression tree and emit
/// a single `dot_product_be` precompile call. Returns None if the pattern doesn't match.
fn try_emit_dot_product_be(
    idx: SymbolicNodeRef<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> Option<String> {
    // Walk the left-spine of Add(_, Mul(Const, _)) nodes down to Constant(ZERO).
    let mut constants = Vec::new();
    let mut operands = Vec::new();
    let mut current = SymbolicExpression::<F>::Operation(idx);
    loop {
        match current {
            SymbolicExpression::Constant(c) if c == F::ZERO && constants.len() >= 2 => break,
            SymbolicExpression::Operation(op_idx) => {
                if op_idx != idx && ctx.expr_cache.contains_key(&op_idx) {
                    return None;
                }
                let node = *op_idx;
                if node.op != SymbolicOperation::Add {
                    return None;
                }
                let mul_idx = match node.rhs {
                    SymbolicExpression::Operation(i) => i,
                    _ => return None,
                };
                let mul = *mul_idx;
                if mul.op != SymbolicOperation::Mul {
                    return None;
                }
                let (c, expr) = match (mul.lhs, mul.rhs) {
                    (SymbolicExpression::Constant(c), o) | (o, SymbolicExpression::Constant(c)) => {
                        (c.as_canonical_u32(), o)
                    }
                    _ => return None,
                };
                constants.push(c);
                operands.push(expr);
                current = node.lhs;
            }
            _ => return None,
        }
    }
    constants.reverse();
    operands.reverse();
    let n = constants.len();

    let consts = ctx.write_base_constants(&constants, res);

    // Reuse an existing contiguous buffer if possible.
    let vals = try_find_contiguous_buffer(&operands, ctx).unwrap_or_else(|| {
        let buf = format!("dp_v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = Array(DIM * {})", buf, n));
        for (i, ext) in operands.iter().enumerate() {
            eval_air_constraint(*ext, Some(&format!("{} + DIM * {}", buf, i)), ctx, res);
        }
        buf
    });

    let dp_dest = dest.map_or_else(
        || {
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            v
        },
        |d| d.to_string(),
    );
    res.push_str(&format!(
        "\n    dot_product_be({}, {}, {}, {})",
        consts, vals, dp_dest, n
    ));
    Some(dp_dest)
}

/// Check whether every operand is already cached as consecutive slots in the
/// same buffer (`buf + DIM * 0`, `buf + DIM * 1`, …).
fn try_find_contiguous_buffer(operands: &[SymbolicExpression<F>], ctx: &AirCodegenCtx) -> Option<String> {
    let mut base: Option<&str> = None;
    for (i, op) in operands.iter().enumerate() {
        let idx = match op {
            SymbolicExpression::Operation(idx) => *idx,
            _ => return None,
        };
        let suffix = format!(" + DIM * {}", i);
        let this_base = ctx.expr_cache.get(&idx)?.strip_suffix(&suffix)?;
        match base {
            None => base = Some(this_base),
            Some(b) if b == this_base => {}
            _ => return None,
        }
    }
    base.map(|s| s.to_string())
}

fn eval_air_binary_op(
    op: SymbolicOperation,
    lhs: SymbolicExpression<F>,
    rhs: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let c0 = match lhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };
    let c1 = match rhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };

    match (c0, c1) {
        // Both extension
        (None, None) => {
            let a = eval_air_constraint(lhs, None, ctx, res);
            let b = eval_air_constraint(rhs, None, ctx, res);
            if let Some(d) = dest {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension",
                    SymbolicOperation::Add => "add_ee",
                    SymbolicOperation::Sub => "sub_extension",
                    _ => unreachable!(),
                };
                res.push_str(&format!("\n    {}({}, {}, {})", f, a, b, d));
                d.to_string()
            } else {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension_ret",
                    SymbolicOperation::Add => "add_extension_ret",
                    SymbolicOperation::Sub => "sub_extension_ret",
                    _ => unreachable!(),
                };
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, a, b));
                v
            }
        }
        // Mul/Add with a base-field constant
        _ if matches!(op, SymbolicOperation::Mul | SymbolicOperation::Add) => {
            let (c, ext_expr) = match (c0, c1) {
                (Some(c), _) => (c, rhs),
                (_, Some(c)) => (c, lhs),
                _ => unreachable!(),
            };
            let ext = eval_air_constraint(ext_expr, None, ctx, res);
            if let Some(d) = dest {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "dot_product_be"
                } else {
                    "add_be"
                };
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    {}({}, {}, {})", f, scalar, ext, d));
                d.to_string()
            } else {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "mul_base_extension_ret"
                } else {
                    "add_base_extension_ret"
                };
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, c, ext));
                v
            }
        }
        // Sub: base - ext
        (Some(c), _) => {
            let ext = eval_air_constraint(rhs, None, ctx, res);
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = sub_base_extension_ret({}, {})", v, c, ext));
            v
        }
        // Sub: ext - base
        (_, Some(c)) => {
            let ext = eval_air_constraint(lhs, None, ctx, res);
            if let Some(d) = dest {
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    add_be({}, {}, {})", scalar, d, ext));
                d.to_string()
            } else {
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = sub_extension_base_ret({}, {})", v, ext, c));
                v
            }
        }
    }
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl(false));
}

#[test]
fn display_poseidon_air_in_zk_dsl() {
    println!("{}", air_eval_in_zk_dsl(Poseidon16Precompile::<false> {}));
}

#[test]
fn fixed_dimension_limits_generated_whir_geometry() {
    let profile = WhirExecutionProfile {
        security_bits: 100,
        grinding_bits: 24,
        first_folding_factor: 5,
        subsequent_folding_factor: 4,
        rs_domain_initial_reduction_factor: 1,
        max_num_variables_to_send_coeffs: 3,
        log_inv_rate: 4,
    };
    let replacements = build_replacements_for_dimension(
        18,
        F::ZERO,
        Some(&profile),
        RecursiveVerifierOptions::default(),
        Some(23),
    );
    assert_eq!(replacements["MIN_STACKED_N_VARS_PLACEHOLDER"], "23");
    assert_eq!(replacements["MAX_STACKED_N_VARS_BY_RATE_PLACEHOLDER"], "[23]");
    assert_eq!(replacements["WHIR_VALID_DIMENSIONS_PLACEHOLDER"], "[[1]]");
    assert_eq!(replacements["MIN_FINAL_WHIR_VARS_PLACEHOLDER"], "2");
    assert_eq!(replacements["MAX_FINAL_WHIR_VARS_PLACEHOLDER"], "2");
    let dispatch = &replacements["WHIR_MERKLE_HEIGHT_DISPATCH_PLACEHOLDER"];
    for height in 0..=24 {
        assert_eq!(
            dispatch.contains(&format!("height == {height}:")),
            (19..=22).contains(&height)
        );
    }
}

#[test]
#[should_panic(expected = "invalid recursive child dimension")]
fn fixed_dimension_rejects_invalid_profile_geometry_before_compilation() {
    build_replacements_for_dimension(
        8,
        F::ZERO,
        Some(&WhirExecutionProfile::security_100(1)),
        RecursiveVerifierOptions::default(),
        Some(17),
    );
}

#[test]
fn explicit_dimension_dispatch_rejects_derived_grinding_above_budget() {
    let profile = WhirExecutionProfile {
        security_bits: 121,
        grinding_bits: 16,
        first_folding_factor: 3,
        subsequent_folding_factor: 3,
        rs_domain_initial_reduction_factor: 1,
        max_num_variables_to_send_coeffs: 2,
        log_inv_rate: 1,
    };
    assert!(profile.validate_for_n_vars(18).is_ok());
    assert!(profile.validate_for_n_vars(26).is_err());
    let replacements = build_replacements_with_profile(8, F::ZERO, Some(&profile), RecursiveVerifierOptions::default());
    // Exercise the same generated validity table and constrained constant-index
    // dispatch used by the WHIR query/OOD/grinding accessors.
    let source = ProgramSource::Raw(
        r#"
MIN_STACKED_N_VARS = MIN_STACKED_N_VARS_PLACEHOLDER
WHIR_VALID_DIMENSIONS = WHIR_VALID_DIMENSIONS_PLACEHOLDER

def main():
    public = 0
    match_range(public[0], range(MIN_STACKED_N_VARS, 27), lambda n: check_dimension(n, public[0]))
    return

def check_dimension(n: Const, observed_n_vars):
    assert observed_n_vars == n * WHIR_VALID_DIMENSIONS[0][n - MIN_STACKED_N_VARS]
    return
"#
        .to_string(),
    );
    let bytecode = compile_program_with_flags(&source, CompilationFlags { replacements });
    let mut input = [F::ZERO; PUBLIC_INPUT_LEN];
    input[0] = F::from_usize(18);
    assert!(try_execute_bytecode(&bytecode, &input, &ExecutionWitness::default(), false).is_ok());
    input[0] = F::from_usize(26);
    assert!(try_execute_bytecode(&bytecode, &input, &ExecutionWitness::default(), false).is_err());
}

#[test]
fn horner_matches_extension_polynomials_and_removes_two_operations() {
    let utilities = EMBEDDED_ZK_DSL.get_file("utils.py").unwrap().contents_utf8().unwrap();
    let utilities = [
        "univariate_polynomial_eval",
        "powers_const",
        "copy_ef",
        "set_to_one",
        "mul_extension",
        "mul_extension_ret",
    ]
    .into_iter()
    .map(|name| {
        let start = utilities.find(&format!("def {name}(")).unwrap();
        let mut lines = utilities[start..].lines();
        let signature = lines.next().unwrap();
        let body = lines
            .take_while(|line| line.is_empty() || line.starts_with(' '))
            .collect::<Vec<_>>()
            .join("\n");
        let decorator = if utilities[..start].ends_with("@inline\n") {
            "@inline\n"
        } else {
            ""
        };
        format!("{decorator}{signature}\n{body}")
    })
    .collect::<Vec<_>>()
    .join("\n\n");
    for degree in 0..=11 {
        let point = EF::from_basis_coefficients_fn(|index| F::from_usize(index + 3));
        let coefficients: Vec<EF> = (0..=degree)
            .map(|index| EF::from_basis_coefficients_fn(|basis| F::from_usize((index + 1) * (basis + 2) + 5)))
            .collect();
        let expected = coefficients
            .iter()
            .rev()
            .fold(EF::ZERO, |acc, coefficient| acc * point + *coefficient);
        let mut operation_counts = Vec::new();
        for horner in [false, true] {
            let source = format!(
                r#"
DIM = 5
ONE_EF_PTR = 8
UNIVARIATE_EVAL_HORNER = UNIVARIATE_EVAL_HORNER_PLACEHOLDER
DEGREE = {degree}
{utilities}

def main():
    one = ONE_EF_PTR
    one[0] = 1
    for i in unroll(1, DIM):
        one[i] = 0
    coefficients = Array((DEGREE + 1) * DIM)
    point = Array(DIM)
    expected = Array(DIM)
    hint_witness("coefficients", coefficients)
    hint_witness("point", point)
    hint_witness("expected", expected)
    actual = univariate_polynomial_eval(coefficients, point, DEGREE)
    copy_ef(actual, expected)
    return
"#
            );
            let flags = CompilationFlags {
                replacements: BTreeMap::from([(
                    "UNIVARIATE_EVAL_HORNER_PLACEHOLDER".to_string(),
                    usize::from(horner).to_string(),
                )]),
            };
            let bytecode = compile_program_with_flags(&ProgramSource::Raw(source), flags);
            let mut hints = Hints::default();
            hints.insert(
                &bytecode,
                "coefficients",
                arena_vec![ArenaVec::from_slice(&flatten_scalars_to_base::<F, EF>(&coefficients))],
            );
            hints.insert(
                &bytecode,
                "point",
                arena_vec![ArenaVec::from_slice(point.as_basis_coefficients_slice())],
            );
            hints.insert(
                &bytecode,
                "expected",
                arena_vec![ArenaVec::from_slice(expected.as_basis_coefficients_slice())],
            );
            let witness = ExecutionWitness {
                preamble_memory_len: DIMENSION,
                hints,
                min_table_log_n_rows: BTreeMap::new(),
            };
            let result = try_execute_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], &witness, false).unwrap();
            operation_counts.push(result.metadata.n_extension_ops);
        }
        assert_eq!(operation_counts[0], operation_counts[1] + 2, "degree {degree}");
    }
}

#[test]
fn recursive_gkr_division_rejects_preassigned_zero_denominators() {
    let utilities = EMBEDDED_ZK_DSL.get_file("utils.py").unwrap().contents_utf8().unwrap();
    let utilities = ["div_extension", "div_extension_nonzero"]
        .into_iter()
        .map(|name| {
            let start = utilities.find(&format!("def {name}(")).unwrap();
            let mut lines = utilities[start..].lines();
            let signature = lines.next().unwrap();
            let body = lines
                .take_while(|line| line.is_empty() || line.starts_with(' '))
                .collect::<Vec<_>>()
                .join("\n");
            format!("@inline\n{signature}\n{body}")
        })
        .collect::<Vec<_>>()
        .join("\n\n");
    let recursion = EMBEDDED_ZK_DSL
        .get_file("recursion.py")
        .unwrap()
        .contents_utf8()
        .unwrap();
    let start = recursion.find("    initial_quotients = Array(").unwrap();
    let end = start + recursion[start..].find("    debug_assert(").unwrap();
    // Exercise the production GKR loop, with every quotient supplied by the adversary.
    let gkr_divisions = recursion[start..end].replace(
        "    for k in unroll(",
        "    hint_witness(\"quotients\", initial_quotients)\n    for k in unroll(",
    );
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let compile = |strict: bool, preassign_inverse: bool| {
        let utilities = if preassign_inverse {
            utilities.replace(
                "    inverse = Array(DIM)",
                "    inverse = Array(DIM)\n    hint_witness(\"inverse\", inverse)",
            )
        } else {
            utilities.clone()
        };
        let divisions = if strict {
            gkr_divisions.clone()
        } else {
            gkr_divisions.replace("div_extension_nonzero(", "div_extension(")
        };
        lean_compiler::compile_program(&ProgramSource::Raw(format!(
            r#"
DIM = 5
ONE_EF_PTR = 8
LOGUP_GKR_N_COEFFS_SENT = {send_len}
{utilities}

def main():
    one = ONE_EF_PTR
    one[0] = 1
    for i in unroll(1, DIM):
        one[i] = 0
    nums = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    denoms = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    hint_witness("numerators", nums)
    hint_witness("denominators", denoms)
{divisions}
    return
"#
        )))
    };
    let run = |bytecode: &Bytecode, numerators: &[EF], denominators: &[EF], quotients: &[EF], inverses: &[EF]| {
        let mut hints = Hints::default();
        for (name, values) in [
            ("numerators", numerators),
            ("denominators", denominators),
            ("quotients", quotients),
        ] {
            hints.insert(
                bytecode,
                name,
                arena_vec![ArenaVec::from_slice(&flatten_scalars_to_base::<F, EF>(values))],
            );
        }
        if bytecode.has_hint("inverse") {
            hints.insert(
                bytecode,
                "inverse",
                inverses
                    .iter()
                    .map(|value| ArenaVec::from_slice(value.as_basis_coefficients_slice()))
                    .collect(),
            );
        }
        let witness = ExecutionWitness {
            preamble_memory_len: DIMENSION,
            hints,
            min_table_log_n_rows: BTreeMap::new(),
        };
        try_execute_bytecode(bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], &witness, false)
    };
    let strict = compile(true, true);
    let honest_solver = compile(true, false);
    let unchecked = compile(false, false);
    let denominators: Vec<EF> = (0..send_len)
        .map(|i| EF::from_basis_coefficients_fn(|j| F::from_usize(i + j + 2)))
        .collect();
    let quotients: Vec<EF> = (0..send_len)
        .map(|i| EF::from_basis_coefficients_fn(|j| F::from_usize(i * (j + 1))))
        .collect();
    let numerators: Vec<EF> = denominators.iter().zip(&quotients).map(|(&d, &q)| d * q).collect();
    let inverses: Vec<EF> = denominators.iter().map(|d| d.inverse()).collect();
    for code in [&strict, &honest_solver] {
        let execution = run(code, &numerators, &denominators, &quotients, &inverses).unwrap();
        assert_eq!(execution.metadata.n_extension_ops, 2 * send_len);
        let mut wrong_quotients = quotients.clone();
        wrong_quotients[send_len - 1] += EF::ONE;
        assert!(matches!(
            run(code, &numerators, &denominators, &wrong_quotients, &inverses),
            Err(RunnerError::InvalidExtensionOp)
        ));
    }
    for position in 0..send_len {
        for fake_inverse in [EF::ZERO, EF::TWO] {
            let mut numerators = numerators.clone();
            let mut denominators = denominators.clone();
            let mut inverses = inverses.clone();
            numerators[position] = EF::ZERO;
            denominators[position] = EF::ZERO;
            inverses[position] = fake_inverse;
            // The old multiplication relation accepts 0/0 with the preassigned quotient.
            run(&unchecked, &numerators, &denominators, &quotients, &inverses).unwrap();
            // Both operands and the result of the inverse constraint are defined. This
            // must fail the equation itself, rather than the witness solver's inversion.
            assert!(matches!(
                run(&strict, &numerators, &denominators, &quotients, &inverses),
                Err(RunnerError::InvalidExtensionOp)
            ));
        }
    }
}

#[test]
fn recursive_whir_continuation_uses_distinct_powers() {
    let extract = |file: &str, names: &[&str]| {
        let source = EMBEDDED_ZK_DSL.get_file(file).unwrap().contents_utf8().unwrap();
        names
            .iter()
            .map(|name| {
                let start = source.find(&format!("def {name}(")).unwrap();
                let mut lines = source[start..].lines();
                let signature = lines.next().unwrap();
                let body = lines
                    .take_while(|line| line.is_empty() || line.starts_with(' '))
                    .collect::<Vec<_>>()
                    .join("\n");
                let decorator = if source[..start].ends_with("@inline\n") {
                    "@inline\n"
                } else {
                    ""
                };
                format!("{decorator}{signature}\n{body}")
            })
            .collect::<Vec<_>>()
            .join("\n\n")
    };
    let utilities = extract(
        "utils.py",
        &["powers", "powers_const", "copy_ef", "set_to_one", "mul_extension"],
    );
    let continuation = extract("whir.py", &["whir_continuation_powers"]);
    // The largest admitted query/OOD total is 399; its shifted list needs power 399.
    for count in [1, 3, 399] {
        let bytecode = lean_compiler::compile_program(&ProgramSource::Raw(format!(
            r#"
DIM = 5
ONE_EF_PTR = 8
{utilities}
{continuation}

def main():
    one = ONE_EF_PTR
    one[0] = 1
    for i in unroll(1, DIM):
        one[i] = 0
    gamma = Array(DIM)
    expected = Array({count} * DIM)
    hint_witness("gamma", gamma)
    hint_witness("expected", expected)
    coefficients = whir_continuation_powers(gamma, {count})
    for i in unroll(0, {count}):
        copy_ef(coefficients + i * DIM, expected + i * DIM)
    return
"#
        )));
        let run = |gamma: EF, shifted: bool| {
            let expected: Vec<_> = gamma.powers().skip(usize::from(shifted)).take(count).collect();
            let mut hints = Hints::default();
            hints.insert(
                &bytecode,
                "gamma",
                arena_vec![ArenaVec::from_slice(gamma.as_basis_coefficients_slice())],
            );
            hints.insert(
                &bytecode,
                "expected",
                arena_vec![ArenaVec::from_slice(&flatten_scalars_to_base::<F, EF>(&expected))],
            );
            try_execute_bytecode(
                &bytecode,
                &[F::ZERO; PUBLIC_INPUT_LEN],
                &ExecutionWitness {
                    preamble_memory_len: DIMENSION,
                    hints,
                    min_table_log_n_rows: BTreeMap::new(),
                },
                false,
            )
        };
        for gamma in [
            EF::ZERO,
            EF::ONE,
            EF::TWO,
            EF::from_basis_coefficients_fn(|i| F::from_usize(i + 2)),
        ] {
            assert!(run(gamma, true).is_ok());
            if gamma != EF::ONE {
                assert!(run(gamma, false).is_err());
            }
        }
    }
}

#[test]
fn recursive_grinding_checks_all_thirty_canonical_low_bits() {
    let source = EMBEDDED_ZK_DSL
        .get_file("fiat_shamir.py")
        .unwrap()
        .contents_utf8()
        .unwrap();
    let start = source.find("def assert_trailing_bits_are_zeros(").unwrap();
    let mut lines = source[start..].lines();
    let signature = lines.next().unwrap();
    let body = lines
        .take_while(|line| line.is_empty() || line.starts_with(' '))
        .collect::<Vec<_>>()
        .join("\n");
    for bits in [1, 11, 12, 23, 24, 25, 26, 27, 28, 29, 30] {
        let bytecode = lean_compiler::compile_program(&ProgramSource::Raw(format!(
            "{signature}\n{body}\n\ndef main():\n    public = 0\n    assert_trailing_bits_are_zeros(public[0], {bits})\n    return\n"
        )));
        let mask = (1u32 << bits) - 1;
        let modulus = F::ORDER_U32;
        for value in [0, 1, 1 << bits, mask, modulus - 1, modulus - 2, (modulus - 1) & !mask] {
            let mut input = [F::ZERO; PUBLIC_INPUT_LEN];
            input[0] = F::from_u32(value);
            assert_eq!(
                try_execute_bytecode(&bytecode, &input, &ExecutionWitness::default(), false).is_ok(),
                value & mask == 0,
                "bits={bits}, value={value}"
            );
        }
    }
}

#[test]
fn recursive_grinding_refreshes_samples_and_matches_native() {
    let extract = |file: &str, names: &[&str]| {
        let source = EMBEDDED_ZK_DSL.get_file(file).unwrap().contents_utf8().unwrap();
        names
            .iter()
            .map(|name| {
                let start = source.find(&format!("def {name}(")).unwrap();
                let mut lines = source[start..].lines();
                let signature = lines.next().unwrap();
                let body = lines
                    .take_while(|line| line.is_empty() || line.starts_with(' '))
                    .collect::<Vec<_>>()
                    .join("\n");
                let decorator = if source[..start].ends_with("@inline\n") {
                    "@inline\n"
                } else {
                    ""
                };
                format!("{decorator}{signature}\n{body}")
            })
            .collect::<Vec<_>>()
            .join("\n\n")
    };
    let utilities = extract("utils.py", &["copy_8", "set_to_8_zeros"]);
    let transcript = extract(
        "fiat_shamir.py",
        &[
            "fs_new",
            "_absorb_chunks",
            "fs_grinding",
            "assert_trailing_bits_are_zeros",
            "fs_duplex",
            "fs_sample_ef",
        ],
    );
    let bytecode = lean_compiler::compile_program(&ProgramSource::Raw(format!(
        r#"
DIGEST_LEN = 8
DIM = 5
ZERO_VEC_PTR = 8
ONE_EF_PTR = 16
{utilities}
{transcript}

def main():
    public = 0
    zero = ZERO_VEC_PTR
    for i in unroll(0, 8):
        zero[i] = 0
    one = ONE_EF_PTR
    one[0] = 1
    for i in unroll(1, DIM):
        one[i] = 0
    capacity = Array(8)
    transcript = Array(8)
    expected = Array(16)
    hint_witness("capacity", capacity)
    hint_witness("transcript", transcript)
    hint_witness("expected", expected)
    initial = fs_new(transcript, capacity)
    fs = fs_duplex(initial)
    result = fs_grinding(fs, public[0])
    for i in unroll(0, 16):
        assert result[i] == expected[i]
    if public[0] == 0:
        assert result[16] == transcript
    else:
        assert result[16] == transcript + DIGEST_LEN
    sampled_fs, sampled = fs_sample_ef(result)
    for i in unroll(0, DIM):
        assert sampled[i] == expected[8 + i]
    return
"#
    )));
    let run = |capacity: &[F; 8], nonce: F, bits: usize, expected: &[F; 16]| {
        let mut raw = [F::ZERO; 8];
        raw[0] = nonce;
        let mut hints = Hints::default();
        for (name, values) in [
            ("capacity", capacity.as_slice()),
            ("transcript", raw.as_slice()),
            ("expected", expected.as_slice()),
        ] {
            hints.insert(&bytecode, name, arena_vec![ArenaVec::from_slice(values)]);
        }
        let mut public = [F::ZERO; PUBLIC_INPUT_LEN];
        public[0] = F::from_usize(bits);
        try_execute_bytecode(
            &bytecode,
            &public,
            &ExecutionWitness {
                preamble_memory_len: 13,
                hints,
                min_table_log_n_rows: BTreeMap::new(),
            },
            false,
        )
    };
    let native = |capacity, nonce, bits| {
        let mut transcript = ProverState::<EF, _>::new(get_poseidon16().clone(), capacity);
        if bits != 0 {
            transcript.add_base_scalars(&[nonce]);
        }
        let mut verifier =
            VerifierState::<EF, _>::new(transcript.into_proof(), get_poseidon16().clone(), capacity).unwrap();
        verifier.duplex();
        (verifier.check_pow_grinding(bits), verifier)
    };
    for seed in 0..8 {
        let capacity = std::array::from_fn(|i| F::from_usize(seed * 8 + i + 1));
        let mut initial = [F::ZERO; 16];
        initial[..8].copy_from_slice(&capacity);
        let initial = poseidon16_permute(initial);
        let checked_state = |nonce| {
            let mut state = initial;
            state[8..].fill(F::ZERO);
            state[8] = F::from_usize(nonce);
            poseidon16_permute(state)
        };
        let (nonce, checked, fresh) = (0..4096)
            .find_map(|nonce| {
                let checked = checked_state(nonce);
                let mut refresh = checked;
                refresh[8..].fill(F::ZERO);
                let fresh = poseidon16_permute(refresh);
                (checked[8].as_canonical_u64() & 15 == 0 && fresh[8].as_canonical_u64() & 15 != 0).then_some((
                    F::from_usize(nonce),
                    checked,
                    fresh,
                ))
            })
            .expect("deterministic nonce search exhausted");
        let (result, mut verifier) = native(capacity, nonce, 4);
        result.unwrap();
        assert_eq!(verifier.sample(), EF::from_basis_coefficients_fn(|i| fresh[8 + i]));
        verifier.check_fully_consumed().unwrap();
        let (result, mut queries) = native(capacity, nonce, 4);
        result.unwrap();
        assert_eq!(
            queries.sample_in_range(8, 8),
            fresh[8..]
                .iter()
                .map(|x| x.as_canonical_u64() as usize & 255)
                .collect::<Vec<_>>()
        );
        assert_eq!(run(&capacity, nonce, 4, &fresh).unwrap().metadata.n_poseidons, 3);
        // A passing nonce constrains the old rate, but not the next challenge.
        // Pin rejection of the former transcript transition, not just an honest round trip.
        assert!(run(&capacity, nonce, 4, &checked).is_err());
        let bad_nonce = F::from_usize(
            (0..256)
                .find(|&n| checked_state(n)[8].as_canonical_u64() & 15 != 0)
                .unwrap(),
        );
        assert!(matches!(
            native(capacity, bad_nonce, 4).0,
            Err(ProofError::InvalidGrindingWitness)
        ));
        assert!(run(&capacity, bad_nonce, 4, &fresh).is_err());
        let (result, mut zero_work) = native(capacity, F::ZERO, 0);
        result.unwrap();
        assert_eq!(zero_work.sample(), EF::from_basis_coefficients_fn(|i| initial[8 + i]));
        assert!(zero_work.into_raw_proof().transcript.is_empty());
        assert_eq!(run(&capacity, F::ZERO, 0, &initial).unwrap().metadata.n_poseidons, 1);
    }
}
