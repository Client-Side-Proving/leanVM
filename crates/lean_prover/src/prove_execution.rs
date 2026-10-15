use std::collections::BTreeMap;

use crate::*;
use backend::ArenaVec;
use backend::ansi::Colorize;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use sub_protocols::*;
use tracing::info_span;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

pub(crate) struct TwoCommitmentWhirProverState {
    pub(crate) secondary_polynomial: MleOwned<EF>,
    pub(crate) secondary_statements: Vec<SparseStatement<EF>>,
    pub(crate) execution_bytecode_point_prefix: Vec<EF>,
    pub(crate) two_commitment_batching_pow_bits: usize,
    pub(crate) secondary_witness: Witness<EF>,
}

/// Precompute the immutable fixed-program Merkle tree outside online terminal
/// proving. The returned root is the value supplied to the verifier as its
/// trusted secondary commitment.
pub fn preprocess_two_commitment_whir_secondary(
    polynomial: &MleOwned<EF>,
    secondary_actual_data_len: usize,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
) -> Result<TwoCommitmentWhirPreprocessedCommitment, ProverError> {
    profile
        .validate_for_hash(hash_profile)
        .map_err(ProverError::InvalidWhirProfile)?;
    let polynomial_ref = polynomial.by_ref();
    let polynomial_len = polynomial_ref.unpacked_len();
    if polynomial_len == 0 || !polynomial_len.is_power_of_two() {
        return Err(ProverError::InvalidTwoCommitmentWhir(
            "secondary polynomial length must be a non-zero power of two",
        ));
    }
    if polynomial_ref.as_base().is_none() && polynomial_ref.as_packed_base().is_none() {
        return Err(ProverError::InvalidTwoCommitmentWhir(
            "secondary polynomial must be base-field valued",
        ));
    }
    if secondary_actual_data_len == 0 || secondary_actual_data_len > polynomial_len {
        return Err(ProverError::InvalidTwoCommitmentWhir(
            "secondary actual data length is outside its polynomial domain",
        ));
    }
    let secondary_num_variables = log2_strict_usize(polynomial_len);
    profile
        .validate_for_n_vars(secondary_num_variables)
        .map_err(ProverError::InvalidWhirProfile)?;
    let (prover_data, root) = WhirConfig::new(&profile.whir_config(), secondary_num_variables)
        .build_commitment_data_with_hash_profile(polynomial, secondary_actual_data_len, hash_profile);
    Ok(TwoCommitmentWhirPreprocessedCommitment { prover_data, root })
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_inner(
        bytecode,
        public_input,
        witness,
        whir_config,
        None,
        ProofHashProfile::Poseidon1,
        None,
        None,
        false,
        vm_profiler,
    )
}

pub fn prove_execution_with_profile(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with_profile_and_hash(
        bytecode,
        public_input,
        witness,
        profile,
        ProofHashProfile::Poseidon1,
        vm_profiler,
    )
}

/// Select the terminal proof hash explicitly. Recursive Poseidon guests use the default entry point.
pub fn prove_execution_with_profile_and_hash(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with_profile_hash_and_public_memory(
        bytecode,
        public_input,
        witness,
        profile,
        hash_profile,
        None,
        vm_profiler,
    )
}

/// Bind an additional public memory slice selected by the application.
pub fn prove_execution_with_profile_hash_and_public_memory(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    public_memory_region: Option<&PublicMemoryRegion>,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    profile
        .validate_for_hash(hash_profile)
        .map_err(ProverError::InvalidWhirProfile)?;
    prove_execution_inner(
        bytecode,
        public_input,
        witness,
        &profile.whir_config(),
        Some(profile),
        hash_profile,
        public_memory_region,
        None,
        false,
        vm_profiler,
    )
}

/// Prove the terminal execution and a trusted fixed-program polynomial through
/// one two-commitment WHIR continuation.
#[allow(clippy::too_many_arguments)]
pub fn prove_execution_with_two_commitment_whir(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    public_memory_region: Option<&PublicMemoryRegion>,
    two_commitment_input: TwoCommitmentWhirProverInput,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with_fixed_programs(
        bytecode,
        public_input,
        witness,
        profile,
        hash_profile,
        public_memory_region,
        two_commitment_input,
        false,
        vm_profiler,
    )
}

/// Experimental grouped LogUp terminal mode with three Keccak commitments.
/// Reuses the fixed-program layout and public-memory binding input of C1.
#[allow(clippy::too_many_arguments)]
pub fn prove_execution_with_grouped_logup(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    public_memory_region: Option<&PublicMemoryRegion>,
    two_commitment_input: TwoCommitmentWhirProverInput,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    prove_execution_with_fixed_programs(
        bytecode,
        public_input,
        witness,
        profile,
        hash_profile,
        public_memory_region,
        two_commitment_input,
        true,
        vm_profiler,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_execution_with_fixed_programs(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    profile: &WhirExecutionProfile,
    hash_profile: ProofHashProfile,
    public_memory_region: Option<&PublicMemoryRegion>,
    two_commitment_input: TwoCommitmentWhirProverInput,
    grouped_logup: bool,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    if grouped_logup && hash_profile != ProofHashProfile::Keccak240 {
        return Err(ProverError::InvalidGroupedLogup(
            "grouped terminal proofs require Keccak240",
        ));
    }
    profile
        .validate_for_hash(hash_profile)
        .map_err(ProverError::InvalidWhirProfile)?;
    two_commitment_input
        .validate()
        .map_err(ProverError::InvalidTwoCommitmentWhir)?;
    let public_memory_region = public_memory_region.ok_or(ProverError::InvalidTwoCommitmentWhir(
        "two-commitment WHIR statements must be bound to public memory",
    ))?;
    crate::profile::validate_two_commitment_public_memory_binding(
        &public_memory_region.values,
        &two_commitment_input.secondary_statements,
        &two_commitment_input.secondary_statement_public_memory_bindings,
    )
    .map_err(ProverError::InvalidTwoCommitmentWhir)?;
    prove_execution_inner(
        bytecode,
        public_input,
        witness,
        &profile.whir_config(),
        Some(profile),
        hash_profile,
        Some(public_memory_region),
        Some(two_commitment_input),
        grouped_logup,
        vm_profiler,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_execution_inner(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    profile: Option<&WhirExecutionProfile>,
    hash_profile: ProofHashProfile,
    public_memory_region: Option<&PublicMemoryRegion>,
    two_commitment_input: Option<TwoCommitmentWhirProverInput>,
    grouped_logup: bool,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    if let Some(region) = public_memory_region {
        region.validate().map_err(ProverError::InvalidPublicMemory)?;
    }
    if profile.is_none() {
        check_rate(whir_config.starting_log_inv_rate).map_err(|_| ProverError::InvalidRate)?;
    }
    let ExecutionTrace {
        mut traces,
        mut memory, // padded with zeros to next power of two
        metadata,
    } = info_span!("Witness generation").in_scope(|| -> Result<_, ProverError> {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| try_execute_bytecode(bytecode, public_input, witness, vm_profiler))?;
        Ok(info_span!("Building execution trace")
            .in_scope(|| get_execution_trace(bytecode, execution_result, &witness.min_table_log_n_rows)))
    })?;

    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size
    // (required by the stacked polynomial ordering)
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    if let Some(region) = public_memory_region {
        region
            .check_witness(&memory)
            .map_err(ProverError::InvalidPublicMemory)?;
    }
    if let Some(profile) = profile {
        let max_height = traces
            .values()
            .map(|trace| trace.log_n_rows)
            .max()
            .unwrap()
            .max(bytecode.log_size());
        let entries = 2 * memory.len()
            + (1 << max_height)
            + traces
                .iter()
                .map(|(table, trace)| table.n_columns() * (1 << trace.log_n_rows))
                .sum::<usize>();
        profile
            .validate_for_n_vars(log2_ceil_usize(entries))
            .map_err(ProverError::InvalidWhirProfile)?;
    }
    let cap = match (&two_commitment_input, profile) {
        (Some(input), Some(profile)) => crate::profile::two_commitment_fiat_shamir_domain_sep(
            profile,
            bytecode,
            input
                .secondary_num_variables()
                .map_err(ProverError::InvalidTwoCommitmentWhir)?,
            input.secondary_actual_data_len,
            &input.secondary_statements,
            &input.secondary_statement_public_memory_bindings,
            &input.execution_bytecode_point_prefix,
            input.two_commitment_batching_pow_bits,
        ),
        (Some(_), None) => {
            return Err(ProverError::InvalidTwoCommitmentWhir(
                "two-commitment WHIR requires an explicit execution profile",
            ));
        }
        (None, profile) => profile.map_or_else(
            || fiat_shamir_domain_sep(bytecode),
            |profile| profile.fiat_shamir_domain_sep(bytecode),
        ),
    };
    let mut prover_state = ProverState::new_with_hash_profile(get_poseidon16().clone(), cap, hash_profile);
    if grouped_logup {
        prover_state.observe_scalars(&crate::grouped_logup_mode_observation());
    }
    prover_state.observe_scalars(public_input);
    if let Some(region) = public_memory_region {
        prover_state.observe_scalars(&region.transcript_header());
        prover_state.observe_scalars(&region.values);
    }
    if let Some(input) = &two_commitment_input {
        prover_state.observe_scalars(&two_commitment_statement_observation(&input.secondary_statements));
    }
    prover_state.add_base_scalars(
        &[
            vec![whir_config.starting_log_inv_rate, log2_strict_usize(memory.len())],
            traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
        ]
        .concat()
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );
    for (table, table_trace) in &traces {
        let log_n_rows = table_trace.log_n_rows;
        assert!(log_n_rows >= MIN_LOG_N_ROWS_PER_TABLE, "missing padding");
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
    }

    let mut table_log = String::new();
    for (table, trace) in &traces {
        table_log.push_str(&format!(
            "{}: 2^{} * (1 + {:.2}) rows | ",
            table.name(),
            trace.log_n_rows - 1,
            (trace.non_padded_n_rows as f64) / (1 << (trace.log_n_rows - 1)) as f64 - 1.0
        ));
    }
    table_log = table_log.trim_end_matches(" | ").to_string();
    tracing::info!("Trace tables sizes: {}", table_log.magenta());

    // TODO parrallelize
    let mut memory_acc = unsafe { ArenaVec::<F>::zeroed(memory.len()) };
    info_span!("Building memory access count").in_scope(|| -> Result<(), ProverError> {
        for (table, trace) in &traces {
            let buses = table.bus_interactions();
            for group in memory_lookup_groups(&buses) {
                let idx_col = &trace.columns[group.idx_col];
                let n = group.value_cols.len();
                for idx in idx_col {
                    let base = idx.to_usize();
                    let cells = memory_acc.get_mut(base..base + n).ok_or(RunnerError::OutOfMemory)?;
                    for cell in cells {
                        *cell += F::ONE;
                    }
                }
            }
        }
        Ok(())
    })?;

    // // TODO parrallelize
    let mut bytecode_acc = unsafe { ArenaVec::<F>::zeroed(bytecode.padded_size()) };
    info_span!("Building bytecode access count").in_scope(|| -> Result<(), ProverError> {
        for pc in traces[&Table::execution()].columns[EXEC_COL_PC].iter() {
            *bytecode_acc.get_mut(pc.to_usize()).ok_or(RunnerError::PCOutOfBounds)? += F::ONE;
        }
        Ok(())
    })?;

    // 1st Commitment
    let StackedPcsPolynomial {
        stacked_n_vars,
        actual_data_len: stacked_actual_data_len,
        global_polynomial,
    } = stack_polynomials(&memory, &memory_acc, &bytecode_acc, &traces);
    let whir = WhirConfig::new(whir_config, stacked_n_vars);
    let mut inner_witness = if two_commitment_input.is_some() {
        whir.commit_without_ood(&mut prover_state, &global_polynomial, stacked_actual_data_len)
    } else {
        whir.commit(&mut prover_state, &global_polynomial, stacked_actual_data_len)
    };
    let secondary_commitment = if let Some(input) = two_commitment_input {
        let secondary_n_vars = input.validate().map_err(ProverError::InvalidTwoCommitmentWhir)?;
        if secondary_n_vars != stacked_n_vars {
            return Err(ProverError::InvalidTwoCommitmentWhir(
                "primary and secondary polynomials must have the same number of variables",
            ));
        }
        let TwoCommitmentWhirProverInput {
            secondary_polynomial,
            secondary_actual_data_len: _,
            secondary_commitment,
            secondary_statements,
            secondary_statement_public_memory_bindings: _,
            execution_bytecode_point_prefix,
            two_commitment_batching_pow_bits,
        } = input;
        prover_state.add_base_scalars(&secondary_commitment.root);
        Some(TwoCommitmentWhirProverState {
            secondary_polynomial,
            secondary_statements,
            execution_bytecode_point_prefix,
            two_commitment_batching_pow_bits,
            secondary_witness: Witness {
                prover_data: secondary_commitment.prover_data,
                ood_points: Vec::new(),
                ood_answers: Vec::new(),
            },
        })
    } else {
        None
    };

    const REBUILD_COMMITMENT_MIN_VARS: usize = 28;
    let rebuild_commitment = secondary_commitment.is_none() && stacked_n_vars >= REBUILD_COMMITMENT_MIN_VARS;
    if rebuild_commitment {
        inner_witness.prover_data.discard_leaf();
    }

    // logup (GKR)
    let logup_c = prover_state.sample();
    prover_state.duplex();
    let logup_alphas = prover_state.sample_vec(LOG_MAX_BUS_WIDTH);
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    if grouped_logup {
        crate::grouped_execution::prove_grouped_tail(
            &mut prover_state,
            &whir,
            stacked_n_vars,
            global_polynomial,
            inner_witness,
            secondary_commitment.ok_or(ProverError::InvalidGroupedLogup("missing fixed commitment"))?,
            bytecode,
            public_input,
            public_memory_region,
            memory,
            memory_acc,
            bytecode_acc,
            traces,
            logup_c,
            &logup_alphas,
        )?;
        reset_pow_grinding_time();
        return Ok(ExecutionProof {
            proof: prover_state.into_proof(),
            metadata: Some(metadata),
        });
    }

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas,
        &logup_alphas_eq_poly,
        &memory,
        &memory_acc,
        bytecode.instructions_multilinear(),
        &bytecode_acc,
        &traces,
    );
    let memory_log_size = log2_strict_usize(memory.len());
    let public_memory = memory[..PUBLIC_INPUT_LEN].to_vec();
    drop(memory_acc);
    drop(bytecode_acc);
    drop(memory);
    let gkr_point = &logup_statements.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        let log_n_rows = traces[&table].log_n_rows;
        committed_statements.insert(
            table,
            vec![(
                MultilinearPoint(from_end(gkr_point, log_n_rows).to_vec()),
                logup_statements.columns_values[&table].clone(),
                BTreeMap::new(),
            )],
        );
    }

    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(total_air_constraints());

    let tables_log_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();

    let shifted_columns_span = info_span!("Computing shifted columns for AIR sumcheck").entered();
    let mut shifted_rows: Vec<Vec<ArenaVec<F>>> = ALL_TABLES
        .iter()
        .map(|table| {
            let columns: Vec<&[F]> = traces[table].columns[..table.n_columns()]
                .iter()
                .map(|c| c.as_slice())
                .collect();
            compute_shifted_columns(table.n_shift_columns(), &columns)
        })
        .collect();

    for (idx, table) in ALL_TABLES.iter().enumerate() {
        reorder_columns_for_air(&mut traces.get_mut(table).unwrap().columns[..table.n_columns()]);
        reorder_columns_for_air(&mut shifted_rows[idx]);
    }
    drop(shifted_columns_span);
    let mut sessions = Vec::with_capacity(ALL_TABLES.len());
    let mut alpha_offset = 0;
    for (idx, table) in ALL_TABLES.iter().enumerate() {
        let log_n_rows = tables_log_heights[table];
        let n_constraints = table.n_constraints();
        let bus_numerator_value = logup_statements.bus_numerators_values[table];
        let bus_denominator_value = logup_statements.bus_denominators_values[table];
        let signed_numerator = bus_numerator_value
            * match table.bus_interactions()[0].direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            };
        // Each table consumes a disjoint range of alpha powers; alpha^offset weights the bus
        // numerator (multiplicity), alpha^{offset+1} weights the bus fingerprint, alpha^{offset+2..}
        // weight the remaining AIR constraints.
        let bus_final_value = air_alpha_powers[alpha_offset] * signed_numerator
            + air_alpha_powers[alpha_offset + 1] * (logup_c - bus_denominator_value);

        let eq_suffix = from_end(gkr_point, log_n_rows).to_vec();

        let alpha_slice = air_alpha_powers[alpha_offset..alpha_offset + n_constraints].to_vec();
        let extra_data = ExtraDataForBuses::new(&logup_alphas_eq_poly, alpha_slice);

        let trace = traces.get_mut(table).unwrap();
        let mut owned_columns: Vec<ArenaVec<F>> = trace.columns.drain(..table.n_columns()).collect();
        owned_columns.append(&mut shifted_rows[idx]);

        let non_padded = traces[table].non_padded_n_rows;

        macro_rules! make_session {
            ($t:expr) => {{
                let session = AirSumcheckSession::new_owned_reordered(
                    owned_columns,
                    eq_suffix,
                    bus_final_value,
                    *$t,
                    extra_data,
                    non_padded,
                );
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        sessions.push(delegate_to_inner!(table => make_session));
        alpha_offset += n_constraints;
    }

    let sumcheck_air_point =
        info_span!("batched AIR sumcheck").in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions));

    for (idx, table) in ALL_TABLES.iter().enumerate() {
        let col_evals = sessions[idx].final_column_evals();
        prover_state.add_extension_scalars(&col_evals);

        let natural_ordering_point =
            natural_ordering_point_for_session(&sumcheck_air_point.0, traces[table].log_n_rows);
        macro_rules! split {
            ($t:expr) => {{ columns_evals_flat_and_shift($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(table => split);
        committed_statements.get_mut(table).unwrap().push(claim);
    }

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(PUBLIC_INPUT_LEN)));
    let public_memory_eval = public_memory.evaluate(&public_memory_random_point);

    let mut previous_statements = vec![
        SparseStatement::new(
            stacked_n_vars,
            logup_statements.memory_and_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_memory_acc),
            ],
        ),
        SparseStatement::new(
            stacked_n_vars,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
        SparseStatement::new(
            stacked_n_vars,
            logup_statements.bytecode_and_acc_point,
            vec![SparseValue::new(
                (2 * (1 << memory_log_size)) >> bytecode.log_size(),
                logup_statements.value_bytecode_acc,
            )],
        ),
    ];

    if let Some(region) = public_memory_region {
        let point = MultilinearPoint(prover_state.sample_vec(region.num_variables()));
        let value = region.values.evaluate(&point);
        previous_statements.push(SparseStatement::new(
            stacked_n_vars,
            point,
            vec![SparseValue::new(region.selector(), value)],
        ));
    }

    let global_statements_base = stacked_pcs_global_statements(
        stacked_n_vars,
        memory_log_size,
        bytecode.log_size(),
        bytecode.ending_pc(),
        previous_statements,
        &tables_log_heights,
        &committed_statements,
    );

    drop(sessions);
    drop(shifted_rows);
    drop(committed_statements);
    drop(traces);

    if let Some(mut secondary) = secondary_commitment {
        let bytecode_evaluation = logup_statements
            .bytecode_evaluation
            .as_ref()
            .expect("the prover derives the bytecode evaluation during LogUp");
        let mut point = std::mem::take(&mut secondary.execution_bytecode_point_prefix);
        point.extend_from_slice(&bytecode_evaluation.point.0);
        if point.len() != stacked_n_vars {
            return Err(ProverError::InvalidTwoCommitmentWhir(
                "execution bytecode claim does not fit the secondary polynomial layout",
            ));
        }
        secondary.secondary_statements.push(SparseStatement::dense(
            MultilinearPoint(point),
            bytecode_evaluation.value,
        ));
        whir.prove_two_commitments(
            &mut prover_state,
            secondary.two_commitment_batching_pow_bits,
            global_statements_base,
            inner_witness,
            &global_polynomial.by_ref(),
            secondary.secondary_statements,
            secondary.secondary_witness,
            &secondary.secondary_polynomial.by_ref(),
        );
    } else if rebuild_commitment {
        whir.prove_rebuilding_commitment_leaf(
            &mut prover_state,
            global_statements_base,
            inner_witness,
            global_polynomial,
            stacked_actual_data_len,
        );
    } else {
        whir.prove(
            &mut prover_state,
            global_statements_base,
            inner_witness,
            &global_polynomial.by_ref(),
        );
    }

    tracing::info!("total pow_grinding time: {} ms", pow_grinding_time().as_millis());
    reset_pow_grinding_time();

    Ok(ExecutionProof {
        proof: prover_state.into_proof(),
        metadata: Some(metadata),
    })
}
