//! Experimental terminal argument. The public entry points select this mode
//! explicitly; the ordinary recursive and two-commitment proofs keep their format.
use crate::prove_execution::TwoCommitmentWhirProverState;
use crate::verify_execution::ProofVerificationDetails;
use crate::*;
use std::collections::BTreeMap;
use sub_protocols::grouped_logup::*;
use sub_protocols::*;

pub const GROUPED_BATCHING_POW_BITS: usize = 4;

/// Version, maximum group width, commitment count, extension dimension,
/// maximum sumcheck degree and initial batching work are part of the mode.
pub fn grouped_logup_mode_observation() -> [F; 8] {
    [0x474c_5531, 1, 8, 3, DIMENSION, 11, GROUPED_BATCHING_POW_BITS, 0].map(F::from_usize)
}

fn fixed_program_offset(n_vars: usize, bytecode: &Bytecode, prefix: &[EF]) -> Result<usize, &'static str> {
    if bytecode.cumulated_n_vars().checked_add(prefix.len()) != Some(n_vars) {
        return Err("fixed execution program has the wrong dimension");
    }
    let mut selector = 0usize;
    for &bit in prefix {
        if bit != EF::ZERO && bit != EF::ONE {
            return Err("fixed execution program selector must be Boolean");
        }
        selector = 2 * selector + usize::from(bit == EF::ONE);
    }
    selector
        .checked_shl(bytecode.cumulated_n_vars() as u32)
        .ok_or("fixed execution program offset overflow")
}

fn pcs_layout(
    n_vars: usize,
    memory_log: usize,
    bytecode: &Bytecode,
    prefix: &[EF],
) -> Result<GroupedPcsLayout, &'static str> {
    Ok(GroupedPcsLayout {
        primary_n_vars: n_vars,
        fixed_n_vars: n_vars,
        helper_n_vars: n_vars,
        memory_log,
        bytecode_log: bytecode.log_size(),
        fixed_bytecode_offset: fixed_program_offset(n_vars, bytecode, prefix)?,
        ending_pc: bytecode.ending_pc(),
    })
}

fn public_statement(n_vars: usize, selector: usize, values: &[F], point: Vec<EF>) -> SparseStatement<EF> {
    let point = MultilinearPoint(point);
    let value = values.evaluate(&point);
    SparseStatement::new(n_vars, point, vec![SparseValue::new(selector, value)])
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_grouped_tail(
    prover: &mut impl FSProver<EF>,
    whir: &WhirConfig<EF>,
    n_vars: usize,
    primary: MleOwned<EF>,
    primary_witness: Witness<EF>,
    secondary: TwoCommitmentWhirProverState,
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    region: Option<&PublicMemoryRegion>,
    memory: ArenaVec<F>,
    memory_acc: ArenaVec<F>,
    bytecode_acc: ArenaVec<F>,
    traces: BTreeMap<Table, TableTrace>,
    gamma: EF,
    lookup_beta: &[EF],
) -> Result<(), ProverError> {
    let pcs = pcs_layout(
        n_vars,
        log2_strict_usize(memory.len()),
        bytecode,
        &secondary.execution_bytecode_point_prefix,
    )
    .map_err(ProverError::InvalidGroupedLogup)?;
    let beta = eval_eq(lookup_beta).to_vec();
    let inputs = GroupedInputs {
        memory: &memory,
        memory_acc: &memory_acc,
        bytecode: bytecode.instructions_multilinear(),
        bytecode_acc: &bytecode_acc,
        traces: &traces,
    };
    let witness = tracing::info_span!("Grouped inverse helpers")
        .in_scope(|| GroupedWitness::build(&inputs, gamma, &beta))
        .map_err(|_| ProverError::InvalidGroupedLogup("helper construction failed"))?;
    let layout = witness.layout.clone();
    if layout.helper_base_fields > 1 << n_vars {
        return Err(ProverError::InvalidGroupedLogup(
            "helper polynomial exceeds the shared WHIR domain",
        ));
    }
    let mut helper_values = witness.base_field_polynomial();
    helper_values.resize(1 << n_vars, F::ZERO);
    let helper = MleOwned::<EF>::Base(ArenaVec::from_iter(helper_values));
    let helper_witness = tracing::info_span!("Grouped helper commitment")
        .in_scope(|| whir.commit_without_ood(prover, &helper, layout.helper_base_fields));
    let height = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
    prover.duplex();
    let eq = prover.sample_vec(height);
    let alpha = prover.sample();
    let balance_weight = prover.sample();
    let mut sessions = tracing::info_span!("Grouped AIR sessions")
        .in_scope(|| grouped_sessions(&inputs, &witness, gamma, &beta, &eq, alpha, balance_weight));
    drop(witness);
    drop(memory);
    drop(memory_acc);
    drop(bytecode_acc);
    drop(traces);
    let point =
        tracing::info_span!("Grouped AIR sumcheck").in_scope(|| prove_batched_air_sumcheck(prover, &mut sessions));
    let columns = sessions
        .chunks(2)
        .map(|pair| {
            let evals = pair[0].final_column_evals();
            debug_assert_eq!(evals, pair[1].final_column_evals());
            evals
        })
        .collect::<Vec<_>>();
    let claims = GroupedFinalClaims::from_column_evals(&layout, &columns, &beta)
        .map_err(|_| ProverError::InvalidGroupedLogup("final grouped columns have the wrong layout"))?;
    drop(sessions);
    drop(columns);
    claims.observe_prover(prover);
    let mut public = vec![public_statement(
        n_vars,
        0,
        public_input,
        prover.sample_vec(log2_strict_usize(PUBLIC_INPUT_LEN)),
    )];
    if let Some(region) = region {
        public.push(public_statement(
            n_vars,
            region.selector(),
            &region.values,
            prover.sample_vec(region.num_variables()),
        ));
    }
    let groups = grouped_pcs_statements(
        &layout,
        &claims,
        &point.0,
        lookup_beta,
        &pcs,
        public,
        secondary.secondary_statements,
    )
    .map_err(|_| ProverError::InvalidGroupedLogup("grouped opening statements have the wrong layout"))?;
    let refs = [
        primary.by_ref(),
        secondary.secondary_polynomial.by_ref(),
        helper.by_ref(),
    ];
    whir.prove_three_commitments(
        prover,
        GROUPED_BATCHING_POW_BITS,
        groups,
        [primary_witness, secondary.secondary_witness, helper_witness],
        refs.each_ref(),
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn verify_grouped_tail(
    verifier: &mut impl FSVerifier<EF>,
    whir: &WhirConfig<EF>,
    primary: ParsedCommitment<F, EF>,
    fixed: ParsedCommitment<F, EF>,
    input: TwoCommitmentWhirVerifierInput,
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    region: Option<&PublicMemoryRegion>,
    memory_log: usize,
    heights: &BTreeMap<Table, usize>,
    gamma: EF,
    lookup_beta: &[EF],
) -> ProofResult<ProofVerificationDetails> {
    let n_vars = primary.num_variables;
    let pcs = pcs_layout(n_vars, memory_log, bytecode, &input.execution_bytecode_point_prefix)
        .map_err(|_| ProofError::InvalidProof)?;
    let layout = GroupedLayout::new(memory_log, bytecode.log_size(), heights);
    if layout.helper_base_fields > 1 << n_vars {
        return Err(ProofError::InvalidProof);
    }
    let beta = eval_eq_sequential(lookup_beta).to_vec();
    let helper = whir.parse_commitment_without_ood::<F>(verifier)?;
    let height = layout.sections.iter().map(|s| s.log_n_rows).max().unwrap();
    verifier.duplex();
    let eq = verifier.sample_vec(height);
    let alpha = verifier.sample();
    let balance_weight = verifier.sample();
    let evaluation = sumcheck_verify(verifier, height, 11, EF::ZERO, None)?;
    let claims = GroupedFinalClaims::read_verifier(&layout, verifier)?;
    if claims
        .evaluate(&layout, gamma, &beta, &eq, alpha, balance_weight, &evaluation.point.0)
        .map_err(|_| ProofError::InvalidProof)?
        != evaluation.value
    {
        return Err(ProofError::InvalidProof);
    }
    let mut public = vec![public_statement(
        n_vars,
        0,
        public_input,
        verifier.sample_vec(log2_strict_usize(PUBLIC_INPUT_LEN)),
    )];
    if let Some(region) = region {
        public.push(public_statement(
            n_vars,
            region.selector(),
            &region.values,
            verifier.sample_vec(region.num_variables()),
        ));
    }
    let groups = grouped_pcs_statements(
        &layout,
        &claims,
        &evaluation.point.0,
        lookup_beta,
        &pcs,
        public,
        input.secondary_statements,
    )
    .map_err(|_| ProofError::InvalidProof)?;
    // All eight program evaluations are authenticated below. The legacy
    // diagnostic interface returns the first of these already-verified claims.
    let index = layout
        .sections
        .iter()
        .position(|s| s.source == GroupedSource::Bytecode)
        .ok_or(ProofError::InvalidProof)?;
    let section = &layout.sections[index];
    let mut bytecode_point = vec![EF::ZERO; bytecode.log_size() - section.log_n_rows];
    bytecode_point.extend(natural_ordering_point_for_session(
        &evaluation.point.0,
        section.log_n_rows,
    ));
    bytecode_point.extend_from_slice(lookup_beta);
    let bytecode_evaluation = Evaluation {
        point: MultilinearPoint(bytecode_point),
        value: claims.sections[index][0],
    };
    whir.verify_three_commitments::<F>(verifier, GROUPED_BATCHING_POW_BITS, [&primary, &fixed, &helper], groups)?;
    Ok(ProofVerificationDetails {
        bytecode_evaluation,
        sorted_table_perm: sort_tables_by_height(heights)
            .into_iter()
            .map(|(t, _)| t.index())
            .collect(),
    })
}
