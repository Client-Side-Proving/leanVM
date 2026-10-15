use std::ops::{Add, AddAssign, Mul};

use backend::*;

use crate::quotient_gkr::layers::unpack_and_unreverse_active;

pub(super) fn even_odd_split<T: Copy>(v: &[T]) -> (ArenaVec<T>, ArenaVec<T>) {
    (
        v.iter().step_by(2).copied().collect(),
        v.iter().skip(1).step_by(2).copied().collect(),
    )
}

#[derive(Clone, Copy, Default)]
struct RoundCoeffs<T: Copy> {
    c0_den: T,
    c2_den: T,
    c0_num: T,
    c2_num: T,
}

impl<T: Copy + Default> RoundCoeffs<T> {
    fn zero() -> Self {
        Self::default()
    }
}

impl<T: Copy + AddAssign> AddAssign for RoundCoeffs<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.c0_den += rhs.c0_den;
        self.c2_den += rhs.c2_den;
        self.c0_num += rhs.c0_num;
        self.c2_num += rhs.c2_num;
    }
}

impl<T: Copy + AddAssign> Add for RoundCoeffs<T> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self {
        self += rhs;
        self
    }
}

impl<T, W> Mul<W> for RoundCoeffs<T>
where
    T: Copy + Mul<W, Output = T>,
    W: Copy,
{
    type Output = Self;
    fn mul(self, w: W) -> Self {
        Self {
            c0_den: self.c0_den * w,
            c2_den: self.c2_den * w,
            c0_num: self.c0_num * w,
            c2_num: self.c2_num * w,
        }
    }
}

#[inline(always)]
fn pair_coeffs<T, N>(nl: (N, N), nr: (N, N), dl: (T, T), dr: (T, T)) -> RoundCoeffs<T>
where
    N: PrimeCharacteristicRing + Copy,
    T: Algebra<N> + Algebra<T> + Copy,
{
    let ddl = dl.1 - dl.0;
    let ddr = dr.1 - dr.0;
    let dnl = nl.1 - nl.0;
    let dnr = nr.1 - nr.0;
    RoundCoeffs {
        c0_den: dr.0 * dl.0,
        c2_den: ddl * ddr,
        c0_num: dr.0 * nl.0 + dl.0 * nr.0,
        c2_num: ddr * dnl + ddl * dnr,
    }
}

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
}

fn finalize_round<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    coeffs: RoundCoeffs<EFPacking<EF>>,
    alpha: EF,
    eq_alpha: EF,
    sum: &mut EF,
    mmf: &mut EF,
    padding_correction: EF,
) -> EF {
    let c0_raw: EF = (coeffs.c0_num + coeffs.c0_den * alpha).to_ext_lanes().sum::<EF>() + padding_correction;
    let c2_raw: EF = (coeffs.c2_num + coeffs.c2_den * alpha).to_ext_lanes().sum();
    let bare = build_bare_from_coeffs(c0_raw, c2_raw, eq_alpha, *sum, *mmf);
    prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
    let r = prover_state.sample();
    let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
    *sum = eq_eval * bare.evaluate(r);
    *mmf *= eq_eval;
    r
}

#[allow(clippy::too_many_arguments)]
pub(super) fn quotient_sumcheck_prove_packed_br_base<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    packed_nums: &[PFPacking<EF>],
    packed_dens: &[EFPacking<EF>],
    parent_chunk_log: usize,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log >= w + 3);
    debug_assert_eq!(packed_nums.len(), packed_dens.len());
    let active_chunks = (packed_nums.len() << w) >> parent_chunk_log;

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let outer_point = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = eval_eq(&outer_point);

    let padding_sum = alpha * mle_of_zeros_then_ones(active_chunks, &outer_point);

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let coeffs_0 = compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        coeffs_0,
        alpha,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r0);
    remaining_eq.pop();

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (nums_ext, dens_ext, coeffs_1) =
        fold_and_compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, r0, &eq_outer, &eq_within_1);
    let r1 = finalize_round(
        prover_state,
        coeffs_1,
        alpha,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r1);
    remaining_eq.pop();

    run_phase1_sumcheck(
        prover_state,
        ArenaCow::Owned(nums_ext),
        ArenaCow::Owned(dens_ext),
        parent_chunk_log - 2,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
        Some(eq_outer),
        Some(r1),
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn quotient_sumcheck_prove_packed_br_base_in_place<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    packed_nums: &[PFPacking<EF>],
    mut packed_dens: ArenaVec<EFPacking<EF>>,
    parent_chunk_log: usize,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log >= w + 3);
    debug_assert_eq!(packed_nums.len(), packed_dens.len());
    let active_chunks = (packed_nums.len() << w) >> parent_chunk_log;

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let outer_point = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = eval_eq(&outer_point);
    let padding_sum = alpha * mle_of_zeros_then_ones(active_chunks, &outer_point);

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let coeffs_0 = compute_round_packed::<EF, _>(packed_nums, &packed_dens, parent_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        coeffs_0,
        alpha,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r0);
    remaining_eq.pop();

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    #[cfg(debug_assertions)]
    let reference_fold = fold_and_compute_round_packed::<EF, _>(
        packed_nums,
        &packed_dens,
        parent_chunk_log,
        r0,
        &eq_outer,
        &eq_within_1,
    );
    fold_initial_into_denominator::<EF>(packed_nums, &mut packed_dens, parent_chunk_log, r0);
    let mut folds = 1;
    let coeffs_1 = compute_round_virtual_pairs::<EF>(&packed_dens, parent_chunk_log, folds, &eq_outer, &eq_within_1);
    #[cfg(debug_assertions)]
    {
        let first_fold_bit = parent_chunk_log - 2 - packing_log_width::<EF>();
        for i in 0..reference_fold.0.len() {
            let (num, den) = virtual_pair::<EF>(&packed_dens, first_fold_bit, folds, i);
            assert_eq!(num, reference_fold.0[i]);
            assert_eq!(den, reference_fold.1[i]);
        }
        assert_eq!(coeffs_1.c0_den, reference_fold.2.c0_den);
        assert_eq!(coeffs_1.c2_den, reference_fold.2.c2_den);
        assert_eq!(coeffs_1.c0_num, reference_fold.2.c0_num);
        assert_eq!(coeffs_1.c2_num, reference_fold.2.c2_num);
    }
    let r1 = finalize_round(
        prover_state,
        coeffs_1,
        alpha,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r1);
    remaining_eq.pop();

    run_phase1_sumcheck_virtual_pairs(
        prover_state,
        &mut packed_dens,
        parent_chunk_log,
        &mut folds,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
        eq_outer,
        r1,
    )
}

fn pair_indices(index: usize, bit: usize) -> (usize, usize) {
    let stride = 1usize << bit;
    let low_mask = stride - 1;
    let high = index >> bit;
    let low = index & low_mask;
    let first = (high << (bit + 1)) | low;
    (first, first | stride)
}

fn virtual_pair_positions(index: usize, first_fold_bit: usize, folds: usize) -> (usize, usize) {
    debug_assert!(folds > 0 && folds <= first_fold_bit + 1);
    let mut physical = index;
    for bit in first_fold_bit + 1 - folds..=first_fold_bit {
        physical = pair_indices(physical, bit).0;
    }
    (physical, physical | (1 << first_fold_bit))
}

fn fold_initial_into_denominator<EF: KoalaBearExtension>(
    nums: &[PFPacking<EF>],
    dens: &mut [EFPacking<EF>],
    parent_chunk_log: usize,
    challenge: EF,
) {
    let first_fold_bit = parent_chunk_log - 2 - packing_log_width::<EF>();
    let challenge_packed = EFPacking::<EF>::from(challenge);
    let ptr = parallel::SendPtr(dens.as_mut_ptr());
    parallel::for_each_index(nums.len() / 2, |j| {
        let (i0, i1) = pair_indices(j, first_fold_bit);
        let den0 = unsafe { *ptr.add(i0) };
        let den1 = unsafe { *ptr.add(i1) };
        let num = challenge_packed * (nums[i1] - nums[i0]) + nums[i0];
        let den = den0 + (den1 - den0) * challenge;
        unsafe {
            ptr.add(i0).write(num);
            ptr.add(i1).write(den);
        }
    });
}

fn virtual_pair<EF: KoalaBearExtension>(
    storage: &[EFPacking<EF>],
    first_fold_bit: usize,
    folds: usize,
    index: usize,
) -> (EFPacking<EF>, EFPacking<EF>) {
    let (num, den) = virtual_pair_positions(index, first_fold_bit, folds);
    (storage[num], storage[den])
}

fn compute_round_virtual_pairs<EF: KoalaBearExtension>(
    storage: &[EFPacking<EF>],
    parent_chunk_log: usize,
    folds: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EFPacking<EF>> {
    let w = packing_log_width::<EF>();
    let layer_chunk_log = parent_chunk_log - folds;
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    let virtual_len = storage.len() >> folds;
    debug_assert!(virtual_len.is_multiple_of(layer_packed));
    debug_assert_eq!(eq_within.len(), quarter);
    let first_fold_bit = parent_chunk_log - 2 - w;

    parallel::map_reduce(
        virtual_len / layer_packed,
        RoundCoeffs::zero,
        |chunk| {
            let base = chunk * layer_packed;
            let eq_o = eq_outer.get(chunk).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for (inner, &eq) in eq_within.iter().enumerate() {
                let (n00, d00) = virtual_pair::<EF>(storage, first_fold_bit, folds, base + inner);
                let (n01, d01) = virtual_pair::<EF>(storage, first_fold_bit, folds, base + inner + quarter);
                let (n10, d10) = virtual_pair::<EF>(storage, first_fold_bit, folds, base + inner + half);
                let (n11, d11) = virtual_pair::<EF>(storage, first_fold_bit, folds, base + inner + half + quarter);
                local +=
                    pair_coeffs::<EFPacking<EF>, EFPacking<EF>>((n00, n01), (n10, n11), (d00, d01), (d10, d11)) * eq;
            }
            local * eq_o
        },
        Add::add,
    )
}

fn fold_virtual_pairs_in_place<EF: KoalaBearExtension>(
    storage: &mut [EFPacking<EF>],
    parent_chunk_log: usize,
    folds: usize,
    challenge: EF,
) {
    let w = packing_log_width::<EF>();
    let first_fold_bit = parent_chunk_log - 2 - w;
    let current_bit = first_fold_bit - folds;
    let current_len = storage.len() >> folds;
    let ptr = parallel::SendPtr(storage.as_mut_ptr());
    parallel::for_each_index(current_len / 2, |j| {
        let (i0, i1) = pair_indices(j, current_bit);
        let (n0_pos, d0_pos) = virtual_pair_positions(i0, first_fold_bit, folds);
        let (n1_pos, d1_pos) = virtual_pair_positions(i1, first_fold_bit, folds);
        let (out_n, out_d) = virtual_pair_positions(j, first_fold_bit, folds + 1);
        let n0 = unsafe { *ptr.add(n0_pos) };
        let d0 = unsafe { *ptr.add(d0_pos) };
        let n1 = unsafe { *ptr.add(n1_pos) };
        let d1 = unsafe { *ptr.add(d1_pos) };
        unsafe {
            ptr.add(out_n).write(n0 + (n1 - n0) * challenge);
            ptr.add(out_d).write(d0 + (d1 - d0) * challenge);
        }
    });
}

#[allow(clippy::too_many_arguments)]
fn run_phase1_sumcheck_virtual_pairs<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    storage: &mut ArenaVec<EFPacking<EF>>,
    parent_chunk_log: usize,
    folds: &mut usize,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
    eq_outer: ArenaVec<EF>,
    mut pending_r: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    let mut layer_chunk_log = parent_chunk_log - *folds - 1;
    let head_len = (remaining_eq.len() + 1).saturating_sub(layer_chunk_log);
    let outer_point = remaining_eq[..head_len].to_vec();
    let active_chunks = ((storage.len() >> *folds) << w) >> (layer_chunk_log + 1);
    let padding_sum = alpha * mle_of_zeros_then_ones(active_chunks, &outer_point);

    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_within: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
        fold_virtual_pairs_in_place(storage, parent_chunk_log, *folds, pending_r);
        *folds += 1;
        let coeffs = compute_round_virtual_pairs(storage, parent_chunk_log, *folds, &eq_outer, &eq_within);
        let r = finalize_round(prover_state, coeffs, alpha, eq_alpha, &mut sum, &mut mmf, padding_sum);
        pending_r = r;
        layer_chunk_log -= 1;
        q_natural.push(r);
        remaining_eq.pop();
    }

    fold_virtual_pairs_in_place(storage, parent_chunk_log, *folds, pending_r);
    *folds += 1;
    let first_fold_bit = parent_chunk_log - 2 - w;
    let virtual_len = storage.len() >> *folds;
    let mut nums: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(virtual_len) };
    let mut dens: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(virtual_len) };
    parallel::par_for_each_mut2(&mut nums, &mut dens, |i, num, den| {
        (*num, *den) = virtual_pair::<EF>(storage, first_fold_bit, *folds, i);
    });

    let nums_nat = unpack_and_unreverse_active::<EF>(&nums, layer_chunk_log);
    let dens_nat = unpack_and_unreverse_active::<EF>(&dens, layer_chunk_log);
    let (num_l, num_r) = even_odd_split(&nums_nat);
    let (den_l, den_r) = even_odd_split(&dens_nat);
    run_phase2_sumcheck(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn quotient_sumcheck_prove_reduced_initial<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    initial_nums: &[PFPacking<EF>],
    initial_dens: &[EFPacking<EF>],
    initial_chunk_log: usize,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    let layer_chunk_log = initial_chunk_log - 1;
    debug_assert!(layer_chunk_log >= w + 3);
    debug_assert_eq!(initial_nums.len(), initial_dens.len());

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = (k + 1).saturating_sub(layer_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let outer_point = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = eval_eq(&outer_point);
    let active_chunks = (initial_nums.len() << (w - 1)) >> layer_chunk_log;
    let padding_sum = alpha * mle_of_zeros_then_ones(active_chunks, &outer_point);

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let coeffs_0 =
        compute_round_reduced_initial::<EF>(initial_nums, initial_dens, initial_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        coeffs_0,
        alpha,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r0);
    remaining_eq.pop();

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (nums_ext, dens_ext, coeffs_1) = fold_and_compute_round_reduced_initial::<EF>(
        initial_nums,
        initial_dens,
        initial_chunk_log,
        r0,
        &eq_outer,
        &eq_within_1,
    );
    let r1 = finalize_round(
        prover_state,
        coeffs_1,
        alpha,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r1);
    remaining_eq.pop();

    run_phase1_sumcheck(
        prover_state,
        ArenaCow::Owned(nums_ext),
        ArenaCow::Owned(dens_ext),
        layer_chunk_log - 2,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
        Some(eq_outer),
        Some(r1),
    )
}

#[inline(always)]
fn reduced_initial_value<EF: KoalaBearExtension>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    initial_chunk_log: usize,
    index: usize,
) -> (EFPacking<EF>, EFPacking<EF>) {
    let bit = initial_chunk_log - 1 - packing_log_width::<EF>();
    let stride = 1usize << bit;
    let low_mask = stride - 1;
    let high = index >> bit;
    let low = index & low_mask;
    let i0 = (high << (bit + 1)) | low;
    let i1 = i0 | stride;
    (dens[i1] * nums[i0] + dens[i0] * nums[i1], dens[i0] * dens[i1])
}

fn compute_round_reduced_initial<EF: KoalaBearExtension>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    initial_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EFPacking<EF>> {
    let w = packing_log_width::<EF>();
    let layer_chunk_log = initial_chunk_log - 1;
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    let reduced_len = nums.len() / 2;
    debug_assert!(reduced_len.is_multiple_of(layer_packed));
    debug_assert_eq!(eq_within.len(), quarter);

    let n_chunks = reduced_len / layer_packed;
    parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |chunk| {
            let base = chunk * layer_packed;
            let eq_o = eq_outer.get(chunk).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for (inner, &eq) in eq_within.iter().enumerate() {
                let (n00, d00) = reduced_initial_value::<EF>(nums, dens, initial_chunk_log, base + inner);
                let (n01, d01) = reduced_initial_value::<EF>(nums, dens, initial_chunk_log, base + inner + quarter);
                let (n10, d10) = reduced_initial_value::<EF>(nums, dens, initial_chunk_log, base + inner + half);
                let (n11, d11) =
                    reduced_initial_value::<EF>(nums, dens, initial_chunk_log, base + inner + half + quarter);
                local +=
                    pair_coeffs::<EFPacking<EF>, EFPacking<EF>>((n00, n01), (n10, n11), (d00, d01), (d10, d11)) * eq;
            }
            local * eq_o
        },
        Add::add,
    )
}

#[allow(clippy::type_complexity)]
fn fold_and_compute_round_reduced_initial<EF: KoalaBearExtension>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    initial_chunk_log: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (
    ArenaVec<EFPacking<EF>>,
    ArenaVec<EFPacking<EF>>,
    RoundCoeffs<EFPacking<EF>>,
) {
    let w = packing_log_width::<EF>();
    let layer_chunk_log = initial_chunk_log - 1;
    let in_packed = 1usize << (layer_chunk_log - w);
    let in_half = in_packed / 2;
    let in_quarter = in_packed / 4;
    let in_eighth = in_packed / 8;
    let out_packed = in_packed / 2;
    let out_half = out_packed / 2;
    let out_quarter = out_packed / 4;
    let reduced_len = nums.len() / 2;
    debug_assert!(reduced_len.is_multiple_of(in_packed));
    debug_assert_eq!(eq_within.len(), in_eighth);

    let mut new_nums: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(reduced_len / 2) };
    let mut new_dens: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(reduced_len / 2) };
    let prev_r_packed = EFPacking::<EF>::from(prev_r);
    let n_chunks = reduced_len / in_packed;
    let nums_out = parallel::SendPtr(new_nums.as_mut_ptr());
    let dens_out = parallel::SendPtr(new_dens.as_mut_ptr());
    let coeffs = parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |chunk| {
            let input_base = chunk * in_packed;
            let output_base = chunk * out_packed;
            let out_nums = unsafe { nums_out.slice(output_base, out_packed) };
            let out_dens = unsafe { dens_out.slice(output_base, out_packed) };
            let eq_o = eq_outer.get(chunk).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for i in 0..in_eighth {
                for side in 0..2 {
                    for quarter in 0..2 {
                        let lo = input_base + i + side * in_half + quarter * in_eighth;
                        let hi = lo + in_quarter;
                        let out = i + side * out_half + quarter * out_quarter;
                        let (num_lo, den_lo) = reduced_initial_value::<EF>(nums, dens, initial_chunk_log, lo);
                        let (num_hi, den_hi) = reduced_initial_value::<EF>(nums, dens, initial_chunk_log, hi);
                        out_nums[out] = prev_r_packed * (num_hi - num_lo) + num_lo;
                        out_dens[out] = den_lo + (den_hi - den_lo) * prev_r;
                    }
                }
                local += pair_coeffs::<EFPacking<EF>, EFPacking<EF>>(
                    (out_nums[i], out_nums[i + out_quarter]),
                    (out_nums[i + out_half], out_nums[i + out_half + out_quarter]),
                    (out_dens[i], out_dens[i + out_quarter]),
                    (out_dens[i + out_half], out_dens[i + out_half + out_quarter]),
                ) * eq_within[i];
            }
            local * eq_o
        },
        Add::add,
    );

    (new_nums, new_dens, coeffs)
}

/// bit-reversed by chunk + Packed
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase1_sumcheck<'a, EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    mut nums: ArenaCow<'a, EFPacking<EF>>,
    mut dens: ArenaCow<'a, EFPacking<EF>>,
    mut layer_chunk_log: usize,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
    precomputed_eq_outer: Option<ArenaVec<EF>>,
    initial_pending_r: Option<EF>,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();

    if layer_chunk_log <= w {
        assert!(initial_pending_r.is_none());
        let (num_l, num_r) = even_odd_split(&unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log));
        let (den_l, den_r) = even_odd_split(&unpack_and_unreverse_active::<EF>(dens.as_ref(), layer_chunk_log));
        return run_phase2_sumcheck(
            prover_state,
            num_l,
            num_r,
            den_l,
            den_r,
            remaining_eq,
            q_natural,
            alpha,
            sum,
            mmf,
        );
    }

    let head_len = (remaining_eq.len() + 1).saturating_sub(layer_chunk_log);
    let outer_point: Vec<EF> = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = precomputed_eq_outer.unwrap_or_else(|| eval_eq(&outer_point));

    let active_chunks = (nums.len() << w) >> (layer_chunk_log + usize::from(initial_pending_r.is_some()));

    let padding_sum = alpha * mle_of_zeros_then_ones(active_chunks, &outer_point);

    let mut pending_r: Option<EF> = initial_pending_r;
    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_within: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));

        let coeffs = if let Some(prev_r) = pending_r.take() {
            match (&mut nums, &mut dens) {
                (ArenaCow::Owned(nums), ArenaCow::Owned(dens)) => fold_and_compute_round_packed_in_place::<EF>(
                    nums,
                    dens,
                    layer_chunk_log + 1,
                    prev_r,
                    &eq_outer,
                    &eq_within,
                ),
                _ => {
                    let (new_nums, new_dens, c) = fold_and_compute_round_packed::<EF, _>(
                        nums.as_ref(),
                        dens.as_ref(),
                        layer_chunk_log + 1,
                        prev_r,
                        &eq_outer,
                        &eq_within,
                    );
                    nums = ArenaCow::Owned(new_nums);
                    dens = ArenaCow::Owned(new_dens);
                    c
                }
            }
        } else {
            compute_round_packed::<EF, _>(nums.as_ref(), dens.as_ref(), layer_chunk_log, &eq_outer, &eq_within)
        };

        let r = finalize_round(prover_state, coeffs, alpha, eq_alpha, &mut sum, &mut mmf, padding_sum);
        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.push(r);
        remaining_eq.pop();
    }

    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        let mul = |x: EFPacking<EF>, a: EF| x * a;
        nums = ArenaCow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &mul, false));
        dens = ArenaCow::Owned(fold_multilinear_at_bit(dens.as_ref(), prev_r, prev_bit, &mul, false));
    }

    let nums_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), layer_chunk_log);
    let (num_l, num_r) = even_odd_split(&nums_nat);
    let (den_l, den_r) = even_odd_split(&dens_nat);
    run_phase2_sumcheck(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
    )
}

fn fold_and_compute_round_packed_in_place<EF: KoalaBearExtension>(
    nums: &mut ArenaVec<EFPacking<EF>>,
    dens: &mut ArenaVec<EFPacking<EF>>,
    layer_chunk_log_old: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EFPacking<EF>> {
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log_old >= w + 3);
    let in_packed = 1usize << (layer_chunk_log_old - w);
    let in_half = in_packed / 2;
    let in_quarter = in_packed / 4;
    let in_eighth = in_packed / 8;
    let out_packed = in_packed / 2;
    let out_half = out_packed / 2;
    let out_quarter = out_packed / 4;
    debug_assert!(nums.len().is_multiple_of(in_packed));
    debug_assert_eq!(dens.len(), nums.len());
    debug_assert_eq!(eq_within.len(), in_eighth);

    let prev_r_packed = EFPacking::<EF>::from(prev_r);
    let n_chunks = nums.len() / in_packed;
    for chunk in 0..n_chunks {
        let input_base = chunk * in_packed;
        let output_base = chunk * out_packed;
        for i in 0..in_eighth {
            for side in 0..2 {
                for quarter in 0..2 {
                    let lo = input_base + i + side * in_half + quarter * in_eighth;
                    let hi = lo + in_quarter;
                    let out = output_base + i + side * out_half + quarter * out_quarter;
                    let num_lo = nums[lo];
                    let num_hi = nums[hi];
                    let den_lo = dens[lo];
                    let den_hi = dens[hi];
                    nums[out] = prev_r_packed * (num_hi - num_lo) + num_lo;
                    dens[out] = den_lo + (den_hi - den_lo) * prev_r;
                }
            }
        }
    }
    nums.truncate(nums.len() / 2);
    dens.truncate(dens.len() / 2);
    compute_round_packed::<EF, _>(nums, dens, layer_chunk_log_old - 1, eq_outer, eq_within)
}

// Normal ordering (not bit-reversed) + not packed
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase2_sumcheck<EF: KoalaBearExtension>(
    prover_state: &mut impl FSProver<EF>,
    mut num_l: ArenaVec<EF>,
    mut num_r: ArenaVec<EF>,
    mut den_l: ArenaVec<EF>,
    mut den_r: ArenaVec<EF>,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
) -> (Vec<EF>, [EF; 4]) {
    let eq_prefix_init = &remaining_eq[..remaining_eq.len().saturating_sub(1)];
    let mut eq_table: ArenaVec<EF> = eval_eq(eq_prefix_init);

    for _round in 0..remaining_eq.len() {
        let eq_alpha = *remaining_eq.last().unwrap();

        let active_l = num_l.len();
        let active_r = num_r.len();
        let active_pairs = active_l.div_ceil(2);
        let fully_active = active_r / 2;

        let term = |j: usize| -> RoundCoeffs<EF> {
            let coeffs = if j < fully_active {
                pair_coeffs::<EF, EF>(
                    (num_l[2 * j], num_l[2 * j + 1]),
                    (num_r[2 * j], num_r[2 * j + 1]),
                    (den_l[2 * j], den_l[2 * j + 1]),
                    (den_r[2 * j], den_r[2 * j + 1]),
                )
            } else {
                let get_pair = |arr: &[EF], idx: usize, pad: EF| {
                    (
                        arr.get(idx).copied().unwrap_or(pad),
                        arr.get(idx + 1).copied().unwrap_or(pad),
                    )
                };
                pair_coeffs::<EF, EF>(
                    get_pair(&num_l, 2 * j, EF::ZERO),
                    get_pair(&num_r, 2 * j, EF::ZERO),
                    get_pair(&den_l, 2 * j, EF::ONE),
                    get_pair(&den_r, 2 * j, EF::ONE),
                )
            };
            coeffs * eq_table[j]
        };

        let acc: RoundCoeffs<EF> = if active_pairs > PARALLEL_THRESHOLD {
            parallel::map_reduce(active_pairs, RoundCoeffs::zero, term, Add::add)
        } else {
            (0..active_pairs).map(term).fold(RoundCoeffs::<EF>::zero(), Add::add)
        };

        let eq_prefix = &remaining_eq[..remaining_eq.len() - 1];
        let padding_sum = alpha * mle_of_zeros_then_ones(active_pairs, eq_prefix);

        let bare = build_bare_from_coeffs(
            acc.c0_num + alpha * acc.c0_den + padding_sum,
            acc.c2_num + alpha * acc.c2_den,
            eq_alpha,
            sum,
            mmf,
        );

        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        num_l = fold_normal_with_padding(&num_l, r, EF::ZERO);
        num_r = fold_normal_with_padding(&num_r, r, EF::ZERO);
        den_l = fold_normal_with_padding(&den_l, r, EF::ONE);
        den_r = fold_normal_with_padding(&den_r, r, EF::ONE);

        let new_eq_len = eq_table.len() / 2;
        if new_eq_len > 0 {
            let fold_eq = |i: usize| eq_table[2 * i] + eq_table[2 * i + 1];
            eq_table = if new_eq_len >= PARALLEL_THRESHOLD {
                ArenaVec::par_collect(new_eq_len, fold_eq)
            } else {
                (0..new_eq_len).map(fold_eq).collect()
            };
        }

        q_natural.push(r);
        remaining_eq.pop();
    }

    q_natural.reverse();
    let evals = [num_l[0], num_r[0], den_l[0], den_r[0]];
    (q_natural, evals)
}

fn fold_normal_with_padding<EF: KoalaBearExtension>(m: &[EF], r: EF, pad_value: EF) -> ArenaVec<EF> {
    let active = m.len();
    let new_active = active.div_ceil(2);
    assert!(new_active != 0);
    let mut out: ArenaVec<EF> = unsafe { ArenaVec::uninitialized(new_active) };

    let compute = |i: usize, slot: &mut EF| {
        let a = m[2 * i];
        let b = if 2 * i + 1 < active { m[2 * i + 1] } else { pad_value };
        *slot = a + (b - a) * r;
    };

    if new_active < PARALLEL_THRESHOLD {
        out.iter_mut().enumerate().for_each(|(i, slot)| compute(i, slot));
    } else {
        parallel::par_for_each_mut(&mut out, compute);
    }
    out
}

fn compute_round_packed<EF: KoalaBearExtension, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EFPacking<EF>>
where
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log >= w + 2);
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    debug_assert!(nums.len().is_multiple_of(layer_packed));
    debug_assert_eq!(dens.len(), nums.len());
    debug_assert_eq!(eq_within.len(), quarter);

    let n_chunks = nums.len() / layer_packed;
    parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |c| {
            let n_c = &nums[c * layer_packed..][..layer_packed];
            let d_c = &dens[c * layer_packed..][..layer_packed];
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for inner in 0..quarter {
                let coeffs = pair_coeffs::<EFPacking<EF>, _>(
                    (n_c[inner], n_c[inner + quarter]),
                    (n_c[inner + half], n_c[inner + half + quarter]),
                    (d_c[inner], d_c[inner + quarter]),
                    (d_c[inner + half], d_c[inner + half + quarter]),
                );
                local += coeffs * eq_within[inner];
            }
            local * eq_o
        },
        Add::add,
    )
}

#[allow(clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: KoalaBearExtension, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log_old: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (
    ArenaVec<EFPacking<EF>>,
    ArenaVec<EFPacking<EF>>,
    RoundCoeffs<EFPacking<EF>>,
)
where
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log_old >= w + 3);
    let in_packed = 1usize << (layer_chunk_log_old - w);
    let in_half = in_packed / 2;
    let in_quarter = in_packed / 4;
    let in_eighth = in_packed / 8;
    let out_packed = in_packed / 2;
    let out_half = out_packed / 2;
    let out_quarter = out_packed / 4;
    debug_assert!(nums.len().is_multiple_of(in_packed));
    debug_assert_eq!(dens.len(), nums.len());
    debug_assert_eq!(eq_within.len(), in_eighth);

    let active_out_packed = nums.len() / 2;
    let mut new_nums: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(active_out_packed) };
    let mut new_dens: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(active_out_packed) };
    let prev_r_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(prev_r);

    let n_chunks = nums.len() / in_packed;
    let nn = parallel::SendPtr(new_nums.as_mut_ptr());
    let nd = parallel::SendPtr(new_dens.as_mut_ptr());
    let coeffs = parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |c| {
            let n_c = &nums[c * in_packed..][..in_packed];
            let d_c = &dens[c * in_packed..][..in_packed];
            let nn_c = unsafe { nn.slice(c * out_packed, out_packed) };
            let nd_c = unsafe { nd.slice(c * out_packed, out_packed) };
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for i in 0..in_eighth {
                for side in 0..2 {
                    for c in 0..2 {
                        let lo = i + side * in_half + c * in_eighth;
                        let hi = lo + in_quarter;
                        let out = i + side * out_half + c * out_quarter;
                        nn_c[out] = prev_r_packed * (n_c[hi] - n_c[lo]) + n_c[lo];
                        nd_c[out] = d_c[lo] + (d_c[hi] - d_c[lo]) * prev_r;
                    }
                }
                let round = pair_coeffs::<EFPacking<EF>, EFPacking<EF>>(
                    (nn_c[i], nn_c[i + out_quarter]),
                    (nn_c[i + out_half], nn_c[i + out_half + out_quarter]),
                    (nd_c[i], nd_c[i + out_quarter]),
                    (nd_c[i + out_half], nd_c[i + out_half + out_quarter]),
                );
                local += round * eq_within[i];
            }
            local * eq_o
        },
        Add::add,
    );

    (new_nums, new_dens, coeffs)
}

fn build_bare_from_coeffs<EF: KoalaBearExtension>(
    c0_raw: EF,
    c2_raw: EF,
    eq_alpha: EF,
    sum: EF,
    mmf: EF,
) -> DensePolynomial<EF> {
    let c0_mmf = c0_raw * mmf;
    let c2_mmf = c2_raw * mmf;
    let h1_mmf = (sum - (EF::ONE - eq_alpha) * c0_mmf) / eq_alpha;
    let c1_mmf = h1_mmf - c0_mmf - c2_mmf;
    DensePolynomial::new(vec![c0_mmf, c1_mmf, c2_mmf])
}
