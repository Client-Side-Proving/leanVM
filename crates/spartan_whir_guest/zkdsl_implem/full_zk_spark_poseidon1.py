from snark_lib import *
from extension import *
from full_zk_common import *
from full_zk_production_common import *
from hiding_whir_spark_poseidon1 import *
from plain_whir_poseidon1 import *
from spark_poseidon1 import *
from transcript_poseidon1 import *


CONTEXT_PREFIX = FULL_ZK_CONTEXT_PREFIX_PLACEHOLDER
RELATION_DOMAIN_SEPARATOR = FULL_ZK_RELATION_DOMAIN_SEPARATOR_PLACEHOLDER
FIXED_VALUE_ROOT = FULL_ZK_FIXED_VALUE_ROOT_PLACEHOLDER
STATEMENT_PREFIX = FULL_ZK_STATEMENT_PREFIX_PLACEHOLDER

BRANCH_DOMAIN = [115, 112, 97, 114, 116, 97, 110, 45, 119, 104, 105, 114, 45, 115, 112, 97, 114, 107, 45, 111, 112, 101, 110, 105, 110, 103, 45, 98, 114, 97, 110, 99, 104, 101, 115, 45, 118, 51]
BRANCH_END = [115, 112, 97, 114, 116, 97, 110, 45, 119, 104, 105, 114, 45, 115, 112, 97, 114, 107, 45, 111, 112, 101, 110, 105, 110, 103, 45, 98, 114, 97, 110, 99, 104, 45, 101, 110, 100, 45, 118, 51]
BRANCH_MERGE = [115, 112, 97, 114, 116, 97, 110, 45, 119, 104, 105, 114, 45, 115, 112, 97, 114, 107, 45, 111, 112, 101, 110, 105, 110, 103, 45, 109, 101, 114, 103, 101, 45, 118, 51]
FIXED_COLUMNS = [0, 1, 2, 2, 3, 3, 4, 4, 5, 6]
FIXED_EVAL_INDICES = [6, 7, 0, 1, 2, 3, 4, 5, 8, 9]
FIXED_POINT_KINDS = [0, 0, 1, 2, 1, 2, 1, 2, 0, 0]
COLUMN_BITS_3 = [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]
READ_REVERSED_COLUMNS_3 = [0, 4, 2, 6, 1, 5, 3, 7]

OUTER_ROUNDS = SPARK_OUTER_ROUNDS_VALUE
INNER_ROUNDS = SPARK_INNER_ROUNDS_VALUE
APPLICATION_PUBLIC_INPUTS = SPARK_PUBLIC_INPUTS_VALUE
VALUE_BITS = SPARK_VALUE_BITS_VALUE
ROW_BITS = SPARK_ROW_BITS_VALUE
COL_BITS = SPARK_COL_BITS_VALUE
FIXED_BITS = SPARK_FIXED_BITS_VALUE
READ1_BITS = SPARK_READ1_BITS_VALUE
PUBLIC_INPUT_LEN = 8
FULL_ZK_WORDS = 1048576
CANONICAL_WORDS = SPARK_CANONICAL_WORDS_VALUE
OPT_COMPACT_INPUT = OPT_COMPACT_INPUT_VALUE
FRESH_ROW_HINT_OFFSETS = FRESH_ROW_HINT_OFFSETS_PLACEHOLDER
ZERO_PTR = PUBLIC_INPUT_LEN
ZERO_LEN = 16
ONE_EF_PTR = ZERO_PTR + ZERO_LEN


def build_preamble():
    zero_ptr = ZERO_PTR
    for i in unroll(0, ZERO_LEN):
        zero_ptr[i] = 0
    one = ONE_EF_PTR
    one[0] = 1
    for i in unroll(1, DIM):
        one[i] = 0
    return


def copy_ext(source, destination):
    for i in unroll(0, DIM):
        destination[i] = source[i]
    return


def copy_eval_batch(source, destination, count: Const):
    for value in unroll(0, count):
        copy_ext(source + value * DIM, destination + value * DIM)
    return


def assert_non_boolean(value):
    if value[0] == 0:
        if value[1] == 0:
            if value[2] == 0:
                if value[3] == 0:
                    assert value[4] != 0
    if value[0] == 1:
        if value[1] == 0:
            if value[2] == 0:
                if value[3] == 0:
                    assert value[4] != 0
    return


def build_application_covectors(r_x, outer_claims, outer_mask_evals, rho, batching):
    covectors = Array((4 * OUTER_ROUNDS) * 8 * DIM)
    matrix_coefficients = Array(3 * DIM)
    copy_ext(ef_one(), matrix_coefficients)
    copy_ext(rho, matrix_coefficients + DIM)
    copy_ext(ef_square(rho), matrix_coefficients + 2 * DIM)

    target: Mut = ef_add(
        outer_claims,
        ef_add(ef_mul(rho, outer_claims + DIM), ef_mul(ef_square(rho), outer_claims + 2 * DIM)),
    )
    coefficient: Mut = ef_copy(batching)
    mask_index: Mut = 0
    for matrix in unroll(0, 3):
        for round_index in unroll(0, OUTER_ROUNDS):
            point = r_x + round_index * DIM
            first_coefficient = ef_copy(coefficient)
            second_coefficient = ef_mul(first_coefficient, batching)
            power: Mut = ef_one()
            for term in unroll(0, 4):
                value: Mut = ef_add(
                    ef_mul(power, matrix_coefficients + matrix * DIM),
                    second_coefficient,
                )
                if term == 0:
                    value = ef_add(value, first_coefficient)
                copy_ext(value, covectors + (mask_index * 8 + term) * DIM)
                power = ef_mul(power, point)
            for term in unroll(4, 8):
                copy_ext(ef_zero(), covectors + (mask_index * 8 + term) * DIM)
            coefficient = ef_mul(second_coefficient, batching)
            mask_index += 1

    for round_index in unroll(0, OUTER_ROUNDS):
        point = r_x + round_index * DIM
        power: Mut = ef_one()
        for term in unroll(0, 8):
            copy_ext(ef_mul(coefficient, power), covectors + (mask_index * 8 + term) * DIM)
            power = ef_mul(power, point)
        target = ef_add(target, ef_mul(coefficient, outer_mask_evals + round_index * DIM))
        coefficient = ef_mul(coefficient, batching)
        mask_index += 1
    assert mask_index == (4 * OUTER_ROUNDS)
    return covectors, target


def build_sumcheck_covectors(r_y):
    covectors = Array(INNER_ROUNDS * 3 * DIM)
    for mask in unroll(0, INNER_ROUNDS):
        copy_ext(ef_one(), covectors + mask * 3 * DIM)
        copy_ext(r_y + mask * DIM, covectors + (mask * 3 + 1) * DIM)
        copy_ext(ef_square(r_y + mask * DIM), covectors + (mask * 3 + 2) * DIM)
    return covectors


def scale_covectors(covectors, count: Const, width: Const, scale):
    result = Array(count * width * DIM)
    for i in unroll(0, count * width):
        value = ef_mul(covectors + i * DIM, scale)
        copy_ext(value, result + i * DIM)
    return result


def verify_spartan_prefix(proof):
    fs: Mut = fs_new()
    if OPT_TRANSCRIPT_BLOCKS == 1:
        context_prefix_words = Array(len(CONTEXT_PREFIX))
        for i in unroll(0, len(CONTEXT_PREFIX)):
            context_prefix_words[i] = CONTEXT_PREFIX[i]
        fs = fs_observe_const(fs, context_prefix_words, len(CONTEXT_PREFIX))
    else:
        for i in unroll(0, len(CONTEXT_PREFIX)):
            fs = fs_observe_one(fs, CONTEXT_PREFIX[i])
    if OPT_TRANSCRIPT_BLOCKS == 1:
        fs = fs_observe_const(fs, proof + SPARK_OFFSET_10_VALUE, APPLICATION_PUBLIC_INPUTS)
    else:
        for i in unroll(0, APPLICATION_PUBLIC_INPUTS):
            fs = fs_observe_one(fs, proof[SPARK_OFFSET_10_VALUE + i])
    fs = fs_observe_const(fs, proof + SPARK_OFFSET_276_VALUE, 8)
    if OPT_TRANSCRIPT_BLOCKS == 1:
        relation_domain_separator_words = Array(len(RELATION_DOMAIN_SEPARATOR))
        for i in unroll(0, len(RELATION_DOMAIN_SEPARATOR)):
            relation_domain_separator_words[i] = RELATION_DOMAIN_SEPARATOR[i]
        fs = fs_observe_const(fs, relation_domain_separator_words, len(RELATION_DOMAIN_SEPARATOR))
    else:
        for i in unroll(0, len(RELATION_DOMAIN_SEPARATOR)):
            fs = fs_observe_one(fs, RELATION_DOMAIN_SEPARATOR[i])
    fs = fs_observe_const(fs, proof + SPARK_OFFSET_267_VALUE, 8)

    fs = fs_observe_extension(fs, proof + SPARK_OFFSET_284_VALUE)
    fs, outer_epsilon = fs_sample_extension(fs)
    tau = Array(OUTER_ROUNDS * DIM)
    for i in unroll(0, OUTER_ROUNDS):
        fs, challenge = fs_sample_extension(fs)
        copy_ext(challenge, tau + i * DIM)

    outer_claim: Mut = ef_copy(proof + SPARK_OFFSET_284_VALUE)
    r_x = Array(OUTER_ROUNDS * DIM)
    for round_index in unroll(0, OUTER_ROUNDS):
        wire = proof + SPARK_OFFSET_291_VALUE + round_index * 36
        assert proof[SPARK_OFFSET_290_VALUE + round_index * 36] == 7
        fs = fs_observe_const(fs, wire, 7 * DIM)
        fs, challenge = fs_sample_extension(fs)
        if round_index == OUTER_ROUNDS - 1:
            assert_non_boolean(challenge)
        outer_claim = evaluate_degree_seven_compact(wire, outer_claim, challenge)
        copy_ext(challenge, r_x + round_index * DIM)

    outer_claims = proof + SPARK_OFFSET_1010_VALUE
    outer_mask_evals = proof + SPARK_OFFSET_1026_VALUE
    outer_relation = ef_sub(ef_mul(outer_claims, outer_claims + DIM), outer_claims + 2 * DIM)
    expected_outer = ef_add(
        ef_mul(outer_epsilon, ef_mul(outer_relation, eq_points(tau, r_x, OUTER_ROUNDS))),
        dot_extension_vectors_with_ones(outer_mask_evals, OUTER_ROUNDS),
    )
    ef_assert_equal(outer_claim, expected_outer)

    fs = fs_observe_const(fs, outer_mask_evals, OUTER_ROUNDS * DIM)
    fs = fs_observe_const(fs, outer_claims, 3 * DIM)
    fs, rho = fs_sample_extension(fs)
    fs, batching = fs_sample_extension(fs)
    application_covectors, joint_target = build_application_covectors(
        r_x,
        outer_claims,
        outer_mask_evals,
        rho,
        batching,
    )

    fs = fs_observe_extension(fs, joint_target)
    fs = fs_observe_const(fs, proof + SPARK_OFFSET_1366_VALUE, 8)
    fs = fs_observe_extension(fs, proof + SPARK_OFFSET_1127_VALUE)
    fs, inner_epsilon = fs_sample_extension(fs)
    inner_claim: Mut = ef_add(ef_mul(inner_epsilon, joint_target), proof + SPARK_OFFSET_1127_VALUE)
    r_y = Array(INNER_ROUNDS * DIM)
    for round_index in unroll(0, INNER_ROUNDS):
        wire = proof + SPARK_OFFSET_1134_VALUE + round_index * 11
        assert proof[SPARK_OFFSET_1133_VALUE + round_index * 11] == 2
        fs = fs_observe_const(fs, wire, 2 * DIM)
        fs, challenge = fs_sample_extension(fs)
        inner_claim = evaluate_quadratic_wire(wire, inner_claim, challenge)
        copy_ext(challenge, r_y + round_index * DIM)

    application_scale = ef_scale(inner_epsilon, SPARK_INNER_INV_POWER_VALUE)
    scaled_application_covectors = scale_covectors(application_covectors, (4 * OUTER_ROUNDS), 8, application_scale)
    sumcheck_covectors = build_sumcheck_covectors(r_y)
    return (
        fs,
        r_x,
        r_y,
        rho,
        inner_epsilon,
        inner_claim,
        scaled_application_covectors,
        sumcheck_covectors,
    )


def dot_extension_vectors_with_ones(values, count: Const):
    result: Mut = ef_zero()
    for i in unroll(0, count):
        result = ef_add(result, values + i * DIM)
    return result


def rectangular_point(column: Const, column_bits: Const, base_point, base_len: Const):
    result = Array((column_bits + base_len) * DIM)
    for bit_index in unroll(0, column_bits):
        bit: Imm
        if column_bits == 1:
            bit = column
        if column_bits == 3:
            bit = COLUMN_BITS_3[column * 3 + bit_index]
        copy_ext(ef_from_base(bit), result + bit_index * DIM)
    for i in unroll(0, base_len * DIM):
        result[column_bits * DIM + i] = base_point[i]
    return result


def read_layout_point(column: Const, column_bits: Const, base_point, base_len: Const):
    result = Array((base_len + column_bits) * DIM)
    for i in unroll(0, base_len * DIM):
        result[i] = base_point[i]
    reversed_column: Imm
    if column_bits == 1:
        reversed_column = column
    if column_bits == 3:
        reversed_column = READ_REVERSED_COLUMNS_3[column]
    for bit_index in unroll(0, column_bits):
        bit: Imm
        if column_bits == 1:
            bit = reversed_column
        if column_bits == 3:
            bit = COLUMN_BITS_3[reversed_column * 3 + bit_index]
        copy_ext(ef_from_base(bit), result + (base_len + bit_index) * DIM)
    return result


def build_fixed_claims(ops_point, ops_dot_point, mem_point, fixed_evals):
    low = Array(VALUE_BITS * DIM)
    high = Array(VALUE_BITS * DIM)
    copy_ext(ef_zero(), low)
    copy_ext(ef_one(), high)
    for i in unroll(0, (VALUE_BITS - 1) * DIM):
        low[DIM + i] = ops_dot_point[i]
        high[DIM + i] = ops_dot_point[i]

    points = Array(12 * FIXED_BITS * DIM)
    evals = Array(12 * DIM)
    for claim in unroll(0, 10):
        base: Imm
        if FIXED_POINT_KINDS[claim] == 0:
            base = ops_point
        if FIXED_POINT_KINDS[claim] == 1:
            base = low
        if FIXED_POINT_KINDS[claim] == 2:
            base = high
        point = rectangular_point(FIXED_COLUMNS[claim], 3, base, VALUE_BITS)
        for i in unroll(0, FIXED_BITS * DIM):
            points[(claim * FIXED_BITS * DIM) + i] = point[i]
        copy_ext(fixed_evals + FIXED_EVAL_INDICES[claim] * DIM, evals + claim * DIM)

    row_base = Array(VALUE_BITS * DIM)
    for i in unroll(0, VALUE_BITS - ROW_BITS):
        copy_ext(ef_zero(), row_base + i * DIM)
    for i in unroll(0, ROW_BITS * DIM):
        row_base[(VALUE_BITS - ROW_BITS) * DIM + i] = mem_point[(COL_BITS - ROW_BITS) * DIM + i]
    col_base = Array(VALUE_BITS * DIM)
    for i in unroll(0, VALUE_BITS - COL_BITS - 1):
        copy_ext(ef_zero(), col_base + i * DIM)
    copy_ext(ef_one(), col_base + (VALUE_BITS - COL_BITS - 1) * DIM)
    for i in unroll(0, COL_BITS * DIM):
        col_base[(VALUE_BITS - COL_BITS) * DIM + i] = mem_point[i]
    row_point = rectangular_point(7, 3, row_base, VALUE_BITS)
    col_point = rectangular_point(7, 3, col_base, VALUE_BITS)
    for i in unroll(0, FIXED_BITS * DIM):
        points[10 * FIXED_BITS * DIM + i] = row_point[i]
        points[11 * FIXED_BITS * DIM + i] = col_point[i]
    copy_ext(fixed_evals + 10 * DIM, evals + 10 * DIM)
    copy_ext(fixed_evals + 11 * DIM, evals + 11 * DIM)
    return points, evals


def basis_recombine(coordinate_evals):
    result: Mut = ef_zero()
    for coordinate in unroll(0, DIM):
        basis = Array(DIM)
        for i in unroll(0, DIM):
            if i == coordinate:
                basis[i] = 1
            else:
                basis[i] = 0
        result = ef_add(result, ef_mul(coordinate_evals + coordinate * DIM, basis))
    return result


def build_read_claims(ops_point, ops_dot_point, group0_evals, group1_evals):
    low = Array(VALUE_BITS * DIM)
    high = Array(VALUE_BITS * DIM)
    copy_ext(ef_zero(), low)
    copy_ext(ef_one(), high)
    for i in unroll(0, (VALUE_BITS - 1) * DIM):
        low[DIM + i] = ops_dot_point[i]
        high[DIM + i] = ops_dot_point[i]
    logical_points = Array(6 * VALUE_BITS * DIM)
    for i in unroll(0, VALUE_BITS * DIM):
        logical_points[i] = low[i]
        logical_points[VALUE_BITS * DIM + i] = high[i]
        logical_points[2 * VALUE_BITS * DIM + i] = ops_point[i]
        logical_points[3 * VALUE_BITS * DIM + i] = low[i]
        logical_points[4 * VALUE_BITS * DIM + i] = high[i]
        logical_points[5 * VALUE_BITS * DIM + i] = ops_point[i]

    group0_points = Array(24 * FIXED_BITS * DIM)
    group0_claim_evals = Array(24 * DIM)
    for logical in unroll(0, 6):
        if logical < 3:
            for member in unroll(0, 5):
                claim = logical * 5 + member
                point = read_layout_point(member, 3, logical_points + logical * VALUE_BITS * DIM, VALUE_BITS)
                for i in unroll(0, FIXED_BITS * DIM):
                    group0_points[claim * FIXED_BITS * DIM + i] = point[i]
                copy_ext(group0_evals + claim * DIM, group0_claim_evals + claim * DIM)
        if 3 <= logical:
            for member in unroll(0, 3):
                claim = 15 + (logical - 3) * 3 + member
                point = read_layout_point(5 + member, 3, logical_points + logical * VALUE_BITS * DIM, VALUE_BITS)
                for i in unroll(0, FIXED_BITS * DIM):
                    group0_points[claim * FIXED_BITS * DIM + i] = point[i]
                copy_ext(group0_evals + claim * DIM, group0_claim_evals + claim * DIM)

    group1_points = Array(6 * READ1_BITS * DIM)
    group1_claim_evals = Array(6 * DIM)
    for logical in unroll(3, 6):
        for member in unroll(0, 2):
            claim = (logical - 3) * 2 + member
            point = read_layout_point(member, 1, logical_points + logical * VALUE_BITS * DIM, VALUE_BITS)
            for i in unroll(0, READ1_BITS * DIM):
                group1_points[claim * READ1_BITS * DIM + i] = point[i]
            copy_ext(group1_evals + claim * DIM, group1_claim_evals + claim * DIM)

    coordinate_evals = Array(6 * DIM * DIM)
    for logical in unroll(0, 3):
        for coordinate in unroll(0, 5):
            source = group0_evals + (logical * 5 + coordinate) * DIM
            copy_ext(source, coordinate_evals + (logical * DIM + coordinate) * DIM)
    group0_ecol_start = 15
    for logical in unroll(0, 3):
        for coordinate in unroll(0, 3):
            source = group0_evals + (group0_ecol_start + logical * 3 + coordinate) * DIM
            copy_ext(source, coordinate_evals + ((logical + 3) * DIM + coordinate) * DIM)
        for coordinate in unroll(3, 5):
            source = group1_evals + (logical * 2 + coordinate - 3) * DIM
            copy_ext(source, coordinate_evals + ((logical + 3) * DIM + coordinate) * DIM)
    read_evals = Array(6 * DIM)
    for logical in unroll(0, 6):
        value = basis_recombine(coordinate_evals + logical * DIM * DIM)
        copy_ext(value, read_evals + logical * DIM)
    return group0_points, group0_claim_evals, group1_points, group1_claim_evals, read_evals


def observe_branch_domain(fs):
    current: Mut = fs_observe_one(fs, len(BRANCH_DOMAIN))
    if OPT_TRANSCRIPT_BLOCKS == 1:
        branch_domain_words = Array(len(BRANCH_DOMAIN))
        for i in unroll(0, len(BRANCH_DOMAIN)):
            branch_domain_words[i] = BRANCH_DOMAIN[i]
        current = fs_observe_const(current, branch_domain_words, len(BRANCH_DOMAIN))
    else:
        for i in unroll(0, len(BRANCH_DOMAIN)):
            current = fs_observe_one(current, BRANCH_DOMAIN[i])
    return current


def observe_branch_end(fs):
    current: Mut = fs_observe_one(fs, len(BRANCH_END))
    if OPT_TRANSCRIPT_BLOCKS == 1:
        branch_end_words = Array(len(BRANCH_END))
        for i in unroll(0, len(BRANCH_END)):
            branch_end_words[i] = BRANCH_END[i]
        current = fs_observe_const(current, branch_end_words, len(BRANCH_END))
    else:
        for i in unroll(0, len(BRANCH_END)):
            current = fs_observe_one(current, BRANCH_END[i])
    return current


def observe_branch_merge(fs):
    current: Mut = fs_observe_one(fs, len(BRANCH_MERGE))
    if OPT_TRANSCRIPT_BLOCKS == 1:
        branch_merge_words = Array(len(BRANCH_MERGE))
        for i in unroll(0, len(BRANCH_MERGE)):
            branch_merge_words[i] = BRANCH_MERGE[i]
        current = fs_observe_const(current, branch_merge_words, len(BRANCH_MERGE))
    else:
        for i in unroll(0, len(BRANCH_MERGE)):
            current = fs_observe_one(current, BRANCH_MERGE[i])
    return current


def seal_branch(fs):
    current: Mut = observe_branch_end(fs)
    seal = Array(8)
    for i in unroll(0, 8):
        current, seal[i] = fs_sample_base(current)
    return current, seal


def merge_branches(fs, fixed_seal, read_seal):
    current: Mut = observe_branch_merge(fs)
    current = fs_observe_one(current, 0)
    current = fs_observe_const(current, fixed_seal, 8)
    current = fs_observe_one(current, 1)
    current = fs_observe_const(current, read_seal, 8)
    return current


def verify_spark_closing(proof, fs, r_x, r_y):
    fixed_root = proof + SPARK_OFFSET_10645_VALUE
    for i in unroll(0, 8):
        assert fixed_root[i] == FIXED_VALUE_ROOT[i]
    fixed_proof = SPARK_OFFSET_10714_VALUE
    read0_root = proof + SPARK_OFFSET_140436_VALUE
    read0_proof = SPARK_OFFSET_140571_VALUE
    read1_root = proof + SPARK_OFFSET_270067_VALUE
    read1_proof = SPARK_OFFSET_270109_VALUE

    initial_fs, fixed_ood_point, fixed_ood_eval = parse_plain_commitment(
        proof,
        fixed_proof,
        fixed_root,
        fs,
        0,
        1,
        FIXED_BITS,
    )
    current_fs: Mut = initial_fs
    current_fs, _unused_point0, _unused_eval0 = parse_plain_commitment(
        proof,
        read0_proof,
        read0_root,
        current_fs,
        0,
        0,
        FIXED_BITS,
    )
    current_fs, _unused_point1, _unused_eval1 = parse_plain_commitment(
        proof,
        read1_proof,
        read1_root,
        current_fs,
        1,
        0,
        READ1_BITS,
    )

    (
        product_cursor,
        current_fs,
        beta,
        gamma,
        matrix_evals,
        ops_point,
        ops_evals,
        ops_dot_point,
        ops_dot_left,
        ops_dot_right,
        ops_dot_weight,
        mem_point,
        mem_evals,
    ) = verify_spark_products(proof, SPARK_OFFSET_1375_VALUE, current_fs)
    assert product_cursor == SPARK_OFFSET_10640_VALUE

    fixed_evals = proof + SPARK_OFFSET_10654_VALUE
    fixed_points, fixed_claim_evals = build_fixed_claims(
        ops_point,
        ops_dot_point,
        mem_point,
        fixed_evals,
    )
    ef_assert_equal(fixed_points + (1 * FIXED_BITS) * DIM, ef_zero())
    ef_assert_equal(fixed_points + (1 * FIXED_BITS + 1) * DIM, ef_zero())
    ef_assert_equal(fixed_points + (1 * FIXED_BITS + 2) * DIM, ef_one())
    group0_evals = Array(24 * DIM)
    copy_eval_batch(proof + SPARK_OFFSET_140446_VALUE, group0_evals, 5)
    copy_eval_batch(proof + SPARK_OFFSET_140472_VALUE, group0_evals + 5 * DIM, 5)
    copy_eval_batch(proof + SPARK_OFFSET_140498_VALUE, group0_evals + 10 * DIM, 5)
    copy_eval_batch(proof + SPARK_OFFSET_140524_VALUE, group0_evals + 15 * DIM, 3)
    copy_eval_batch(proof + SPARK_OFFSET_140540_VALUE, group0_evals + 18 * DIM, 3)
    copy_eval_batch(proof + SPARK_OFFSET_140556_VALUE, group0_evals + 21 * DIM, 3)

    group1_evals = Array(6 * DIM)
    copy_eval_batch(proof + SPARK_OFFSET_270077_VALUE, group1_evals, 2)
    copy_eval_batch(proof + SPARK_OFFSET_270088_VALUE, group1_evals + 2 * DIM, 2)
    copy_eval_batch(proof + SPARK_OFFSET_270099_VALUE, group1_evals + 4 * DIM, 2)
    (
        group0_points,
        group0_claim_evals,
        group1_points,
        group1_claim_evals,
        read_evals,
    ) = build_read_claims(ops_point, ops_dot_point, group0_evals, group1_evals)

    current_fs = observe_branch_domain(current_fs)
    current_fs = fs_observe_one(current_fs, 2)
    fixed_fs: Mut = fs_clone(current_fs)
    fixed_fs = fs_observe_one(fixed_fs, 0)
    read_fs: Mut = fs_clone(current_fs)
    read_fs = fs_observe_one(read_fs, 1)

    fixed_cursor, fixed_fs = verify_plain_whir_a(
        proof,
        fixed_proof,
        fixed_root,
        fixed_fs,
        fixed_points,
        fixed_claim_evals,
        12,
        1,
        1,
        fixed_ood_point,
        fixed_ood_eval,
    )
    assert fixed_cursor == SPARK_OFFSET_140430_VALUE
    fixed_fs, fixed_seal = seal_branch(fixed_fs)

    read0_cursor, read_fs = verify_plain_whir_a(
        proof,
        read0_proof,
        read0_root,
        read_fs,
        group0_points,
        group0_claim_evals,
        24,
        0,
        0,
        _unused_point0,
        _unused_eval0,
    )
    assert read0_cursor == SPARK_OFFSET_270063_VALUE
    read1_cursor, read_fs = verify_plain_whir_b(
        proof,
        read1_proof,
        read1_root,
        read_fs,
        group1_points,
        group1_claim_evals,
        6,
        0,
        0,
        _unused_point1,
        _unused_eval1,
    )
    assert read1_cursor == SPARK_OFFSET_390151_VALUE
    read_fs, read_seal = seal_branch(read_fs)
    current_fs = merge_branches(current_fs, fixed_seal, read_seal)

    verify_spark_leaf_claims(
        beta,
        gamma,
        ops_point,
        ops_evals,
        ops_dot_left,
        ops_dot_right,
        ops_dot_weight,
        mem_point,
        mem_evals,
        fixed_evals,
        read_evals,
        r_x,
        r_y,
    )
    return current_fs, matrix_evals


def main():
    build_preamble()
    public_input = 0
    proof: Imm
    if OPT_COMPACT_INPUT == 1:
        proof = Array(CANONICAL_WORDS)
        for interval in unroll(0, len(FRESH_ROW_HINT_OFFSETS)):
            hint_witness("full_zk_spark_words", proof + FRESH_ROW_HINT_OFFSETS[interval])
    else:
        proof = Array(FULL_ZK_WORDS)
        hint_witness("full_zk_spark_words", proof)

    assert proof[0] == 76
    assert proof[1] == 86
    assert proof[2] == 90
    assert proof[3] == 87
    assert proof[4] == SPARK_GUEST_VERSION_VALUE
    assert proof[5] == 2
    assert proof[6] == 5
    assert proof[7] == 1
    assert proof[8] == CANONICAL_WORDS
    assert proof[9] == APPLICATION_PUBLIC_INPUTS
    assert proof[SPARK_OFFSET_266_VALUE] == 1
    assert proof[SPARK_OFFSET_275_VALUE] == 1
    assert proof[SPARK_OFFSET_289_VALUE] == OUTER_ROUNDS
    assert proof[SPARK_OFFSET_1025_VALUE] == OUTER_ROUNDS
    assert proof[SPARK_OFFSET_1126_VALUE] == 3
    assert proof[SPARK_OFFSET_1132_VALUE] == INNER_ROUNDS
    assert proof[SPARK_OFFSET_1364_VALUE] == 0
    assert proof[SPARK_OFFSET_1365_VALUE] == 1
    assert proof[SPARK_OFFSET_1374_VALUE] == 1

    statement_fs: Mut = fs_new()
    if OPT_TRANSCRIPT_BLOCKS == 1:
        statement_prefix_words = Array(len(STATEMENT_PREFIX))
        for i in unroll(0, len(STATEMENT_PREFIX)):
            statement_prefix_words[i] = STATEMENT_PREFIX[i]
        statement_fs = fs_observe_const(statement_fs, statement_prefix_words, len(STATEMENT_PREFIX))
    else:
        for i in unroll(0, len(STATEMENT_PREFIX)):
            statement_fs = fs_observe_one(statement_fs, STATEMENT_PREFIX[i])
    if OPT_TRANSCRIPT_BLOCKS == 1:
        statement_fs = fs_observe_const(statement_fs, proof + SPARK_OFFSET_10_VALUE, APPLICATION_PUBLIC_INPUTS)
    else:
        for i in unroll(0, APPLICATION_PUBLIC_INPUTS):
            statement_fs = fs_observe_one(statement_fs, proof[SPARK_OFFSET_10_VALUE + i])
    digest = fs_finalize(statement_fs)
    for i in unroll(0, PUBLIC_INPUT_LEN):
        assert digest[i] == public_input[i]

    (
        prefix_fs,
        r_x,
        r_y,
        rho,
        inner_epsilon,
        inner_claim,
        application_covectors,
        sumcheck_covectors,
    ) = verify_spartan_prefix(proof)
    fs: Mut = prefix_fs
    fs, matrix_evals = verify_spark_closing(proof, fs, r_x, r_y)

    matrix_eval = ef_add(
        matrix_evals,
        ef_add(ef_mul(rho, matrix_evals + DIM), ef_mul(ef_square(rho), matrix_evals + 2 * DIM)),
    )
    selector = r_y
    public_eval = evaluate_public_half(proof, r_y)
    relation_coefficient = ef_mul(
        inner_epsilon,
        ef_mul(matrix_eval, ef_one_minus(selector)),
    )
    relation_target = ef_sub(
        inner_claim,
        ef_mul(inner_epsilon, ef_mul(matrix_eval, ef_mul(selector, public_eval))),
    )
    _final_fs = verify_hiding_whir_relation(
        proof,
        fs,
        r_y,
        relation_coefficient,
        relation_target,
        application_covectors,
        sumcheck_covectors,
    )
    return
