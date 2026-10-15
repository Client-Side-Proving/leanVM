from snark_lib import *
from extension import *
from full_zk_common import *
from transcript_poseidon1 import *


SPARK_ROW_MEMORY_SIZE = SPARK_ROW_MEMORY_SIZE_VALUE
SPARK_COL_MEMORY_SIZE = SPARK_COL_MEMORY_SIZE_VALUE
SPARK_VALUE_DOMAIN_SIZE = SPARK_VALUE_DOMAIN_SIZE_VALUE
SPARK_MATRIX_NNZ_PADDED = SPARK_MATRIX_NNZ_PADDED_VALUE
SPARK_LAYOUT_TAG = 1

OPT_SPARK_HORNER_CUBIC = SPARK_HORNER_CUBIC_PLACEHOLDER
OPT_SPARK_EQ_PRECOMPILE = SPARK_EQ_PRECOMPILE_PLACEHOLDER
OPT_SPARK_FACTOR_EQ_ENDPOINTS = SPARK_FACTOR_EQ_ENDPOINTS_PLACEHOLDER


def spark_evaluate_cubic_horner(h0, h2, h3, claim, challenge):
    h1 = ef_sub(claim, h0)
    d1 = ef_sub(h1, h0)
    d2 = ef_add(ef_sub(h2, ef_scale(h1, 2)), h0)
    d3 = ef_sub(ef_add(ef_sub(h3, ef_scale(h2, 3)), ef_scale(h1, 3)), h0)
    quadratic = ef_add(
        ef_scale(d2, INV_TWO),
        ef_mul(ef_sub_base(challenge, 2), ef_scale(d3, INV_SIX)),
    )
    linear = ef_add(d1, ef_mul(ef_sub_base(challenge, 1), quadratic))
    return ef_add(h0, ef_mul(challenge, linear))


def spark_eq_points_precompile(a, b, length: Const):
    result: Imm
    if length == 0:
        result = ef_one()
    else:
        result = Array(DIM)
        poly_eq_ee(a, b, result, length)
    return result


def spark_copy_extension(source, destination):
    for i in unroll(0, DIM):
        destination[i] = source[i]
    return


def spark_observe_base_extension(fs, value: Const):
    element = Array(DIM)
    element[0] = value
    for i in unroll(1, DIM):
        element[i] = 0
    return fs_observe_extension(fs, element)


def spark_extrapolate(left, right, challenge):
    return ef_add(left, ef_mul(challenge, ef_sub(right, left)))


def verify_spark_batched_product(
    proof,
    cursor_start,
    fs,
    expected_roots,
    expected_dotclaims,
    layer_count: Const,
    dot_count: Const,
):
    assert proof[cursor_start] == 4
    proof_roots = proof + cursor_start + 1
    for i in unroll(0, 4):
        ef_assert_equal(proof_roots + i * DIM, expected_roots + i * DIM)
    dot_count_offset = cursor_start + 1 + 4 * DIM
    assert proof[dot_count_offset] == dot_count
    proof_dotclaims = proof + dot_count_offset + 1
    for i in unroll(0, dot_count):
        ef_assert_equal(proof_dotclaims + i * DIM, expected_dotclaims + i * DIM)
    layer_count_offset = dot_count_offset + 1 + dot_count * DIM
    assert proof[layer_count_offset] == layer_count
    layer_starts = Array(layer_count + 1)
    layer_starts[0] = layer_count_offset + 1

    claims = Array((layer_count + 1) * 10 * DIM)
    for i in unroll(0, 4 * DIM):
        claims[i] = expected_roots[i]
    parent_points = Array((layer_count + 1) * layer_count * DIM)
    output_evals = Array(4 * DIM)
    output_dot_point = Array(layer_count * DIM)
    output_dot_left = Array(dot_count * DIM)
    output_dot_right = Array(dot_count * DIM)
    output_dot_weight = Array(dot_count * DIM)
    current_fs: Mut = fs

    for layer_index in unroll(0, layer_count):
        layer_start = layer_starts[layer_index]
        current_claims = claims + layer_index * 10 * DIM
        next_claims = claims + (layer_index + 1) * 10 * DIM
        parent_point = parent_points + layer_index * layer_count * DIM
        next_parent_point = parent_points + (layer_index + 1) * layer_count * DIM
        include_dots: Imm
        if layer_index + 1 == layer_count:
            include_dots = 1
        else:
            include_dots = 0
        if include_dots == 1:
            for i in unroll(0, dot_count * DIM):
                current_claims[4 * DIM + i] = expected_dotclaims[i]

        assert proof[layer_start] == layer_index
        round_wires = Array(layer_index)
        for round_index in unroll(0, layer_index):
            round_offset = layer_start + 1 + round_index * (1 + 3 * DIM)
            assert proof[round_offset] == 3
            round_wires[round_index] = proof + round_offset + 1
        left_offset = layer_start + 1 + layer_index * (1 + 3 * DIM)
        assert proof[left_offset] == 4
        left = proof + left_offset + 1
        right_offset = left_offset + 1 + 4 * DIM
        assert proof[right_offset] == 4
        right = proof + right_offset + 1
        expected_layer_dots: Imm
        if include_dots == 1:
            expected_layer_dots = dot_count
        else:
            expected_layer_dots = 0
        dot_left_offset = right_offset + 1 + 4 * DIM
        assert proof[dot_left_offset] == expected_layer_dots
        dot_left = proof + dot_left_offset + 1
        dot_right_offset = dot_left_offset + 1 + expected_layer_dots * DIM
        assert proof[dot_right_offset] == expected_layer_dots
        dot_right = proof + dot_right_offset + 1
        dot_weight_offset = dot_right_offset + 1 + expected_layer_dots * DIM
        assert proof[dot_weight_offset] == expected_layer_dots
        dot_weight = proof + dot_weight_offset + 1
        layer_starts[layer_index + 1] = dot_weight_offset + 1 + expected_layer_dots * DIM

        coefficients = Array(10 * DIM)
        joint_claim: Mut = ef_zero()
        if include_dots == 1:
            current_fs = fs_observe_const(current_fs, current_claims, (4 + dot_count) * DIM)
            for i in unroll(0, 4 + dot_count):
                current_fs, coefficient = fs_sample_extension(current_fs)
                spark_copy_extension(coefficient, coefficients + i * DIM)
                joint_claim = ef_add(joint_claim, ef_mul(current_claims + i * DIM, coefficient))
        else:
            current_fs = fs_observe_const(current_fs, current_claims, 4 * DIM)
            for i in unroll(0, 4):
                current_fs, coefficient = fs_sample_extension(current_fs)
                spark_copy_extension(coefficient, coefficients + i * DIM)
                joint_claim = ef_add(joint_claim, ef_mul(current_claims + i * DIM, coefficient))

        current_fs = fs_observe_extension(current_fs, joint_claim)
        reduced_claim: Mut = ef_copy(joint_claim)
        alpha = Array(layer_index * DIM)
        for round_index in unroll(0, layer_index):
            wire = round_wires[round_index]
            current_fs = fs_observe_const(current_fs, wire, 3 * DIM)
            current_fs, challenge = fs_sample_extension(current_fs)
            if OPT_SPARK_HORNER_CUBIC == 1:
                reduced_claim = spark_evaluate_cubic_horner(
                    wire,
                    wire + DIM,
                    wire + 2 * DIM,
                    reduced_claim,
                    challenge,
                )
            else:
                reduced_claim = evaluate_cubic_compact(
                    wire,
                    wire + DIM,
                    wire + 2 * DIM,
                    reduced_claim,
                    challenge,
                )
            spark_copy_extension(challenge, alpha + round_index * DIM)

        eq_eval: Imm
        if OPT_SPARK_EQ_PRECOMPILE == 1:
            eq_eval = spark_eq_points_precompile(parent_point, alpha, layer_index)
        else:
            eq_eval = eq_points(parent_point, alpha, layer_index)
        expected: Mut = ef_zero()
        if OPT_SPARK_FACTOR_EQ_ENDPOINTS == 1:
            products: Mut = ef_zero()
            for i in unroll(0, 4):
                term = ef_mul(
                    coefficients + i * DIM,
                    ef_mul(left + i * DIM, right + i * DIM),
                )
                products = ef_add(products, term)
            expected = ef_mul(eq_eval, products)
        else:
            for i in unroll(0, 4):
                term = ef_mul(
                    coefficients + i * DIM,
                    ef_mul(eq_eval, ef_mul(left + i * DIM, right + i * DIM)),
                )
                expected = ef_add(expected, term)
        if include_dots == 1:
            for i in unroll(0, dot_count):
                term = ef_mul(
                    coefficients + (4 + i) * DIM,
                    ef_mul(
                        dot_left + i * DIM,
                        ef_mul(dot_right + i * DIM, dot_weight + i * DIM),
                    ),
                )
                expected = ef_add(expected, term)
        ef_assert_equal(reduced_claim, expected)

        current_fs = fs_observe_const(current_fs, left, 4 * DIM)
        current_fs = fs_observe_const(current_fs, right, 4 * DIM)
        if include_dots == 1:
            current_fs = fs_observe_const(current_fs, dot_left, dot_count * DIM)
            current_fs = fs_observe_const(current_fs, dot_right, dot_count * DIM)
            current_fs = fs_observe_const(current_fs, dot_weight, dot_count * DIM)
        current_fs, combine = fs_sample_extension(current_fs)

        for i in unroll(0, 4):
            next_claim = spark_extrapolate(left + i * DIM, right + i * DIM, combine)
            spark_copy_extension(next_claim, next_claims + i * DIM)
        for i in unroll(0, layer_index * DIM):
            next_parent_point[i] = alpha[i]
        if include_dots == 1:
            for i in unroll(0, layer_index * DIM):
                output_dot_point[i] = alpha[i]
            for i in unroll(0, dot_count * DIM):
                output_dot_left[i] = dot_left[i]
                output_dot_right[i] = dot_right[i]
                output_dot_weight[i] = dot_weight[i]
        spark_copy_extension(combine, next_parent_point + layer_index * DIM)

    final_claims = claims + layer_count * 10 * DIM
    final_parent_point = parent_points + layer_count * layer_count * DIM
    for i in unroll(0, 4 * DIM):
        output_evals[i] = final_claims[i]
    return (
        layer_starts[layer_count],
        current_fs,
        final_parent_point,
        output_evals,
        output_dot_point,
        output_dot_left,
        output_dot_right,
        output_dot_weight,
    )


def verify_spark_products(proof, cursor_start, fs):
    beta = proof + cursor_start
    gamma = proof + cursor_start + DIM
    row_roots = proof + cursor_start + 2 * DIM
    col_roots = proof + cursor_start + 6 * DIM
    matrix_evals = proof + cursor_start + 10 * DIM
    product_start = cursor_start + 13 * DIM

    current_fs: Mut = fs
    current_fs = spark_observe_base_extension(current_fs, SPARK_ROW_MEMORY_SIZE)
    current_fs = spark_observe_base_extension(current_fs, SPARK_COL_MEMORY_SIZE)
    current_fs = spark_observe_base_extension(current_fs, SPARK_VALUE_DOMAIN_SIZE)
    current_fs = spark_observe_base_extension(current_fs, SPARK_MATRIX_NNZ_PADDED)
    current_fs = spark_observe_base_extension(current_fs, SPARK_LAYOUT_TAG)
    current_fs, sampled_beta = fs_sample_extension(current_fs)
    current_fs, sampled_gamma = fs_sample_extension(current_fs)
    ef_assert_equal(beta, sampled_beta)
    ef_assert_equal(gamma, sampled_gamma)

    ops_roots = Array(4 * DIM)
    spark_copy_extension(row_roots + DIM, ops_roots)
    spark_copy_extension(row_roots + 2 * DIM, ops_roots + DIM)
    spark_copy_extension(col_roots + DIM, ops_roots + 2 * DIM)
    spark_copy_extension(col_roots + 2 * DIM, ops_roots + 3 * DIM)
    mem_roots = Array(4 * DIM)
    spark_copy_extension(row_roots, mem_roots)
    spark_copy_extension(row_roots + 3 * DIM, mem_roots + DIM)
    spark_copy_extension(col_roots, mem_roots + 2 * DIM)
    spark_copy_extension(col_roots + 3 * DIM, mem_roots + 3 * DIM)

    ops_dotclaims = proof + product_start + 1 + 4 * DIM + 1
    assert proof[product_start] == 4
    assert proof[product_start + 1 + 4 * DIM] == 6
    for matrix in unroll(0, 3):
        combined = ef_add(
            ops_dotclaims + (2 * matrix) * DIM,
            ops_dotclaims + (2 * matrix + 1) * DIM,
        )
        ef_assert_equal(matrix_evals + matrix * DIM, combined)

    (
        ops_cursor,
        current_fs,
        ops_point,
        ops_evals,
        ops_dot_point,
        ops_dot_left,
        ops_dot_right,
        ops_dot_weight,
    ) = verify_spark_batched_product(
        proof,
        product_start,
        current_fs,
        ops_roots,
        ops_dotclaims,
        SPARK_VALUE_BITS_VALUE,
        6,
    )

    empty = Array(1)
    (
        mem_cursor,
        current_fs,
        mem_point,
        mem_evals,
        _mem_dot_point,
        _mem_dot_left,
        _mem_dot_right,
        _mem_dot_weight,
    ) = verify_spark_batched_product(
        proof,
        ops_cursor,
        current_fs,
        mem_roots,
        empty,
        SPARK_COL_BITS_VALUE,
        0,
    )

    row_left = ef_mul(row_roots, row_roots + 2 * DIM)
    row_right = ef_mul(row_roots + DIM, row_roots + 3 * DIM)
    ef_assert_equal(row_left, row_right)
    col_left = ef_mul(col_roots, col_roots + 2 * DIM)
    col_right = ef_mul(col_roots + DIM, col_roots + 3 * DIM)
    ef_assert_equal(col_left, col_right)

    return (
        mem_cursor,
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
    )


def spark_memory_tuple(addr, value, timestamp, beta):
    return ef_add(addr, ef_add(ef_mul(beta, value), ef_mul(ef_square(beta), timestamp)))


def spark_virtual_index(point, length: Const):
    result: Mut = ef_zero()
    for i in unroll(0, length):
        result = ef_add(result, ef_scale(point + i * DIM, 2 ** (length - i - 1)))
    return result


def spark_padded_memory_term(
    memory_bits: Const,
    padded_bits: Const,
    padded_point,
    memory_point,
    timestamp,
    beta,
    gamma,
):
    prefix_len = padded_bits - memory_bits
    low_weight: Mut = ef_one()
    for i in unroll(0, prefix_len):
        low_weight = ef_mul(low_weight, ef_one_minus(padded_point + i * DIM))
    real_point = padded_point + prefix_len * DIM
    addr = spark_virtual_index(real_point, memory_bits)
    value = eq_points(real_point, memory_point, memory_bits)
    term = ef_sub(spark_memory_tuple(addr, value, timestamp, beta), gamma)
    return ef_add(ef_mul(low_weight, term), ef_one_minus(low_weight))


def verify_spark_leaf_claims(
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
):
    row_addr = fixed_evals + 6 * DIM
    col_addr = fixed_evals + 7 * DIM
    row_read_ts = fixed_evals + 8 * DIM
    col_read_ts = fixed_evals + 9 * DIM
    row_audit_ts = fixed_evals + 10 * DIM
    col_audit_ts = fixed_evals + 11 * DIM
    erow_low = read_evals
    erow_high = read_evals + DIM
    erow_ops = read_evals + 2 * DIM
    ecol_low = read_evals + 3 * DIM
    ecol_high = read_evals + 4 * DIM
    ecol_ops = read_evals + 5 * DIM

    expected_ops = Array(4 * DIM)
    spark_copy_extension(
        ef_sub(spark_memory_tuple(row_addr, erow_ops, row_read_ts, beta), gamma),
        expected_ops,
    )
    spark_copy_extension(
        ef_sub(
            spark_memory_tuple(row_addr, erow_ops, ef_add(row_read_ts, ef_one()), beta),
            gamma,
        ),
        expected_ops + DIM,
    )
    spark_copy_extension(
        ef_sub(spark_memory_tuple(col_addr, ecol_ops, col_read_ts, beta), gamma),
        expected_ops + 2 * DIM,
    )
    spark_copy_extension(
        ef_sub(
            spark_memory_tuple(col_addr, ecol_ops, ef_add(col_read_ts, ef_one()), beta),
            gamma,
        ),
        expected_ops + 3 * DIM,
    )
    for i in unroll(0, 4):
        ef_assert_equal(ops_evals + i * DIM, expected_ops + i * DIM)

    for matrix in unroll(0, 3):
        ef_assert_equal(ops_dot_left + (2 * matrix) * DIM, erow_low)
        ef_assert_equal(ops_dot_left + (2 * matrix + 1) * DIM, erow_high)
        ef_assert_equal(ops_dot_right + (2 * matrix) * DIM, ecol_low)
        ef_assert_equal(ops_dot_right + (2 * matrix + 1) * DIM, ecol_high)
        ef_assert_equal(ops_dot_weight + (2 * matrix) * DIM, fixed_evals + 2 * matrix * DIM)
        ef_assert_equal(ops_dot_weight + (2 * matrix + 1) * DIM, fixed_evals + (2 * matrix + 1) * DIM)

    row_init = spark_padded_memory_term(SPARK_ROW_BITS_VALUE, SPARK_COL_BITS_VALUE, mem_point, r_x, ef_zero(), beta, gamma)
    row_audit = spark_padded_memory_term(SPARK_ROW_BITS_VALUE, SPARK_COL_BITS_VALUE, mem_point, r_x, row_audit_ts, beta, gamma)
    col_init = spark_padded_memory_term(SPARK_COL_BITS_VALUE, SPARK_COL_BITS_VALUE, mem_point, r_y, ef_zero(), beta, gamma)
    col_audit = spark_padded_memory_term(SPARK_COL_BITS_VALUE, SPARK_COL_BITS_VALUE, mem_point, r_y, col_audit_ts, beta, gamma)
    ef_assert_equal(mem_evals, row_init)
    ef_assert_equal(mem_evals + DIM, row_audit)
    ef_assert_equal(mem_evals + 2 * DIM, col_init)
    ef_assert_equal(mem_evals + 3 * DIM, col_audit)
    return
