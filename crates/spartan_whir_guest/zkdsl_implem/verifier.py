from snark_lib import *
from extension import *
from poseidon2 import *
from transcript import *


SPARTAN_DOMAIN_SEPARATOR = SPARTAN_DOMAIN_SEPARATOR_PLACEHOLDER
WHIR_DOMAIN_SEPARATOR = WHIR_DOMAIN_SEPARATOR_PLACEHOLDER

MATRIX_A_ROWS = MATRIX_A_ROWS_PLACEHOLDER
MATRIX_A_COLUMNS = MATRIX_A_COLUMNS_PLACEHOLDER
MATRIX_A_VALUES = MATRIX_A_VALUES_PLACEHOLDER
MATRIX_B_ROWS = MATRIX_B_ROWS_PLACEHOLDER
MATRIX_B_COLUMNS = MATRIX_B_COLUMNS_PLACEHOLDER
MATRIX_B_VALUES = MATRIX_B_VALUES_PLACEHOLDER
MATRIX_C_ROWS = MATRIX_C_ROWS_PLACEHOLDER
MATRIX_C_COLUMNS = MATRIX_C_COLUMNS_PLACEHOLDER
MATRIX_C_VALUES = MATRIX_C_VALUES_PLACEHOLDER

FIELD_ORDER = 2130706433
WHIR_FOLDED_DOMAIN_GENERATOR = WHIR_FOLDED_DOMAIN_GENERATOR_PLACEHOLDER
WHIR_QUERY_COUNT = 14
WHIR_TREE_HEIGHT = 7
WHIR_SIBLING_COUNT = WHIR_SIBLING_COUNT_PLACEHOLDER
WHIR_FINAL_SUMCHECK_OFFSET = 164 + WHIR_SIBLING_COUNT * 8


def checked_less_than(a, b):
    result: Imm
    hint_less_than(a, b, result)
    assert result * (1 - result) == 0
    if result == 1:
        assert a < b
    else:
        assert b <= a
    return result


def checked_decompose_bits(value, bit_count: Const):
    bits = Array(bit_count)
    hint_decompose_bits(value, bits, bit_count)
    reconstructed: Mut = bits[bit_count - 1]
    assert bits[bit_count - 1] * (1 - bits[bit_count - 1]) == 0
    for i in unroll(1, bit_count):
        bit = bits[bit_count - 1 - i]
        assert bit * (1 - bit) == 0
        reconstructed += bit * 2**i
    assert value == reconstructed
    return bits


def checked_decompose_field(value):
    bits = Array(31)
    hint_decompose_bits(value, bits, 31)
    for i in unroll(0, 31):
        assert bits[i] * (1 - bits[i]) == 0

    low_24: Mut = bits[30]
    for i in unroll(1, 24):
        low_24 += bits[30 - i] * 2**i

    high_7: Mut = bits[6]
    for i in unroll(1, 7):
        high_7 += bits[6 - i] * 2**i
    if high_7 == 127:
        assert low_24 == 0
    assert value == low_24 + high_7 * 2**24
    return bits


def sample_uniform_7(fs):
    next_fs, sampled = fs_sample_base(fs)
    # For KoalaBear and seven requested bits, the exact sampler rejects only p - 1.
    # The fixed M1 control transcript does not take that rejection branch.
    assert sampled != FIELD_ORDER - 1
    bits = checked_decompose_field(sampled)
    value: Mut = bits[30]
    for i in unroll(1, 7):
        value += bits[30 - i] * 2**i
    return next_fs, value


def sample_sorted_queries(fs):
    draws = Array(32)
    queries = Array(WHIR_QUERY_COUNT)
    count: Mut = 0
    current_fs: Mut = fs

    for draw_index in unroll(0, 32):
        active = checked_less_than(count, WHIR_QUERY_COUNT)
        if active == 1:
            current_fs, candidate = sample_uniform_7(current_fs)
            draws[draw_index] = candidate
            distinct_product: Mut = 1
            for earlier in unroll(0, draw_index):
                distinct_product *= candidate - draws[earlier]
            if distinct_product != 0:
                queries[count] = candidate
                count += 1
    assert count == WHIR_QUERY_COUNT

    sorted_queries = Array(WHIR_QUERY_COUNT)
    for i in unroll(0, WHIR_QUERY_COUNT):
        rank: Mut = 0
        for j in unroll(0, WHIR_QUERY_COUNT):
            rank += checked_less_than(queries[j], queries[i])
        sorted_queries[rank] = queries[i]
    return current_fs, sorted_queries


def evaluate_matrix_a(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_A_ROWS)):
        row_weight = t_x + MATRIX_A_ROWS[i] * DIM
        column_weight = t_y + MATRIX_A_COLUMNS[i] * DIM
        term = ef_scale(ef_mul(row_weight, column_weight), MATRIX_A_VALUES[i])
        result = ef_add(result, term)
    return result


def evaluate_matrix_b(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_B_ROWS)):
        row_weight = t_x + MATRIX_B_ROWS[i] * DIM
        column_weight = t_y + MATRIX_B_COLUMNS[i] * DIM
        term = ef_scale(ef_mul(row_weight, column_weight), MATRIX_B_VALUES[i])
        result = ef_add(result, term)
    return result


def evaluate_matrix_c(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_C_ROWS)):
        row_weight = t_x + MATRIX_C_ROWS[i] * DIM
        column_weight = t_y + MATRIX_C_COLUMNS[i] * DIM
        term = ef_scale(ef_mul(row_weight, column_weight), MATRIX_C_VALUES[i])
        result = ef_add(result, term)
    return result


def generator_power(index):
    bits = checked_decompose_bits(index, WHIR_TREE_HEIGHT)
    result: Mut = 1
    for i in unroll(0, WHIR_TREE_HEIGHT):
        result *= result
        if bits[i] == 1:
            result *= WHIR_FOLDED_DOMAIN_GENERATOR
    return result


def checked_parent(index, bit_count: Const):
    bits = checked_decompose_bits(index, bit_count)
    parent: Mut = 0
    for i in unroll(0, bit_count - 1):
        parent += bits[i] * 2 ** (bit_count - 2 - i)
    return parent, bits[bit_count - 1]


def verify_final_rows(proof, sorted_queries, folding_randomness, final_coefficients):
    row_digests = Array(WHIR_QUERY_COUNT * 8)
    for i in unroll(0, WHIR_QUERY_COUNT):
        row_offset = 121 + i * 3
        assert proof[row_offset] == 2
        row = proof + row_offset + 1

        folded = ef_add(
            ef_from_base(row[0]),
            ef_scale(folding_randomness, row[1] - row[0]),
        )
        domain_point = generator_power(sorted_queries[i])
        expected = ef_add(final_coefficients, ef_scale(final_coefficients + DIM, domain_point))
        ef_assert_equal(folded, expected)

        digest = poseidon2_leaf_hash(row)
        for j in unroll(0, 8):
            row_digests[i * 8 + j] = digest[j]
    return row_digests


def verify_merkle_root(proof, sorted_queries, row_digests, expected_root):
    current_indices: Mut = sorted_queries
    current_digests: Mut = row_digests
    current_count: Mut = WHIR_QUERY_COUNT
    sibling_cursor: Mut = 0

    for level in unroll(0, WHIR_TREE_HEIGHT):
        next_indices = Array(WHIR_QUERY_COUNT)
        next_digests = Array(WHIR_QUERY_COUNT * 8)
        next_count: Mut = 0
        cursor: Mut = 0

        for _ in unroll(0, WHIR_QUERY_COUNT):
            has_node = checked_less_than(cursor, current_count)
            if has_node == 1:
                index = current_indices[cursor]
                parent, parity = checked_parent(index, WHIR_TREE_HEIGHT - level)
                paired: Mut = 0
                has_next = checked_less_than(cursor + 1, current_count)
                if has_next == 1:
                    next_parent, next_parity = checked_parent(
                        current_indices[cursor + 1], WHIR_TREE_HEIGHT - level
                    )
                    if next_parent == parent:
                        assert parity == 0
                        assert next_parity == 1
                        paired = 1

                parent_digest: Imm
                if paired == 1:
                    parent_digest = poseidon2_compress(
                        current_digests + cursor * 8,
                        current_digests + (cursor + 1) * 8,
                    )
                    cursor += 2
                else:
                    sibling = proof + 164 + sibling_cursor * 8
                    if parity == 0:
                        parent_digest = poseidon2_compress(current_digests + cursor * 8, sibling)
                    else:
                        parent_digest = poseidon2_compress(sibling, current_digests + cursor * 8)
                    sibling_cursor += 1
                    cursor += 1

                next_indices[next_count] = parent
                for j in unroll(0, 8):
                    next_digests[next_count * 8 + j] = parent_digest[j]
                next_count += 1

        current_indices = next_indices
        current_digests = next_digests
        current_count = next_count

    assert current_count == 1
    assert current_indices[0] == 0
    assert sibling_cursor == WHIR_SIBLING_COUNT
    for i in unroll(0, 8):
        assert current_digests[i] == expected_root[i]
    return


def verify_control_proof(proof):
    fs: Mut = fs_new()
    for i in unroll(0, len(SPARTAN_DOMAIN_SEPARATOR)):
        fs = fs_observe_one(fs, SPARTAN_DOMAIN_SEPARATOR[i])
    fs = fs_observe_one(fs, proof[8])
    for i in unroll(0, len(WHIR_DOMAIN_SEPARATOR)):
        fs = fs_observe_one(fs, WHIR_DOMAIN_SEPARATOR[i])
    fs = fs_observe_const(fs, proof + 10, 8)

    fs, ood_alpha = fs_sample_extension(fs)
    ood_point = Array(2 * DIM)
    ood_alpha_squared = ef_square(ood_alpha)
    for i in unroll(0, DIM):
        ood_point[i] = ood_alpha_squared[i]
        ood_point[DIM + i] = ood_alpha[i]
    fs = fs_observe_extension(fs, proof + 88)

    fs, tau = fs_sample_extension(fs)

    outer_claim: Mut = ef_zero()
    fs = fs_observe_extension(fs, outer_claim)
    fs = fs_observe_extension(fs, proof + 20)
    fs = fs_observe_extension(fs, proof + 25)
    fs = fs_observe_extension(fs, proof + 30)
    fs, r_x = fs_sample_extension(fs)
    outer_claim = evaluate_cubic_compact(proof + 20, proof + 25, proof + 30, outer_claim, r_x)

    outer_relation = ef_sub(ef_mul(proof + 35, proof + 40), proof + 45)
    expected_outer = ef_mul(eq_points(tau, r_x, 1), outer_relation)
    ef_assert_equal(outer_claim, expected_outer)

    fs = fs_observe_extension(fs, proof + 35)
    fs = fs_observe_extension(fs, proof + 40)
    fs = fs_observe_extension(fs, proof + 45)
    fs, joint_randomness = fs_sample_extension(fs)
    joint_randomness_squared = ef_square(joint_randomness)
    inner_claim: Mut = ef_add(
        proof + 35,
        ef_add(
            ef_mul(joint_randomness, proof + 40),
            ef_mul(joint_randomness_squared, proof + 45),
        ),
    )

    fs = fs_observe_extension(fs, inner_claim)
    r_y = Array(3 * DIM)
    for round_index in unroll(0, 3):
        round_offset = 51 + round_index * 10
        fs = fs_observe_extension(fs, proof + round_offset)
        fs = fs_observe_extension(fs, proof + round_offset + DIM)
        fs, challenge = fs_sample_extension(fs)
        inner_claim = evaluate_quadratic_compact(
            proof + round_offset,
            proof + round_offset + DIM,
            inner_claim,
            challenge,
        )
        for i in unroll(0, DIM):
            r_y[round_index * DIM + i] = challenge[i]

    t_x = eq_table(r_x, 1)
    t_y = eq_table(r_y, 3)
    eval_a = evaluate_matrix_a(t_x, t_y)
    eval_b = evaluate_matrix_b(t_x, t_y)
    eval_c = evaluate_matrix_c(t_x, t_y)
    matrix_eval = ef_add(
        eval_a,
        ef_add(ef_mul(joint_randomness, eval_b), ef_mul(joint_randomness_squared, eval_c)),
    )

    public_eval = ef_mul(
        ef_one_minus(r_y + DIM),
        ef_add(ef_one_minus(r_y + 2 * DIM), ef_scale(r_y + 2 * DIM, proof[8])),
    )
    eval_z = ef_add(
        ef_mul(ef_one_minus(r_y), proof + 81),
        ef_mul(r_y, public_eval),
    )
    ef_assert_equal(inner_claim, ef_mul(matrix_eval, eval_z))

    fs = fs_observe_one(fs, 1)
    fs = fs_observe_extension(fs, r_y + DIM)
    fs = fs_observe_extension(fs, r_y + 2 * DIM)
    fs = fs_observe_extension(fs, proof + 81)
    fs, batching_randomness = fs_sample_extension(fs)
    whir_claim: Mut = ef_add(proof + 81, ef_mul(batching_randomness, proof + 88))

    fs = fs_observe_extension(fs, proof + 94)
    fs = fs_observe_extension(fs, proof + 99)
    fs, initial_folding_randomness = fs_sample_extension(fs)
    whir_claim = extrapolate_01inf(
        proof + 94,
        ef_sub(whir_claim, proof + 94),
        proof + 99,
        initial_folding_randomness,
    )

    fs = fs_observe_extension(fs, proof + 108)
    fs = fs_observe_extension(fs, proof + 113)
    fs, sorted_queries = sample_sorted_queries(fs)
    row_digests = verify_final_rows(proof, sorted_queries, initial_folding_randomness, proof + 108)
    verify_merkle_root(proof, sorted_queries, row_digests, proof + 10)

    fs = fs_observe_extension(fs, proof + WHIR_FINAL_SUMCHECK_OFFSET + 2)
    fs = fs_observe_extension(fs, proof + WHIR_FINAL_SUMCHECK_OFFSET + 7)
    fs, final_randomness = fs_sample_extension(fs)
    whir_claim = extrapolate_01inf(
        proof + WHIR_FINAL_SUMCHECK_OFFSET + 2,
        ef_sub(whir_claim, proof + WHIR_FINAL_SUMCHECK_OFFSET + 2),
        proof + WHIR_FINAL_SUMCHECK_OFFSET + 7,
        final_randomness,
    )

    folding_point = Array(2 * DIM)
    for i in unroll(0, DIM):
        folding_point[i] = initial_folding_randomness[i]
        folding_point[DIM + i] = final_randomness[i]
    user_weight = eq_points(r_y + DIM, folding_point, 2)
    ood_weight = eq_points(ood_point, folding_point, 2)
    combined_weight = ef_add(user_weight, ef_mul(batching_randomness, ood_weight))
    final_value = ef_add(
        ef_mul(proof + 108, ef_one_minus(final_randomness)),
        ef_mul(proof + 113, final_randomness),
    )
    ef_assert_equal(whir_claim, ef_mul(combined_weight, final_value))
    return
