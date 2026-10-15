from snark_lib import *
from extension import *
from poseidon2 import *
from transcript import *


FIELD_ORDER = 2130706433
INV_FACTORIAL = [1, 1, 1065353217, 355117739, 621456043, 1828856355, 1370162609, 1717670682]

MATRIX_A_ROWS = FULL_ZK_MATRIX_A_ROWS_PLACEHOLDER
MATRIX_A_COLUMNS = FULL_ZK_MATRIX_A_COLUMNS_PLACEHOLDER
MATRIX_A_VALUES = FULL_ZK_MATRIX_A_VALUES_PLACEHOLDER
MATRIX_B_ROWS = FULL_ZK_MATRIX_B_ROWS_PLACEHOLDER
MATRIX_B_COLUMNS = FULL_ZK_MATRIX_B_COLUMNS_PLACEHOLDER
MATRIX_B_VALUES = FULL_ZK_MATRIX_B_VALUES_PLACEHOLDER
MATRIX_C_ROWS = FULL_ZK_MATRIX_C_ROWS_PLACEHOLDER
MATRIX_C_COLUMNS = FULL_ZK_MATRIX_C_COLUMNS_PLACEHOLDER
MATRIX_C_VALUES = FULL_ZK_MATRIX_C_VALUES_PLACEHOLDER


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


def sample_uniform_bits(fs, bit_count: Const):
    # KoalaBear has p - 1 = 127 * 2^24, so the exact Plonky3 sampler rejects
    # only p - 1 for every bit width used by these WHIR configurations.
    current_0, candidate_0 = fs_sample_base(fs)
    result_fs: Mut = current_0
    sampled: Mut = candidate_0
    accepted: Mut = 0
    if candidate_0 != FIELD_ORDER - 1:
        accepted = 1
    if accepted == 0:
        current_1, candidate_1 = fs_sample_base(result_fs)
        result_fs = current_1
        sampled = candidate_1
        if candidate_1 != FIELD_ORDER - 1:
            accepted = 1
        if accepted == 0:
            current_2, candidate_2 = fs_sample_base(result_fs)
            result_fs = current_2
            sampled = candidate_2
            if candidate_2 != FIELD_ORDER - 1:
                accepted = 1
            if accepted == 0:
                current_3, candidate_3 = fs_sample_base(result_fs)
                result_fs = current_3
                sampled = candidate_3
                if candidate_3 != FIELD_ORDER - 1:
                    accepted = 1
    assert accepted == 1
    bits = checked_decompose_field(sampled)
    value: Mut = bits[30]
    for i in unroll(1, bit_count):
        value += bits[30 - i] * 2**i
    return result_fs, value


def sample_sorted_queries(fs, query_count: Const, domain_bits: Const, max_draws: Const):
    draws = Array(max_draws)
    queries = Array(query_count)
    count: Mut = 0
    current_fs: Mut = fs

    for draw_index in unroll(0, max_draws):
        active = checked_less_than(count, query_count)
        if active == 1:
            current_fs, candidate = sample_uniform_bits(current_fs, domain_bits)
            draws[draw_index] = candidate
            distinct_product: Mut = 1
            for earlier in unroll(0, draw_index):
                distinct_product *= candidate - draws[earlier]
            if distinct_product != 0:
                queries[count] = candidate
                count += 1
    assert count == query_count

    sorted_queries = Array(query_count)
    for i in unroll(0, query_count):
        rank: Mut = 0
        for j in unroll(0, query_count):
            rank += checked_less_than(queries[j], queries[i])
        sorted_queries[rank] = queries[i]
    return current_fs, sorted_queries


def evaluate_degree_seven_compact(wire, claim, challenge):
    values = Array(8 * DIM)
    for coefficient in unroll(0, DIM):
        values[coefficient] = wire[coefficient]
        values[DIM + coefficient] = claim[coefficient] - wire[coefficient]
    for point in unroll(2, 8):
        for coefficient in unroll(0, DIM):
            values[point * DIM + coefficient] = wire[(point - 1) * DIM + coefficient]

    differences = Array(8 * 8 * DIM)
    for i in unroll(0, 8 * DIM):
        differences[i] = values[i]
    for order in unroll(1, 8):
        for index in unroll(0, 8 - order):
            previous = differences + (order - 1) * 8 * DIM
            current = differences + order * 8 * DIM
            for coefficient in unroll(0, DIM):
                current[index * DIM + coefficient] = (
                    previous[(index + 1) * DIM + coefficient] - previous[index * DIM + coefficient]
                )

    result: Mut = ef_copy(values)
    falling: Mut = ef_one()
    for order in unroll(1, 8):
        falling = ef_mul(falling, ef_sub_base(challenge, order - 1))
        term = ef_scale(
            ef_mul(differences + order * 8 * DIM, falling),
            INV_FACTORIAL[order],
        )
        result = ef_add(result, term)
    return result


def evaluate_quadratic_wire(wire, claim, challenge):
    c0 = wire
    c2 = wire + DIM
    c1 = ef_sub(ef_sub(claim, ef_scale(c0, 2)), c2)
    return ef_add(c0, ef_mul(challenge, ef_add(c1, ef_mul(challenge, c2))))


def ef_pow_index(base, index, bit_count: Const):
    bits = checked_decompose_bits(index, bit_count)
    result: Mut = ef_one()
    power: Mut = ef_copy(base)
    for i in unroll(0, bit_count):
        bit = bits[bit_count - 1 - i]
        multiplied = ef_mul(result, power)
        selected = Array(DIM)
        for coefficient in unroll(0, DIM):
            selected[coefficient] = (
                bit * multiplied[coefficient] + (1 - bit) * result[coefficient]
            )
        result = selected
        power = ef_square(power)
    return result


def base_pow_index(base, index, bit_count: Const):
    bits = checked_decompose_bits(index, bit_count)
    result: Mut = 1
    power: Mut = base
    for i in unroll(0, bit_count):
        if bits[bit_count - 1 - i] == 1:
            result *= power
        power *= power
    return result


def polynomial_eval(message, message_len: Const, randomness, randomness_len: Const, point):
    result: Mut = ef_zero()
    for i in unroll(0, message_len):
        result = ef_add(ef_mul(result, point), message + (message_len - 1 - i) * DIM)
    random_eval: Mut = ef_zero()
    for i in unroll(0, randomness_len):
        random_eval = ef_add(
            ef_mul(random_eval, point),
            randomness + (randomness_len - 1 - i) * DIM,
        )
    point_to_message_len: Mut = ef_one()
    for _ in unroll(0, message_len):
        point_to_message_len = ef_mul(point_to_message_len, point)
    return ef_add(result, ef_mul(point_to_message_len, random_eval))


def evaluate_matrix_a(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_A_ROWS)):
        term = ef_scale(
            ef_mul(t_x + MATRIX_A_ROWS[i] * DIM, t_y + MATRIX_A_COLUMNS[i] * DIM),
            MATRIX_A_VALUES[i],
        )
        result = ef_add(result, term)
    return result


def evaluate_matrix_b(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_B_ROWS)):
        term = ef_scale(
            ef_mul(t_x + MATRIX_B_ROWS[i] * DIM, t_y + MATRIX_B_COLUMNS[i] * DIM),
            MATRIX_B_VALUES[i],
        )
        result = ef_add(result, term)
    return result


def evaluate_matrix_c(t_x, t_y):
    result: Mut = ef_zero()
    for i in unroll(0, len(MATRIX_C_ROWS)):
        term = ef_scale(
            ef_mul(t_x + MATRIX_C_ROWS[i] * DIM, t_y + MATRIX_C_COLUMNS[i] * DIM),
            MATRIX_C_VALUES[i],
        )
        result = ef_add(result, term)
    return result


def checked_parent(index, bit_count: Const):
    bits = checked_decompose_bits(index, bit_count)
    parent: Mut = 0
    for i in unroll(0, bit_count - 1):
        parent += bits[i] * 2 ** (bit_count - 2 - i)
    return parent, bits[bit_count - 1]


def verify_pruned_merkle(
    expected_root,
    indices,
    row_digests,
    query_count: Const,
    tree_height: Const,
    sibling_digests,
    sibling_count,
):
    current_indices: Mut = indices
    current_digests: Mut = row_digests
    current_count: Mut = query_count
    sibling_cursor: Mut = 0

    for level in unroll(0, tree_height):
        next_indices = Array(query_count)
        next_digests = Array(query_count * 8)
        next_count: Mut = 0
        cursor: Mut = 0

        for _ in unroll(0, query_count):
            has_node = checked_less_than(cursor, current_count)
            if has_node == 1:
                index = current_indices[cursor]
                parent, parity = checked_parent(index, tree_height - level)
                paired: Mut = 0
                has_next = checked_less_than(cursor + 1, current_count)
                if has_next == 1:
                    next_parent, next_parity = checked_parent(
                        current_indices[cursor + 1], tree_height - level
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
                    assert sibling_cursor < sibling_count
                    sibling = sibling_digests + sibling_cursor * 8
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
    assert sibling_cursor == sibling_count
    for i in unroll(0, 8):
        assert current_digests[i] == expected_root[i]
    return


def compress_reveal_layer(current, input_count: Const, output_count: Const):
    result = Array(output_count * 8)
    parent_count = input_count / 2
    for parent in unroll(0, parent_count):
        digest = poseidon2_compress(current + parent * 16, current + parent * 16 + 8)
        for i in unroll(0, 8):
            result[parent * 8 + i] = digest[i]
    for parent in unroll(parent_count, output_count):
        for i in unroll(0, 8):
            result[parent * 8 + i] = 0
    return result


def reveal_merkle_root(reveals):
    leaves = Array(246 * 8)
    for row in unroll(0, 246):
        digest = poseidon2_leaf_hash_10(reveals + row * 2 * DIM)
        for i in unroll(0, 8):
            leaves[row * 8 + i] = digest[i]

    current = Array(124 * 8)
    for parent in unroll(0, 123):
        digest = poseidon2_compress(leaves + parent * 16, leaves + parent * 16 + 8)
        for i in unroll(0, 8):
            current[parent * 8 + i] = digest[i]
    for i in unroll(0, 8):
        current[123 * 8 + i] = 0

    level_62 = compress_reveal_layer(current, 124, 62)
    level_32 = compress_reveal_layer(level_62, 62, 32)
    level_16 = compress_reveal_layer(level_32, 32, 16)
    level_8 = compress_reveal_layer(level_16, 16, 8)
    level_4 = compress_reveal_layer(level_8, 8, 4)
    level_2 = compress_reveal_layer(level_4, 4, 2)
    return compress_reveal_layer(level_2, 2, 1)
