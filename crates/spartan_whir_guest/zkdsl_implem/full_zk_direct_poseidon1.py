from snark_lib import *
from extension import *
from full_zk_common import *
from transcript_poseidon1 import *


CONTEXT_PREFIX = FULL_ZK_CONTEXT_PREFIX_PLACEHOLDER
RELATION_DOMAIN_SEPARATOR = FULL_ZK_RELATION_DOMAIN_SEPARATOR_PLACEHOLDER
MASK_DOMAIN_GENERATOR = FULL_ZK_MASK_DOMAIN_GENERATOR_PLACEHOLDER
SOURCE_DOMAIN_GENERATOR = FULL_ZK_SOURCE_DOMAIN_GENERATOR_PLACEHOLDER

PUBLIC_INPUT_LEN = 8
FULL_ZK_WORDS = FULL_ZK_WORDS_PLACEHOLDER
FULL_ZK_LAYOUT_CONSTANTS_PLACEHOLDER
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


def copy_extension_vector(source, destination, count: Const):
    for i in unroll(0, count * DIM):
        destination[i] = source[i]
    return


def build_application_covectors(r_x, outer_claims, outer_mask_evals, rho, batching):
    covectors = Array(8 * 8 * DIM)

    rho_squared = ef_square(rho)
    matrix_coefficients = Array(3 * DIM)
    copy_extension_vector(ef_one(), matrix_coefficients, 1)
    copy_extension_vector(rho, matrix_coefficients + DIM, 1)
    copy_extension_vector(rho_squared, matrix_coefficients + 2 * DIM, 1)

    target: Mut = ef_add(
        outer_claims,
        ef_add(ef_mul(rho, outer_claims + DIM), ef_mul(rho_squared, outer_claims + 2 * DIM)),
    )
    coefficient: Mut = ef_copy(batching)
    mask_index: Mut = 0
    for matrix in unroll(0, 3):
        for round_index in unroll(0, 2):
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
                copy_extension_vector(value, covectors + (mask_index * 8 + term) * DIM, 1)
                power = ef_mul(power, point)
            for term in unroll(4, 8):
                copy_extension_vector(
                    ef_zero(),
                    covectors + (mask_index * 8 + term) * DIM,
                    1,
                )
            coefficient = ef_mul(second_coefficient, batching)
            mask_index += 1

    for round_index in unroll(0, 2):
        point = r_x + round_index * DIM
        power: Mut = ef_one()
        for term in unroll(0, 8):
            value = ef_mul(power, coefficient)
            copy_extension_vector(value, covectors + (mask_index * 8 + term) * DIM, 1)
            power = ef_mul(power, point)
        target = ef_add(target, ef_mul(coefficient, outer_mask_evals + round_index * DIM))
        coefficient = ef_mul(coefficient, batching)
        mask_index += 1

    assert mask_index == 8
    return covectors, target


def build_inner_covectors(application_covectors, application_scale, r_y):
    result = Array(12 * 8 * DIM)
    for mask in unroll(0, 8):
        for term in unroll(0, 8):
            value = ef_mul(
                application_covectors + (mask * 8 + term) * DIM,
                application_scale,
            )
            copy_extension_vector(value, result + (mask * 8 + term) * DIM, 1)
    for mask in unroll(0, 4):
        destination = result + (8 + mask) * 8 * DIM
        copy_extension_vector(ef_one(), destination, 1)
        copy_extension_vector(r_y + mask * DIM, destination + DIM, 1)
        copy_extension_vector(ef_square(r_y + mask * DIM), destination + 2 * DIM, 1)
        for term in unroll(3, 8):
            copy_extension_vector(ef_zero(), destination + term * DIM, 1)
    return result


def build_whir_covectors(inner_covectors, whir_scale, whir_randomness):
    result = Array(13 * 8 * DIM)
    for mask in unroll(0, 12):
        for term in unroll(0, 8):
            value = ef_mul(inner_covectors + (mask * 8 + term) * DIM, whir_scale)
            copy_extension_vector(value, result + (mask * 8 + term) * DIM, 1)
    destination = result + 12 * 8 * DIM
    copy_extension_vector(ef_one(), destination, 1)
    copy_extension_vector(whir_randomness, destination + DIM, 1)
    copy_extension_vector(ef_square(whir_randomness), destination + 2 * DIM, 1)
    for term in unroll(3, 8):
        copy_extension_vector(ef_zero(), destination + term * DIM, 1)
    return result


def build_blinded_mask_pointers(proof):
    messages = Array(13)
    randomness = Array(13)
    for i in unroll(0, 8):
        offset = 381 + i * 192
        assert proof[offset] == 8
        assert proof[offset + 41] == 30
        messages[i] = proof + offset + 1
        randomness[i] = proof + offset + 42
    for i in unroll(0, 5):
        offset = 1917 + i * 167
        assert proof[offset] == 3
        assert proof[offset + 16] == 30
        messages[8 + i] = proof + offset + 1
        randomness[8 + i] = proof + offset + 17
    return messages, randomness


def build_reveal_block(proof, mask_messages, mask_randomness):
    reveals = Array(492 * DIM)
    cursor: Mut = 0
    for i in unroll(0, 4 * DIM):
        reveals[cursor * DIM + i % DIM] = proof[269 + i]
        if i % DIM == DIM - 1:
            cursor += 1
    for i in unroll(0, 18 * DIM):
        reveals[cursor * DIM + i % DIM] = proof[290 + i]
        if i % DIM == DIM - 1:
            cursor += 1
    for mask in unroll(0, 8):
        copy_extension_vector(mask_messages[mask], reveals + cursor * DIM, 8)
        cursor += 8
        copy_extension_vector(mask_randomness[mask], reveals + cursor * DIM, 30)
        cursor += 30
    for mask in unroll(8, 13):
        copy_extension_vector(mask_messages[mask], reveals + cursor * DIM, 3)
        cursor += 3
        copy_extension_vector(mask_randomness[mask], reveals + cursor * DIM, 30)
        cursor += 30
    assert cursor == 491
    for i in unroll(0, DIM):
        reveals[491 * DIM + i] = 0
    return reveals


def dot_extension_vectors(left, right, length: Const):
    result: Mut = ef_zero()
    for i in unroll(0, length):
        result = ef_add(result, ef_mul(left + i * DIM, right + i * DIM))
    return result


def mask_domain_power(index):
    generator = Array(DIM)
    for i in unroll(0, DIM):
        generator[i] = MASK_DOMAIN_GENERATOR[i]
    return ef_pow_index(generator, index, 9)


def opening_rows(proof, first_row: Const, row_stride: Const, count: Const, row_width: Const):
    rows = Array(count)
    for i in unroll(0, count):
        length_offset = first_row - 1 + i * row_stride
        assert proof[length_offset] == row_width
        rows[i] = proof + first_row + i * row_stride
    return rows


def verify_source_openings(fs, proof, whir_randomness, gamma, blinded_message, blinded_randomness):
    current_fs: Mut = fs
    current_fs, positions = sample_sorted_queries(current_fs, 18, 10, 64)
    source_rows = opening_rows(proof, SOURCE_CARRIED_FIRST_ROW, 3, 18, 2)
    source_digests = Array(18 * 8)
    for row in unroll(0, 18):
        digest = poseidon1_leaf_hash_2(source_rows[row], ZERO_PTR)
        for i in unroll(0, 8):
            source_digests[row * 8 + i] = digest[i]
    verify_pruned_merkle(proof + 12, positions, source_digests, 18, 10, proof + SOURCE_CARRIED_SIBLINGS, SOURCE_CARRIED_SIBLING_COUNT)

    fresh_rows = opening_rows(proof, SOURCE_FRESH_FIRST_ROW, 6, 18, 1)
    fresh_digests = Array(18 * 8)
    for row in unroll(0, 18):
        digest = poseidon1_leaf_hash_5(fresh_rows[row], ZERO_PTR)
        for i in unroll(0, 8):
            fresh_digests[row * 8 + i] = digest[i]
    verify_pruned_merkle(proof + 227, positions, fresh_digests, 18, 10, proof + SOURCE_FRESH_SIBLINGS, SOURCE_FRESH_SIBLING_COUNT)

    for i in unroll(0, 18):
        source_row = source_rows[i]
        source_value = ef_add(
            ef_from_base(source_row[0]),
            ef_mul(whir_randomness, ef_from_base(source_row[1] - source_row[0])),
        )
        base_point = base_pow_index(SOURCE_DOMAIN_GENERATOR, positions[i], 10)
        point = ef_from_base(base_point)
        blinded_value = polynomial_eval(blinded_message, 4, blinded_randomness, 18, point)
        expected = ef_add(fresh_rows[i], ef_mul(gamma, source_value))
        ef_assert_equal(blinded_value, expected)
    return current_fs


def verify_mask_group(
    fs,
    proof,
    carried_root,
    fresh_root,
    carried_first_row: Const,
    fresh_first_row: Const,
    row_stride: Const,
    width: Const,
    carried_siblings: Const,
    carried_sibling_count: Const,
    fresh_siblings: Const,
    fresh_sibling_count: Const,
    mask_offset: Const,
    mask_messages,
    mask_randomness,
    gamma,
):
    current_fs: Mut = fs
    current_fs, positions = sample_sorted_queries(current_fs, 30, 9, 96)
    carried_rows = opening_rows(proof, carried_first_row, row_stride, 30, width)
    fresh_rows = opening_rows(proof, fresh_first_row, row_stride, 30, width)
    carried_digests = Array(30 * 8)
    fresh_digests = Array(30 * 8)
    for row in unroll(0, 30):
        carried_digest: Imm
        fresh_digest: Imm
        if width == 8:
            carried_digest = poseidon1_leaf_hash(carried_rows[row], 8 * DIM, ZERO_PTR)
            fresh_digest = poseidon1_leaf_hash(fresh_rows[row], 8 * DIM, ZERO_PTR)
        if width == 4:
            carried_digest = poseidon1_leaf_hash_20(carried_rows[row], ZERO_PTR)
            fresh_digest = poseidon1_leaf_hash_20(fresh_rows[row], ZERO_PTR)
        if width == 1:
            carried_digest = poseidon1_leaf_hash_5(carried_rows[row], ZERO_PTR)
            fresh_digest = poseidon1_leaf_hash_5(fresh_rows[row], ZERO_PTR)
        for i in unroll(0, 8):
            carried_digests[row * 8 + i] = carried_digest[i]
            fresh_digests[row * 8 + i] = fresh_digest[i]
    verify_pruned_merkle(
        carried_root,
        positions,
        carried_digests,
        30,
        9,
        proof + carried_siblings,
        carried_sibling_count,
    )
    verify_pruned_merkle(
        fresh_root,
        positions,
        fresh_digests,
        30,
        9,
        proof + fresh_siblings,
        fresh_sibling_count,
    )

    for row in unroll(0, 30):
        point = mask_domain_power(positions[row])
        for member in unroll(0, width):
            mask = mask_offset + member
            message_len: Imm
            if mask < 8:
                message_len = 8
            else:
                message_len = 3
            blinded: Imm
            if message_len == 8:
                blinded = polynomial_eval(mask_messages[mask], 8, mask_randomness[mask], 30, point)
            else:
                blinded = polynomial_eval(mask_messages[mask], 3, mask_randomness[mask], 30, point)
            expected = ef_add(
                fresh_rows[row] + member * DIM,
                ef_mul(gamma, carried_rows[row] + member * DIM),
            )
            ef_assert_equal(blinded, expected)
    return current_fs


def verify_full_zk_direct(proof):
    assert proof[0] == 76
    assert proof[1] == 86
    assert proof[2] == 90
    assert proof[3] == 87
    assert proof[4] == 1
    assert proof[5] == 2
    assert proof[6] == 5
    assert proof[7] == 0
    assert proof[8] == FULL_ZK_WORDS
    assert proof[9] == 1
    assert proof[11] == 1
    assert proof[20] == 1
    assert proof[34] == 2
    assert proof[35] == 7
    assert proof[71] == 7
    assert proof[122] == 2
    assert proof[133] == 3
    assert proof[139] == 4
    assert proof[140] == 2
    assert proof[151] == 2
    assert proof[162] == 2
    assert proof[173] == 2
    assert proof[184] == 0
    assert proof[185] == 1
    assert proof[194] == 0
    assert proof[195] == 1
    assert proof[196] == 3
    assert proof[202] == 1
    assert proof[203] == 2
    assert proof[214] == 0
    assert proof[215] == 1
    assert proof[216] == 1
    assert proof[225] == 0
    assert proof[226] == 1
    assert proof[235] == 3
    assert proof[236] == 1
    assert proof[245] == 1
    assert proof[254] == 1
    assert proof[268] == 4
    assert proof[289] == 18
    assert proof[380] == 13
    assert proof[2752] == 0
    assert proof[2753] == 0
    FULL_ZK_OPENING_COUNTS_PLACEHOLDER

    fs: Mut = fs_new()
    for i in unroll(0, len(CONTEXT_PREFIX)):
        fs = fs_observe_one(fs, CONTEXT_PREFIX[i])
    fs = fs_observe_one(fs, proof[10])
    fs = fs_observe_const(fs, proof + 21, 8)
    for i in unroll(0, len(RELATION_DOMAIN_SEPARATOR)):
        fs = fs_observe_one(fs, RELATION_DOMAIN_SEPARATOR[i])
    fs = fs_observe_const(fs, proof + 12, 8)

    fs = fs_observe_extension(fs, proof + 29)
    fs, outer_epsilon = fs_sample_extension(fs)
    tau = Array(2 * DIM)
    fs, tau_first = fs_sample_extension(fs)
    fs, tau_second = fs_sample_extension(fs)
    copy_extension_vector(tau_first, tau, 1)
    copy_extension_vector(tau_second, tau + DIM, 1)

    outer_claim: Mut = ef_copy(proof + 29)
    r_x = Array(2 * DIM)
    for round_index in unroll(0, 2):
        wire = proof + 36 + round_index * 36
        fs = fs_observe_const(fs, wire, 7 * DIM)
        fs, challenge = fs_sample_extension(fs)
        if round_index == 1:
            assert_non_boolean(challenge)
        outer_claim = evaluate_degree_seven_compact(wire, outer_claim, challenge)
        copy_extension_vector(challenge, r_x + round_index * DIM, 1)

    outer_relation = ef_sub(ef_mul(proof + 107, proof + 112), proof + 117)
    expected_outer = ef_add(
        ef_mul(outer_epsilon, ef_mul(outer_relation, eq_points(tau, r_x, 2))),
        ef_add(proof + 123, proof + 128),
    )
    ef_assert_equal(outer_claim, expected_outer)

    fs = fs_observe_const(fs, proof + 123, 2 * DIM)
    fs = fs_observe_const(fs, proof + 107, 3 * DIM)
    fs, rho = fs_sample_extension(fs)
    fs, batching = fs_sample_extension(fs)
    application_covectors, joint_target = build_application_covectors(
        r_x, proof + 107, proof + 123, rho, batching
    )

    fs = fs_observe_extension(fs, joint_target)
    fs = fs_observe_const(fs, proof + 186, 8)
    fs = fs_observe_extension(fs, proof + 134)
    fs, inner_epsilon = fs_sample_extension(fs)
    inner_claim: Mut = ef_add(ef_mul(inner_epsilon, joint_target), proof + 134)
    r_y = Array(4 * DIM)
    for round_index in unroll(0, 4):
        wire = proof + 141 + round_index * 11
        fs = fs_observe_const(fs, wire, 2 * DIM)
        fs, challenge = fs_sample_extension(fs)
        inner_claim = evaluate_quadratic_wire(wire, inner_claim, challenge)
        copy_extension_vector(challenge, r_y + round_index * DIM, 1)

    application_scale = ef_scale(inner_epsilon, 1997537281)
    inner_covectors = build_inner_covectors(application_covectors, application_scale, r_y)

    t_x = eq_table(r_x, 2)
    t_y = eq_table(r_y, 4)
    eval_a = evaluate_matrix_a(t_x, t_y)
    eval_b = evaluate_matrix_b(t_x, t_y)
    eval_c = evaluate_matrix_c(t_x, t_y)
    matrix_eval = ef_add(eval_a, ef_add(ef_mul(rho, eval_b), ef_mul(ef_square(rho), eval_c)))

    public_eval = ef_mul(
        ef_mul(ef_one_minus(r_y + DIM), ef_one_minus(r_y + 2 * DIM)),
        ef_add(ef_one_minus(r_y + 3 * DIM), ef_scale(r_y + 3 * DIM, proof[10])),
    )
    selector = r_y
    relation_coefficient = ef_mul(
        inner_epsilon,
        ef_mul(matrix_eval, ef_one_minus(selector)),
    )
    relation_target = ef_sub(
        inner_claim,
        ef_mul(inner_epsilon, ef_mul(matrix_eval, ef_mul(selector, public_eval))),
    )

    fs = fs_observe_extension(fs, relation_target)
    fs = fs_observe_const(fs, proof + 217, 8)
    fs = fs_observe_extension(fs, proof + 197)
    fs, whir_epsilon = fs_sample_extension(fs)
    whir_claim: Mut = ef_add(ef_mul(whir_epsilon, relation_target), proof + 197)
    fs = fs_observe_const(fs, proof + 204, 2 * DIM)
    fs, whir_randomness = fs_sample_extension(fs)
    whir_claim = evaluate_quadratic_wire(proof + 204, whir_claim, whir_randomness)

    source_scale = ef_mul(
        whir_epsilon,
        ef_mul(relation_coefficient, eq_points(r_y + DIM, whir_randomness, 1)),
    )
    source_table = eq_table(r_y + 2 * DIM, 2)
    source_covector = Array(4 * DIM)
    for i in unroll(0, 4):
        copy_extension_vector(
            ef_mul(source_scale, source_table + i * DIM),
            source_covector + i * DIM,
            1,
        )

    whir_mask_scale = ef_scale(whir_epsilon, 1065353217)
    whir_covectors = build_whir_covectors(inner_covectors, whir_mask_scale, whir_randomness)

    fs = fs_observe_const(fs, proof + 227, 8)
    fs = fs_observe_const(fs, proof + 237, 8)
    fs = fs_observe_const(fs, proof + 246, 8)
    fs = fs_observe_const(fs, proof + 255, 8)
    fs = fs_observe_extension(fs, proof + 263)
    fs, gamma = fs_sample_extension(fs)

    mask_messages, mask_randomness = build_blinded_mask_pointers(proof)
    reveals = build_reveal_block(proof, mask_messages, mask_randomness)
    reveal_root = reveal_merkle_root(reveals)
    fs = fs_observe_const(fs, reveal_root, 8)

    combined: Mut = dot_extension_vectors(proof + 269, source_covector, 4)
    for mask in unroll(0, 8):
        combined = ef_add(
            combined,
            dot_extension_vectors(
                mask_messages[mask], whir_covectors + mask * 8 * DIM, 8
            ),
        )
    for mask in unroll(8, 13):
        combined = ef_add(
            combined,
            dot_extension_vectors(
                mask_messages[mask], whir_covectors + mask * 8 * DIM, 3
            ),
        )
    ef_assert_equal(combined, ef_add(proof + 263, ef_mul(gamma, whir_claim)))

    fs = verify_source_openings(
        fs, proof, whir_randomness, gamma, proof + 269, proof + 290
    )
    fs = verify_mask_group(
        fs,
        proof,
        proof + 21,
        proof + 237,
        MASK_0_CARRIED_FIRST_ROW,
        MASK_0_FRESH_FIRST_ROW,
        41,
        8,
        MASK_0_CARRIED_SIBLINGS,
        MASK_0_CARRIED_SIBLING_COUNT,
        MASK_0_FRESH_SIBLINGS,
        MASK_0_FRESH_SIBLING_COUNT,
        0,
        mask_messages,
        mask_randomness,
        gamma,
    )
    fs = verify_mask_group(
        fs,
        proof,
        proof + 186,
        proof + 246,
        MASK_1_CARRIED_FIRST_ROW,
        MASK_1_FRESH_FIRST_ROW,
        21,
        4,
        MASK_1_CARRIED_SIBLINGS,
        MASK_1_CARRIED_SIBLING_COUNT,
        MASK_1_FRESH_SIBLINGS,
        MASK_1_FRESH_SIBLING_COUNT,
        8,
        mask_messages,
        mask_randomness,
        gamma,
    )
    fs = verify_mask_group(
        fs,
        proof,
        proof + 217,
        proof + 255,
        MASK_2_CARRIED_FIRST_ROW,
        MASK_2_FRESH_FIRST_ROW,
        6,
        1,
        MASK_2_CARRIED_SIBLINGS,
        MASK_2_CARRIED_SIBLING_COUNT,
        MASK_2_FRESH_SIBLINGS,
        MASK_2_FRESH_SIBLING_COUNT,
        12,
        mask_messages,
        mask_randomness,
        gamma,
    )
    return


def main():
    build_preamble()
    public_input = 0
    proof = Array(FULL_ZK_WORDS)
    hint_witness("full_zk_words", proof)

    statement_fs: Mut = fs_new()
    statement_fs = fs_observe_one(statement_fs, 1)
    statement_fs = fs_observe_one(statement_fs, proof[10])
    digest = fs_finalize(statement_fs)
    for i in unroll(0, PUBLIC_INPUT_LEN):
        assert digest[i] == public_input[i]

    verify_full_zk_direct(proof)
    return
