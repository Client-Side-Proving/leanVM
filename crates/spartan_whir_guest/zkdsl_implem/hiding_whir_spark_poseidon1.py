from snark_lib import *
from extension import *
from full_zk_common import *
from full_zk_production_common import *
from plain_whir_poseidon1 import *
from transcript_poseidon1 import *


# The compiler supplies zero for the ordinary verifier and one for the candidate.
OPT_FRESH_RELATION = OPT_FRESH_RELATION_VALUE
OPT_FRESH_ROWS = OPT_FRESH_ROWS_VALUE
OPT_ROW_COUNTS = OPT_ROW_COUNTS_VALUE
OPT_UNROLL_POWERS = OPT_UNROLL_POWERS_VALUE
OPT_BLOCK_QUERY_POWERS = OPT_BLOCK_QUERY_POWERS_VALUE


MASK_BATCH_STARTS = SPARK_MASK_BATCH_STARTS_VALUE
MASK_BATCH_MEMBERS = SPARK_MASK_BATCH_MEMBERS_VALUE
MASK_BATCH_WIDTHS = SPARK_MASK_BATCH_WIDTHS_VALUE
MASK_BATCH_HEIGHTS = SPARK_MASK_BATCH_HEIGHTS_VALUE
MASK_FRESH_ROOTS = SPARK_MASK_FRESH_ROOTS_VALUE
MASK_FRESH_ROWS = SPARK_MASK_FRESH_ROWS_VALUE
MASK_FRESH_SIBLINGS = SPARK_MASK_FRESH_SIBLINGS_VALUE
MASK_CARRIED_ROOTS = SPARK_MASK_CARRIED_ROOTS_VALUE
MASK_CARRIED_ROWS = SPARK_MASK_CARRIED_ROWS_VALUE
MASK_CARRIED_SIBLINGS = SPARK_MASK_CARRIED_SIBLINGS_VALUE
MASK_GROUP_WIDTHS = SPARK_MASK_GROUP_WIDTHS_VALUE
MASK_GROUP_HEIGHTS = SPARK_MASK_GROUP_HEIGHTS_VALUE
MASK_GROUP_GENERATORS = SPARK_MASK_GROUP_GENERATORS_VALUE
MASK_GROUP_MESSAGE_LENGTHS = SPARK_MASK_GROUP_MESSAGE_LENGTHS_VALUE
MASK_GROUP_RANDOMNESS_LENGTHS = SPARK_MASK_GROUP_RANDOMNESS_LENGTHS_VALUE
MASK_GROUP_COVECTOR_OFFSETS = SPARK_MASK_GROUP_COVECTOR_OFFSETS_VALUE
MASK_GROUP_REVEAL_OFFSETS = SPARK_MASK_GROUP_REVEAL_OFFSETS_VALUE
MASK_BLINDED_MESSAGES = SPARK_MASK_BLINDED_MESSAGES_VALUE
MASK_APPLICATION_FREE_BASIS = SPARK_MASK_APPLICATION_FREE_BASIS_VALUE
MASK_OUTER_ROUNDS = SPARK_MASK_OUTER_ROUNDS_VALUE
MASK_INNER_ROUNDS = SPARK_MASK_INNER_ROUNDS_VALUE
MASK_REVEAL_LEAF_COUNT = SPARK_MASK_REVEAL_LEAF_COUNT_VALUE
MASK_REVEAL_LAYER_COUNTS = SPARK_MASK_REVEAL_LAYER_COUNTS_VALUE
MASK_GROUP_OFFSETS = SPARK_MASK_GROUP_OFFSETS_VALUE
MASK_BATCH_COLUMN_OFFSETS = SPARK_MASK_BATCH_COLUMN_OFFSETS_VALUE


RELATION_SUMCHECK_STARTS = RELATION_SUMCHECK_STARTS_VALUE
RELATION_SUMCHECK_COMMITMENTS = RELATION_SUMCHECK_COMMITMENTS_VALUE
RELATION_SUMCHECK_FOLDING = RELATION_FOLDING_FACTORS_VALUE
RELATION_SUMCHECK_POW_BITS = RELATION_FOLDING_POW_BITS_VALUE
RELATION_SUMCHECK_INV_POWERS = RELATION_FOLDING_INV_POWERS_VALUE
RELATION_FOLD_PREFIXES = RELATION_FOLD_PREFIXES_VALUE
RELATION_AFTER_FOLD_VARIABLES = RELATION_AFTER_FOLD_VARIABLES_VALUE

RELATION_ROUND_COMMITMENTS = RELATION_ROUND_COMMITMENTS_VALUE
RELATION_ROUND_MASK_COMMITMENTS = RELATION_ROUND_MASK_COMMITMENTS_VALUE
RELATION_ROUND_OOD_ANSWERS = RELATION_ROUND_OOD_ANSWERS_VALUE
RELATION_ROUND_POW_WITNESSES = RELATION_ROUND_POW_WITNESSES_VALUE
RELATION_ROUND_OPENING_STARTS = RELATION_ROUND_OPENING_STARTS_VALUE
RELATION_ROUND_OOD_COUNTS = RELATION_ROUND_OOD_COUNTS_VALUE
RELATION_ROUND_QUERY_COUNTS = RELATION_QUERY_POSITIONS_PLACEHOLDER
RELATION_ROUND_MAX_DRAWS = RELATION_MAX_DRAWS_VALUE
RELATION_ROUND_DOMAIN_BITS = RELATION_DOMAIN_BITS_VALUE
RELATION_ROUND_FOLDING = RELATION_ROUND_FOLDING_VALUE
RELATION_ROUND_GENERATORS = RELATION_GENERATORS_VALUE
RELATION_ROUND_POW_BITS = RELATION_POW_BITS_VALUE
RELATION_ROUND_BASE_ROWS = RELATION_ROUND_BASE_ROWS_VALUE
RELATION_ROUND_VARIABLES = RELATION_VARIABLES_VALUE
RELATION_ROUNDS = len(RELATION_ROUND_COMMITMENTS)
RELATION_SUMCHECKS = len(RELATION_SUMCHECK_STARTS)
MASK_GROUPS = len(MASK_GROUP_WIDTHS)
MASK_QUERY_COUNT = RELATION_MASK_QUERIES_VALUE
SOURCE_QUERY_COUNT = RELATION_SOURCE_QUERIES_VALUE
SOURCE_DOMAIN_BITS = RELATION_SOURCE_DOMAIN_BITS_VALUE
SOURCE_GENERATOR = RELATION_SOURCE_GENERATOR_VALUE
SOURCE_ENCODED_LEN = RELATION_SOURCE_ENCODED_LEN_VALUE
SOURCE_MESSAGE_LEN = RELATION_SOURCE_MESSAGE_LEN_VALUE
SOURCE_VARIABLES = RELATION_SOURCE_VARIABLES_VALUE
SOURCE_FOLDING = RELATION_SOURCE_FOLDING_VALUE
SOURCE_ROW_WIDTH = 2 ** SOURCE_FOLDING
SOURCE_ROW_STRIDE = 1 + SOURCE_ROW_WIDTH * DIM


def hiding_copy_extension(source, destination):
    for i in unroll(0, DIM):
        destination[i] = source[i]
    return


def evaluate_public_half(proof, r_y):
    fixed_zero_weight: Mut = ef_one()
    for i in unroll(1, SPARK_INNER_ROUNDS_VALUE - SPARK_PUBLIC_HALF_ACTIVE_BITS_VALUE):
        fixed_zero_weight = ef_mul(fixed_zero_weight, ef_one_minus(r_y + i * DIM))
    active_weights = eq_table(r_y + (SPARK_INNER_ROUNDS_VALUE - SPARK_PUBLIC_HALF_ACTIVE_BITS_VALUE) * DIM, SPARK_PUBLIC_HALF_ACTIVE_BITS_VALUE)
    active_eval: Mut = ef_copy(active_weights)
    for i in unroll(0, SPARK_PUBLIC_INPUTS_VALUE):
        active_eval = ef_add(active_eval, ef_scale(active_weights + (i + 1) * DIM, proof[SPARK_OFFSET_10_VALUE + i]))
    return ef_mul(fixed_zero_weight, active_eval)


def replay_relation_sumcheck(proof, fs, claimed_sum, batch: Const):
    start = RELATION_SUMCHECK_STARTS[batch]
    commitment = proof + RELATION_SUMCHECK_COMMITMENTS[batch]
    folding = RELATION_SUMCHECK_FOLDING[batch]
    pow_bits = RELATION_SUMCHECK_POW_BITS[batch]

    assert proof[start] == 3
    current_fs: Mut = fs_observe_extension(fs, claimed_sum)
    current_fs = fs_observe_const(current_fs, commitment, 8)
    current_fs = fs_observe_extension(current_fs, proof + start + 1)
    current_fs, epsilon = fs_sample_extension(current_fs)
    current_claim: Mut = ef_add(ef_mul(epsilon, claimed_sum), proof + start + 1)
    randomness = Array(folding * DIM)
    assert proof[start + 6] == folding
    round_start = start + 7
    for round_index in unroll(0, folding):
        wire_count = round_start + round_index * 11
        assert proof[wire_count] == 2
        wire = proof + wire_count + 1
        current_fs = fs_observe_const(current_fs, wire, 2 * DIM)
        pow_count = round_start + folding * 11
        if pow_bits == 0:
            assert proof[pow_count] == 0
        else:
            assert proof[pow_count] == folding
            current_fs = fs_check_pow(current_fs, proof[pow_count + 1 + round_index], pow_bits)
        current_fs, challenge = fs_sample_extension(current_fs)
        current_claim = evaluate_quadratic_wire(wire, current_claim, challenge)
        hiding_copy_extension(challenge, randomness + round_index * DIM)
    return current_fs, epsilon, current_claim, randomness


def verify_relation_round_opening(
    proof,
    fs,
    active_root,
    folding_randomness,
    round_index: Const,
):
    query_count = RELATION_ROUND_QUERY_COUNTS[round_index]
    max_draws = RELATION_ROUND_MAX_DRAWS[round_index]
    domain_bits = RELATION_ROUND_DOMAIN_BITS[round_index]
    folding = RELATION_ROUND_FOLDING[round_index]
    opening_start = RELATION_ROUND_OPENING_STARTS[round_index]
    base_rows = RELATION_ROUND_BASE_ROWS[round_index]

    current_fs, positions = sample_sorted_queries_bounded(
        fs,
        query_count,
        domain_bits,
        max_draws,
    )
    if base_rows == 1:
        assert proof[opening_start] == 0
    else:
        assert proof[opening_start] == 1
    assert proof[opening_start + 1] == query_count
    rows_start = opening_start + 2
    row_digests = Array(query_count * 8)
    folded_values = Array(query_count * DIM)
    folding_weights = multilinear_weights(folding_randomness, folding)
    cursor_steps = Array(query_count + 1)
    cursor_steps[0] = rows_start
    for row_index in range(0, query_count):
        row_cursor = cursor_steps[row_index]
        if OPT_ROW_COUNTS == 1:
            proof[row_cursor] = 2 ** RELATION_ROUND_FOLDING[round_index]
        else:
            assert proof[row_cursor] == 2 ** RELATION_ROUND_FOLDING[round_index]
        row = proof + row_cursor + 1
        digest: Imm
        next_cursor: Mut = row_cursor + 1
        if RELATION_ROUND_BASE_ROWS[round_index] == 1:
            digest = base_row_digest(row, 2 ** RELATION_ROUND_FOLDING[round_index])
            dot_product_be(row, folding_weights, folded_values + row_index * DIM, 2 ** RELATION_ROUND_FOLDING[round_index])
            next_cursor += 2 ** RELATION_ROUND_FOLDING[round_index]
        else:
            digest = extension_row_digest(row, 2 ** RELATION_ROUND_FOLDING[round_index])
            dot_product_ee(row, folding_weights, folded_values + row_index * DIM, 2 ** RELATION_ROUND_FOLDING[round_index])
            next_cursor += (2 ** RELATION_ROUND_FOLDING[round_index]) * DIM
        for i in unroll(0, 8):
            row_digests[row_index * 8 + i] = digest[i]
        cursor_steps[row_index + 1] = next_cursor

    sibling_count_offset = cursor_steps[query_count]
    sibling_count = proof[sibling_count_offset]
    verify_pruned_merkle_runtime(
        active_root,
        positions,
        row_digests,
        query_count,
        domain_bits,
        proof + sibling_count_offset + 1,
        sibling_count,
    )
    return current_fs, positions, folded_values


def verify_relation_round(proof, fs, active_root, target, randomness, round_index: Const):
    commitment = proof + RELATION_ROUND_COMMITMENTS[round_index]
    mask_commitment = proof + RELATION_ROUND_MASK_COMMITMENTS[round_index]
    ood_answer = proof + RELATION_ROUND_OOD_ANSWERS[round_index]
    query_count = RELATION_ROUND_QUERY_COUNTS[round_index]
    domain_bits = RELATION_ROUND_DOMAIN_BITS[round_index]

    current_fs: Mut = fs_observe_const(fs, commitment, 8)
    current_fs = fs_observe_const(current_fs, mask_commitment, 8)
    ood_count = RELATION_ROUND_OOD_COUNTS[round_index]
    assert proof[RELATION_ROUND_OOD_ANSWERS[round_index] - 1] == ood_count
    ood_points = Array(ood_count * DIM)
    for sample in unroll(0, ood_count):
        current_fs, ood_point = fs_sample_extension(current_fs)
        hiding_copy_extension(ood_point, ood_points + sample * DIM)
        current_fs = fs_observe_extension(current_fs, ood_answer + sample * DIM)
    if RELATION_ROUND_POW_BITS[round_index] != 0:
        current_fs = fs_check_pow(
            current_fs,
            proof[RELATION_ROUND_POW_WITNESSES[round_index]],
            RELATION_ROUND_POW_BITS[round_index],
        )
    current_fs, _checkpoint = fs_sample_base(current_fs)
    current_fs, positions, folded_values = verify_relation_round_opening(
        proof,
        current_fs,
        active_root,
        randomness,
        round_index,
    )

    query_points = Array(query_count * DIM)
    for i in range(0, query_count):
        base_point = base_pow_index(RELATION_ROUND_GENERATORS[round_index], positions[i], RELATION_ROUND_DOMAIN_BITS[round_index])
        hiding_copy_extension(ef_from_base(base_point), query_points + i * DIM)

    current_fs, combination = fs_sample_extension(current_fs)
    coefficients = Array((query_count + ood_count + 1) * DIM)
    target_steps = Array((query_count + ood_count + 1) * DIM)
    hiding_copy_extension(combination, coefficients)
    hiding_copy_extension(target, target_steps)
    for sample in unroll(0, ood_count):
        coefficient = coefficients + sample * DIM
        hiding_copy_extension(ef_mul(coefficient, combination), coefficients + (sample + 1) * DIM)
        hiding_copy_extension(ef_add(target_steps + sample * DIM, ef_mul(coefficient, ood_answer + sample * DIM)), target_steps + (sample + 1) * DIM)
    for query in range(0, query_count):
        index = ood_count + query
        coefficient = coefficients + index * DIM
        hiding_copy_extension(ef_mul(coefficient, combination), coefficients + (index + 1) * DIM)
        hiding_copy_extension(ef_add(target_steps + index * DIM, ef_mul(coefficient, folded_values + query * DIM)), target_steps + (index + 1) * DIM)
    return current_fs, target_steps + (query_count + ood_count) * DIM, commitment, mask_commitment, ood_points, query_points, coefficients


def verify_hiding_whir_rounds(proof, fs, relation_target):
    assert proof[SPARK_OFFSET_390151_VALUE] == RELATION_SUMCHECKS
    assert proof[SPARK_OFFSET_390344_VALUE] == RELATION_SUMCHECKS
    assert proof[SPARK_OFFSET_390372_VALUE] == RELATION_ROUNDS
    random_points = Array(RELATION_SUMCHECKS)
    epsilons = Array(RELATION_SUMCHECKS)
    ood_points = Array(RELATION_ROUNDS)
    queries = Array(RELATION_ROUNDS)
    coefficients = Array(RELATION_ROUNDS)
    current_fs: Mut = fs
    target: Mut = relation_target
    active_root: Mut = proof + SPARK_OFFSET_267_VALUE
    for batch in unroll(0, RELATION_SUMCHECKS):
        current_fs, epsilon, next_target, randomness = replay_relation_sumcheck(proof, current_fs, target, batch)
        random_points[batch] = randomness
        epsilons[batch] = epsilon
        target = next_target
        if batch < RELATION_ROUNDS:
            current_fs, round_target, next_root, _mask_root, ood_point, query_points, query_coefficients = verify_relation_round(
                proof, current_fs, active_root, target, randomness, batch,
            )
            target = round_target
            active_root = next_root
            ood_points[batch] = ood_point
            queries[batch] = query_points
            coefficients[batch] = query_coefficients
    return current_fs, target, active_root, random_points, epsilons, ood_points, queries, coefficients


def fold_power_coefficient(var, coefficient, random_points, epsilons, round_index: Const):
    result: Mut = ef_copy(coefficient)
    for batch in unroll(round_index + 1, RELATION_SUMCHECKS):
        seed: Mut = ef_copy(var)
        for _ in unroll(0, RELATION_AFTER_FOLD_VARIABLES[batch]):
            seed = ef_square(seed)
        result = ef_mul(
            result,
            ef_mul(epsilons[batch], select_weight_extension(seed, random_points[batch], RELATION_SUMCHECK_FOLDING[batch])),
        )
    return result


def select_weight_extension(base, point, length: Const):
    power: Mut = ef_copy(base)
    result: Mut = ef_one()
    for reverse_index in unroll(0, length):
        coordinate = point + (length - 1 - reverse_index) * DIM
        factor = ef_add(ef_one(), ef_mul(coordinate, ef_sub(power, ef_one())))
        result = ef_mul(result, factor)
        power = ef_square(power)
    return result


def update_query_powers_blocked(previous, current, points, query_count: Const):
    # OOD powers occupy the first extension element and are updated by the caller.
    for block in range(0, div_floor(query_count, 8)):
        for offset in unroll(0, 8):
            query = block * 8 + offset
            hiding_copy_extension(
                ef_mul(previous + (query + 1) * DIM, points + query * DIM),
                current + (query + 1) * DIM,
            )
    for query in unroll(div_floor(query_count, 8) * 8, query_count):
        hiding_copy_extension(
            ef_mul(previous + (query + 1) * DIM, points + query * DIM),
            current + (query + 1) * DIM,
        )
    return


def source_round_covector(random_points, epsilons, ood_points, query_points, coefficients, round_index: Const, query_count: Const, ood_count: Const):
    point_count = query_count + ood_count
    final_coefficients = Array(point_count * DIM)
    for sample in unroll(0, ood_count):
        hiding_copy_extension(
            fold_power_coefficient(ood_points + sample * DIM, coefficients + sample * DIM, random_points, epsilons, round_index),
            final_coefficients + sample * DIM,
        )
    for query in range(0, query_count):
        hiding_copy_extension(
            fold_power_coefficient(query_points + query * DIM, coefficients + (query + ood_count) * DIM, random_points, epsilons, round_index),
            final_coefficients + (query + ood_count) * DIM,
        )
    powers = Array(SOURCE_MESSAGE_LEN * point_count * DIM)
    for point in range(0, point_count):
        hiding_copy_extension(ef_one(), powers + point * DIM)
    for slot in range(1, SOURCE_MESSAGE_LEN):
        previous = powers + (slot - 1) * point_count * DIM
        current = powers + slot * point_count * DIM
        for sample in unroll(0, ood_count):
            hiding_copy_extension(ef_mul(previous + sample * DIM, ood_points + sample * DIM), current + sample * DIM)
        if OPT_BLOCK_QUERY_POWERS == 1:
            update_query_powers_blocked(previous + (ood_count - 1) * DIM, current + (ood_count - 1) * DIM, query_points, query_count)
        else:
            for query in range(0, query_count):
                hiding_copy_extension(
                    ef_mul(previous + (query + ood_count) * DIM, query_points + query * DIM),
                    current + (query + ood_count) * DIM,
                )
    result = Array(SOURCE_MESSAGE_LEN * DIM)
    for slot in range(0, SOURCE_MESSAGE_LEN):
        dot_product_ee(final_coefficients, powers + slot * point_count * DIM, result + slot * DIM, query_count + ood_count)
    return result


def build_source_covector(r_y, relation_coefficient, random_points, epsilons, ood_points, queries, coefficients):
    eq_coefficient: Mut = ef_copy(relation_coefficient)
    for batch in unroll(0, RELATION_SUMCHECKS):
        eq_coefficient = ef_mul(
            eq_coefficient,
            ef_mul(eq_points(r_y + (1 + RELATION_FOLD_PREFIXES[batch]) * DIM, random_points[batch], RELATION_SUMCHECK_FOLDING[batch]), epsilons[batch]),
        )
    eq_weights = eq_table(r_y + (1 + RELATION_FOLD_PREFIXES[RELATION_SUMCHECKS]) * DIM, SOURCE_VARIABLES)
    source = Array(SOURCE_MESSAGE_LEN * DIM)
    for slot in range(0, SOURCE_MESSAGE_LEN):
        hiding_copy_extension(ef_mul(eq_coefficient, eq_weights + slot * DIM), source + slot * DIM)
    current_source: Mut = source
    for round_index in unroll(0, RELATION_ROUNDS):
        round_values = source_round_covector(random_points, epsilons, ood_points[round_index], queries[round_index], coefficients[round_index], round_index, RELATION_ROUND_QUERY_COUNTS[round_index], RELATION_ROUND_OOD_COUNTS[round_index])
        next_source = Array(SOURCE_MESSAGE_LEN * DIM)
        for slot in range(0, SOURCE_MESSAGE_LEN):
            hiding_copy_extension(ef_add(current_source + slot * DIM, round_values + slot * DIM), next_source + slot * DIM)
        current_source = next_source
    return current_source


def build_switch_covector(
    destination, message_power: Const, query_count: Const, ood_count: Const,
    ood_points, coefficients, query_points, scale,
):
    vector_len = query_count + ood_count
    point_count = query_count + ood_count
    powers = Array(vector_len * point_count * DIM)
    for sample in unroll(0, ood_count):
        start: Mut = ef_copy(ood_points + sample * DIM)
        for _ in unroll(0, message_power):
            start = ef_square(start)
        hiding_copy_extension(start, powers + sample * DIM)
    for query in range(0, query_count):
        start: Mut = ef_copy(query_points + query * DIM)
        for _ in unroll(0, message_power):
            start = ef_square(start)
        hiding_copy_extension(start, powers + (query + ood_count) * DIM)
    for slot in range(1, vector_len):
        previous = powers + (slot - 1) * point_count * DIM
        current = powers + slot * point_count * DIM
        for sample in unroll(0, ood_count):
            hiding_copy_extension(ef_mul(previous + sample * DIM, ood_points + sample * DIM), current + sample * DIM)
        if OPT_BLOCK_QUERY_POWERS == 1:
            update_query_powers_blocked(previous + (ood_count - 1) * DIM, current + (ood_count - 1) * DIM, query_points, query_count)
        else:
            for query in range(0, query_count):
                hiding_copy_extension(
                    ef_mul(previous + (query + ood_count) * DIM, query_points + query * DIM),
                    current + (query + ood_count) * DIM,
                )
    for slot in range(0, query_count):
        slot_powers = powers + slot * point_count * DIM
        total = Array(DIM)
        dot_product_ee(coefficients, slot_powers, total, query_count + ood_count)
        hiding_copy_extension(ef_mul(total, scale), destination + slot * DIM)
    for slot in range(query_count, vector_len):
        slot_powers = powers + slot * point_count * DIM
        total = Array(DIM)
        dot_product_ee(coefficients, slot_powers, total, ood_count)
        hiding_copy_extension(ef_mul(total, scale), destination + slot * DIM)
    return


def write_sumcheck_mask_covectors(destination, randomness, count: Const, scale):
    for mask in unroll(0, count):
        hiding_copy_extension(scale, destination + mask * 3 * DIM)
        hiding_copy_extension(
            ef_mul(scale, randomness + mask * DIM),
            destination + (mask * 3 + 1) * DIM,
        )
        hiding_copy_extension(
            ef_mul(scale, ef_square(randomness + mask * DIM)),
            destination + (mask * 3 + 2) * DIM,
        )
    return


def build_mask_covectors(application_covectors, sumcheck_covectors, random_points, epsilons, ood_points, queries, coefficients):
    # Each batch divides all existing mask terms by its hypercube size and
    # multiplies them by epsilon; its own fresh masks are added afterwards.
    downstream_scales = Array(RELATION_SUMCHECKS)
    scale: Mut = ef_one()
    for reverse_batch in unroll(0, RELATION_SUMCHECKS):
        batch = RELATION_SUMCHECKS - 1 - reverse_batch
        downstream_scales[batch] = scale
        scale = ef_mul(scale, ef_scale(epsilons[batch], RELATION_SUMCHECK_INV_POWERS[batch]))
    external_scale = scale
    covectors = Array(MASK_GROUP_COVECTOR_OFFSETS[MASK_GROUPS] * DIM)
    if MASK_APPLICATION_FREE_BASIS == 1:
        # Each inner mask has free coefficients (linear, quadratic), with
        # cubic coefficient minus their sum and constant coefficient zero.
        for mask in unroll(0, 3 * MASK_OUTER_ROUNDS):
            logical = application_covectors + mask * 8 * DIM
            for term in unroll(0, 2):
                weight = ef_sub(logical + (term + 1) * DIM, logical + 3 * DIM)
                hiding_copy_extension(ef_mul(weight, external_scale), covectors + (mask * 2 + term) * DIM)
        for i in unroll(0, MASK_OUTER_ROUNDS * 8):
            hiding_copy_extension(
                ef_mul(application_covectors + (3 * MASK_OUTER_ROUNDS * 8 + i) * DIM, external_scale),
                covectors + (3 * MASK_OUTER_ROUNDS * 2 + i) * DIM,
            )
    else:
        for i in unroll(0, 4 * MASK_OUTER_ROUNDS * 8):
            hiding_copy_extension(
                ef_mul(application_covectors + i * DIM, external_scale),
                covectors + i * DIM,
            )
    for i in unroll(0, MASK_INNER_ROUNDS * 3):
        hiding_copy_extension(
            ef_mul(sumcheck_covectors + i * DIM, external_scale),
            covectors + (MASK_GROUP_COVECTOR_OFFSETS[1] + i) * DIM,
        )
    for batch in unroll(0, RELATION_SUMCHECKS):
        write_sumcheck_mask_covectors(
            covectors + MASK_GROUP_COVECTOR_OFFSETS[2 + 2 * batch] * DIM,
            random_points[batch], RELATION_SUMCHECK_FOLDING[batch], downstream_scales[batch],
        )
        if batch < RELATION_ROUNDS:
            build_switch_covector(
                covectors + MASK_GROUP_COVECTOR_OFFSETS[3 + 2 * batch] * DIM,
                RELATION_ROUND_VARIABLES[batch], RELATION_ROUND_QUERY_COUNTS[batch],
                RELATION_ROUND_OOD_COUNTS[batch], ood_points[batch], coefficients[batch],
                queries[batch], downstream_scales[batch],
            )
    return covectors


def build_blinded_mask_pointers(proof):
    messages = Array(MASK_GROUP_OFFSETS[MASK_GROUPS])
    randomness = Array(MASK_GROUP_OFFSETS[MASK_GROUPS])
    covector_offsets = Array(MASK_GROUP_OFFSETS[MASK_GROUPS])
    for group in unroll(0, MASK_GROUPS):
        for column in range(0, MASK_GROUP_WIDTHS[group]):
            mask = MASK_GROUP_OFFSETS[group] + column
            offset = MASK_BLINDED_MESSAGES[group] + column * ((MASK_GROUP_MESSAGE_LENGTHS[group] + MASK_GROUP_RANDOMNESS_LENGTHS[group]) * DIM + 2)
            assert proof[offset - 1] == MASK_GROUP_MESSAGE_LENGTHS[group]
            assert proof[offset + MASK_GROUP_MESSAGE_LENGTHS[group] * DIM] == MASK_GROUP_RANDOMNESS_LENGTHS[group]
            messages[mask] = proof + offset
            randomness[mask] = proof + offset + MASK_GROUP_MESSAGE_LENGTHS[group] * DIM + 1
            covector_offsets[mask] = MASK_GROUP_COVECTOR_OFFSETS[group] + column * MASK_GROUP_MESSAGE_LENGTHS[group]
    return messages, randomness, covector_offsets


def copy_extension_block(source, destination, count: Const):
    for i in range(0, count):
        hiding_copy_extension(source + i * DIM, destination + i * DIM)
    return


def build_reveal_block(proof, mask_messages, mask_randomness):
    reveals = Array(MASK_REVEAL_LAYER_COUNTS[0] * 2 * DIM)
    copy_extension_block(proof + SPARK_OFFSET_476452_VALUE, reveals, SOURCE_MESSAGE_LEN)
    copy_extension_block(proof + SPARK_OFFSET_476773_VALUE, reveals + SOURCE_MESSAGE_LEN * DIM, SOURCE_QUERY_COUNT)
    for group in unroll(0, MASK_GROUPS):
        for column in range(0, MASK_GROUP_WIDTHS[group]):
            mask = MASK_GROUP_OFFSETS[group] + column
            destination = reveals + (MASK_GROUP_REVEAL_OFFSETS[group] + column * (MASK_GROUP_MESSAGE_LENGTHS[group] + MASK_GROUP_RANDOMNESS_LENGTHS[group])) * DIM
            copy_extension_block(mask_messages[mask], destination, MASK_GROUP_MESSAGE_LENGTHS[group])
            copy_extension_block(mask_randomness[mask], destination + MASK_GROUP_MESSAGE_LENGTHS[group] * DIM, MASK_GROUP_RANDOMNESS_LENGTHS[group])
    for i in unroll(MASK_GROUP_REVEAL_OFFSETS[MASK_GROUPS] * DIM, MASK_REVEAL_LAYER_COUNTS[0] * 2 * DIM):
        reveals[i] = 0
    return reveals


def reveal_root(reveals):
    levels = Array(len(MASK_REVEAL_LAYER_COUNTS))
    leaves = Array(MASK_REVEAL_LAYER_COUNTS[0] * 8)
    for leaf in unroll(0, MASK_REVEAL_LEAF_COUNT):
        poseidon1_leaf_hash_10_to(reveals + leaf * 2 * DIM, PRODUCTION_ZERO_PTR, leaves + leaf * 8)
    for leaf in unroll(MASK_REVEAL_LEAF_COUNT, MASK_REVEAL_LAYER_COUNTS[0]):
        for coordinate in unroll(0, 8):
            leaves[leaf * 8 + coordinate] = 0
    levels[0] = leaves
    for level in unroll(1, len(MASK_REVEAL_LAYER_COUNTS)):
        levels[level] = compress_reveal_layer(levels[level - 1], MASK_REVEAL_LAYER_COUNTS[level - 1], MASK_REVEAL_LAYER_COUNTS[level])
    return levels[len(MASK_REVEAL_LAYER_COUNTS) - 1]


def dot_extension_block(left, right, count: Const):
    result = Array(DIM)
    dot_product_ee(left, right, result, count)
    return result


def verify_base_target(
    proof,
    source_covector,
    mask_covectors,
    mask_messages,
    covector_offsets,
    target,
    gamma,
):
    dot_values = Array((MASK_GROUP_OFFSETS[MASK_GROUPS] + 1) * DIM)
    hiding_copy_extension(
        dot_extension_block(proof + SPARK_OFFSET_476452_VALUE, source_covector, SOURCE_MESSAGE_LEN),
        dot_values,
    )
    for group in unroll(0, MASK_GROUPS):
        for column in range(0, MASK_GROUP_WIDTHS[group]):
            mask = MASK_GROUP_OFFSETS[group] + column
            hiding_copy_extension(
                dot_extension_block(mask_messages[mask], mask_covectors + covector_offsets[mask] * DIM, MASK_GROUP_MESSAGE_LENGTHS[group]),
                dot_values + (mask + 1) * DIM,
            )
    ones = Array(MASK_GROUP_OFFSETS[MASK_GROUPS] + 1)
    for i in unroll(0, MASK_GROUP_OFFSETS[MASK_GROUPS] + 1):
        ones[i] = 1
    total = Array(DIM)
    dot_product_be(ones, dot_values, total, MASK_GROUP_OFFSETS[MASK_GROUPS] + 1)
    ef_assert_equal(
        total,
        ef_add(proof + SPARK_OFFSET_476446_VALUE, ef_mul(gamma, target)),
    )
    return


def extension_rows_and_digests(
    proof,
    query_count: Const,
    first_row: Const,
    row_stride: Const,
    width: Const,
):
    rows = Array(query_count)
    digests = Array(query_count * 8)
    for row_index in range(0, query_count):
        count_offset = first_row - 1 + row_index * row_stride
        if OPT_ROW_COUNTS == 1:
            proof[count_offset] = width
        else:
            assert proof[count_offset] == width
        row = proof + count_offset + 1
        rows[row_index] = row
        digest = extension_row_digest(row, width)
        for i in unroll(0, 8):
            digests[row_index * 8 + i] = digest[i]
    return rows, digests


def verify_extension_rows(
    proof,
    expected_root,
    positions,
    query_count: Const,
    tree_height: Const,
    first_row: Const,
    row_stride: Const,
    width: Const,
    sibling_count_offset: Const,
):
    rows = Array(query_count)
    digests = Array(query_count * 8)
    for row_index in range(0, query_count):
        count_offset = first_row - 1 + row_index * row_stride
        if OPT_ROW_COUNTS == 1:
            proof[count_offset] = width
        else:
            assert proof[count_offset] == width
        row = proof + count_offset + 1
        rows[row_index] = row
        digest = extension_row_digest(row, width)
        for i in unroll(0, 8):
            digests[row_index * 8 + i] = digest[i]
    sibling_count = proof[sibling_count_offset]
    verify_pruned_merkle_runtime(
        expected_root,
        positions,
        digests,
        query_count,
        tree_height,
        proof + sibling_count_offset + 1,
        sibling_count,
    )
    return rows


def extension_power_table(point, length: Const):
    powers = Array(length * DIM)
    hiding_copy_extension(ef_one(), powers)
    for i in range(1, length):
        hiding_copy_extension(
            ef_mul(powers + (i - 1) * DIM, point),
            powers + i * DIM,
        )
    return powers


def polynomial_dot(coefficients, powers, length: Const):
    result = Array(DIM)
    dot_product_ee(coefficients, powers, result, length)
    return result


def base_power_table(point, length: Const):
    powers = Array(length)
    powers[0] = 1
    # Cap each specialization's code growth; longer tables keep the runtime loop.
    if OPT_UNROLL_POWERS == 1:
        if length <= 1024:
            for i in unroll(1, length):
                powers[i] = powers[i - 1] * point
        else:
            for i in range(1, length):
                powers[i] = powers[i - 1] * point
    else:
        for i in range(1, length):
            powers[i] = powers[i - 1] * point
    return powers


def polynomial_dot_base_powers(coefficients, powers, length: Const):
    result = Array(DIM)
    dot_product_be(powers, coefficients, result, length)
    return result


def extension_row_pointers(proof, query_count: Const, first_row: Const, row_stride: Const, width: Const):
    rows = Array(query_count)
    for row_index in range(0, query_count):
        count_offset = first_row - 1 + row_index * row_stride
        if OPT_ROW_COUNTS == 1:
            proof[count_offset] = width
        else:
            assert proof[count_offset] == width
        rows[row_index] = proof + count_offset + 1
    return rows


def extension_pointer_digests(rows, query_count: Const, width: Const):
    digests = Array(query_count * 8)
    for row_index in range(0, query_count):
        digest = extension_row_digest(rows[row_index], width)
        for i in unroll(0, 8):
            digests[row_index * 8 + i] = digest[i]
    return digests


def verify_base_source_openings(proof, fs, active_root, randomness, gamma, reveals):
    current_fs, positions = sample_sorted_queries_bounded(fs, SOURCE_QUERY_COUNT, SOURCE_DOMAIN_BITS, SOURCE_QUERY_COUNT + 64)
    assert proof[SPARK_OFFSET_534804_VALUE] == 1
    assert proof[SPARK_OFFSET_534805_VALUE] == SOURCE_QUERY_COUNT
    assert proof[SPARK_OFFSET_542363_VALUE] == SOURCE_QUERY_COUNT
    source_rows: Imm
    fresh_rows: Imm
    if OPT_FRESH_ROWS == 1:
        source_rows = extension_row_pointers(proof, SOURCE_QUERY_COUNT, SPARK_OFFSET_534807_VALUE, SOURCE_ROW_STRIDE, SOURCE_ROW_WIDTH)
        fresh_rows = extension_row_pointers(proof, SOURCE_QUERY_COUNT, SPARK_OFFSET_542365_VALUE, 6, 1)
    else:
        if OPT_MERKLE_PAIRED == 1:
            source_rows, source_digests = extension_rows_and_digests(
                proof, SOURCE_QUERY_COUNT, SPARK_OFFSET_534807_VALUE, SOURCE_ROW_STRIDE, SOURCE_ROW_WIDTH,
            )
            fresh_rows, fresh_digests = extension_rows_and_digests(
                proof, SOURCE_QUERY_COUNT, SPARK_OFFSET_542365_VALUE, 6, 1,
            )
            verify_pruned_merkle_pair(
                active_root, proof + SPARK_OFFSET_476374_VALUE, positions,
                source_digests, fresh_digests, SOURCE_QUERY_COUNT, SOURCE_DOMAIN_BITS,
                proof + SPARK_OFFSET_539891_VALUE, proof[SPARK_OFFSET_539890_VALUE],
                proof + SPARK_OFFSET_543109_VALUE, proof[SPARK_OFFSET_543108_VALUE],
            )
        else:
            source_rows = verify_extension_rows(
                proof,
                active_root,
                positions,
                SOURCE_QUERY_COUNT,
                SOURCE_DOMAIN_BITS,
                SPARK_OFFSET_534807_VALUE,
                SOURCE_ROW_STRIDE,
                SOURCE_ROW_WIDTH,
                SPARK_OFFSET_539890_VALUE,
            )
            fresh_rows = verify_extension_rows(
                proof,
                proof + SPARK_OFFSET_476374_VALUE,
                positions,
                SOURCE_QUERY_COUNT,
                SOURCE_DOMAIN_BITS,
                SPARK_OFFSET_542365_VALUE,
                6,
                1,
                SPARK_OFFSET_543108_VALUE,
            )
    folding_weights = multilinear_weights(randomness, SOURCE_FOLDING)
    for i in range(0, SOURCE_QUERY_COUNT):
        source_value = Array(DIM)
        dot_product_ee(source_rows[i], folding_weights, source_value, SOURCE_ROW_WIDTH)
        base_point = base_pow_index(SOURCE_GENERATOR, positions[i], SOURCE_DOMAIN_BITS)
        powers = base_power_table(base_point, SOURCE_ENCODED_LEN)
        blinded_value = polynomial_dot_base_powers(reveals, powers, SOURCE_ENCODED_LEN)
        if OPT_FRESH_RELATION + OPT_FRESH_ROWS != 0:
            product = ef_mul(gamma, source_value)
            # All operands are already populated. The precompile enforces the
            # same five-coordinate equality against the blinded evaluation.
            add_ee(fresh_rows[i], product, blinded_value)
        else:
            ef_assert_equal(
                blinded_value,
                ef_add(fresh_rows[i], ef_mul(gamma, source_value)),
            )
    if OPT_FRESH_ROWS == 1:
        source_digests = extension_pointer_digests(source_rows, SOURCE_QUERY_COUNT, SOURCE_ROW_WIDTH)
        fresh_digests = extension_pointer_digests(fresh_rows, SOURCE_QUERY_COUNT, 1)
        if OPT_MERKLE_PAIRED == 1:
            verify_pruned_merkle_pair(
                active_root, proof + SPARK_OFFSET_476374_VALUE, positions,
                source_digests, fresh_digests, SOURCE_QUERY_COUNT, SOURCE_DOMAIN_BITS,
                proof + SPARK_OFFSET_539891_VALUE, proof[SPARK_OFFSET_539890_VALUE], proof + SPARK_OFFSET_543109_VALUE, proof[SPARK_OFFSET_543108_VALUE],
            )
        else:
            verify_pruned_merkle_runtime(active_root, positions, source_digests, SOURCE_QUERY_COUNT, SOURCE_DOMAIN_BITS, proof + SPARK_OFFSET_539891_VALUE, proof[SPARK_OFFSET_539890_VALUE])
            verify_pruned_merkle_runtime(proof + SPARK_OFFSET_476374_VALUE, positions, fresh_digests, SOURCE_QUERY_COUNT, SOURCE_DOMAIN_BITS, proof + SPARK_OFFSET_543109_VALUE, proof[SPARK_OFFSET_543108_VALUE])
    return current_fs


def mask_group_point(position, group: Const):
    return base_pow_index(MASK_GROUP_GENERATORS[group], position, MASK_GROUP_HEIGHTS[group])


def mask_power_table(point, group: Const):
    return base_power_table(point, MASK_GROUP_MESSAGE_LENGTHS[group] + MASK_GROUP_RANDOMNESS_LENGTHS[group])


def evaluate_blinded_mask(reveals, mask, powers, group: Const):
    length = MASK_GROUP_MESSAGE_LENGTHS[group] + MASK_GROUP_RANDOMNESS_LENGTHS[group]
    offset = MASK_GROUP_REVEAL_OFFSETS[group] + (mask - MASK_GROUP_OFFSETS[group]) * length
    return polynomial_dot_base_powers(reveals + offset * DIM, powers, length)


def verify_base_mask_batch(proof, fs, batch: Const, reveals, gamma):
    width = MASK_BATCH_WIDTHS[batch]
    height = MASK_BATCH_HEIGHTS[batch]
    current_fs, positions = sample_sorted_queries_bounded(fs, MASK_QUERY_COUNT, height, MASK_QUERY_COUNT + 64)
    fresh_rows = extension_row_pointers(
        proof, MASK_QUERY_COUNT, MASK_FRESH_ROWS[batch], width * DIM + 1, width,
    )
    first_group = MASK_BATCH_MEMBERS[MASK_BATCH_STARTS[batch]]
    first_width = MASK_GROUP_WIDTHS[first_group]
    first_carried_rows = extension_row_pointers(
        proof, MASK_QUERY_COUNT, MASK_CARRIED_ROWS[first_group], first_width * DIM + 1, first_width,
    )
    for member in unroll(MASK_BATCH_STARTS[batch], MASK_BATCH_STARTS[batch + 1]):
        group = MASK_BATCH_MEMBERS[member]
        group_width = MASK_GROUP_WIDTHS[group]
        carried_rows: Imm
        if member == MASK_BATCH_STARTS[batch]:
            carried_rows = first_carried_rows
        else:
            carried_rows = extension_row_pointers(
                proof, MASK_QUERY_COUNT, MASK_CARRIED_ROWS[group], group_width * DIM + 1, group_width,
            )
        assert proof[MASK_CARRIED_ROWS[group] - 2] == MASK_QUERY_COUNT
        for row in range(0, MASK_QUERY_COUNT):
            point = mask_group_point(positions[row], MASK_BATCH_MEMBERS[member])
            powers = mask_power_table(point, MASK_BATCH_MEMBERS[member])
            for column in range(0, group_width):
                blinded = evaluate_blinded_mask(
                    reveals, MASK_GROUP_OFFSETS[MASK_BATCH_MEMBERS[member]] + column, powers, MASK_BATCH_MEMBERS[member],
                )
                fresh = fresh_rows[row] + (MASK_BATCH_COLUMN_OFFSETS[member] + column) * DIM
                if OPT_FRESH_RELATION + OPT_FRESH_ROWS != 0:
                    product = ef_mul(gamma, carried_rows[row] + column * DIM)
                    add_ee(fresh, product, blinded)
                else:
                    ef_assert_equal(
                        blinded, ef_add(fresh, ef_mul(gamma, carried_rows[row] + column * DIM)),
                    )
        if OPT_MERKLE_PAIRED == 0:
            carried_digests = extension_pointer_digests(carried_rows, MASK_QUERY_COUNT, group_width)
            verify_pruned_merkle_runtime(
                proof + MASK_CARRIED_ROOTS[group], positions, carried_digests, MASK_QUERY_COUNT, height,
                proof + MASK_CARRIED_SIBLINGS[group] + 1, proof[MASK_CARRIED_SIBLINGS[group]],
            )
        else:
            if member != MASK_BATCH_STARTS[batch]:
                carried_digests = extension_pointer_digests(carried_rows, MASK_QUERY_COUNT, group_width)
                verify_pruned_merkle_runtime(
                    proof + MASK_CARRIED_ROOTS[group], positions, carried_digests, MASK_QUERY_COUNT, height,
                    proof + MASK_CARRIED_SIBLINGS[group] + 1, proof[MASK_CARRIED_SIBLINGS[group]],
                )
    assert proof[MASK_FRESH_ROWS[batch] - 2] == MASK_QUERY_COUNT
    fresh_digests = extension_pointer_digests(fresh_rows, MASK_QUERY_COUNT, width)
    if OPT_MERKLE_PAIRED == 1:
        first_carried_digests = extension_pointer_digests(first_carried_rows, MASK_QUERY_COUNT, first_width)
        verify_pruned_merkle_pair(
            proof + MASK_CARRIED_ROOTS[first_group], proof + MASK_FRESH_ROOTS[batch], positions,
            first_carried_digests, fresh_digests, MASK_QUERY_COUNT, height,
            proof + MASK_CARRIED_SIBLINGS[first_group] + 1, proof[MASK_CARRIED_SIBLINGS[first_group]],
            proof + MASK_FRESH_SIBLINGS[batch] + 1, proof[MASK_FRESH_SIBLINGS[batch]],
        )
    else:
        verify_pruned_merkle_runtime(
            proof + MASK_FRESH_ROOTS[batch], positions, fresh_digests, MASK_QUERY_COUNT, height,
            proof + MASK_FRESH_SIBLINGS[batch] + 1, proof[MASK_FRESH_SIBLINGS[batch]],
        )
    return current_fs


def verify_hiding_whir_base_case(
    proof,
    fs,
    active_root,
    source_covector,
    mask_covectors,
    final_randomness,
    target,
):
    assert proof[SPARK_OFFSET_476373_VALUE] == 1
    assert proof[SPARK_OFFSET_476382_VALUE] == len(MASK_BATCH_WIDTHS)
    assert proof[SPARK_OFFSET_477393_VALUE] == MASK_GROUP_OFFSETS[MASK_GROUPS]
    assert proof[SPARK_MASK_CARRIED_COUNT_VALUE] == MASK_GROUPS
    if SPARK_MASK_SEPARATE_OPENING_VECTORS_VALUE == 1:
        assert proof[SPARK_MASK_FRESH_COUNT_VALUE] == len(MASK_BATCH_WIDTHS)
    current_fs: Mut = fs_observe_const(fs, proof + SPARK_OFFSET_476374_VALUE, 8)
    for batch in unroll(0, len(MASK_BATCH_WIDTHS)):
        assert proof[MASK_FRESH_ROOTS[batch] - 1] == 1
        current_fs = fs_observe_const(current_fs, proof + MASK_FRESH_ROOTS[batch], 8)
    current_fs = fs_observe_extension(current_fs, proof + SPARK_OFFSET_476446_VALUE)
    current_fs, gamma = fs_sample_extension(current_fs)

    mask_messages, mask_randomness, covector_offsets = build_blinded_mask_pointers(proof)
    reveals = build_reveal_block(proof, mask_messages, mask_randomness)
    reveal_digest = reveal_root(reveals)
    current_fs = fs_observe_const(current_fs, reveal_digest, 8)

    verify_base_target(
        proof,
        source_covector,
        mask_covectors,
        mask_messages,
        covector_offsets,
        target,
        gamma,
    )
    if RELATION_FINAL_POW_BITS_VALUE != 0:
        current_fs = fs_check_pow(current_fs, proof[SPARK_OFFSET_534803_VALUE], RELATION_FINAL_POW_BITS_VALUE)
    source_fs = verify_base_source_openings(
        proof,
        current_fs,
        active_root,
        final_randomness,
        gamma,
        reveals,
    )
    current_fs = source_fs

    for batch in unroll(0, len(MASK_BATCH_WIDTHS)):
        current_fs = verify_base_mask_batch(proof, current_fs, batch, reveals, gamma)
    return current_fs


def verify_hiding_whir_relation(
    proof, fs, r_y, relation_coefficient, relation_target, application_covectors, sumcheck_covectors,
):
    relation_fs, relation_residual, active_root, random_points, epsilons, ood_points, queries, coefficients = verify_hiding_whir_rounds(proof, fs, relation_target)
    source_covector = build_source_covector(r_y, relation_coefficient, random_points, epsilons, ood_points, queries, coefficients)
    mask_covectors = build_mask_covectors(application_covectors, sumcheck_covectors, random_points, epsilons, ood_points, queries, coefficients)
    return verify_hiding_whir_base_case(
        proof, relation_fs, active_root, source_covector, mask_covectors,
        random_points[RELATION_SUMCHECKS - 1], relation_residual,
    )
