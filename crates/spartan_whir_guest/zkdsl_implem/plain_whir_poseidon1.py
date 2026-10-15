from snark_lib import *
from extension import *
from full_zk_common import *
from full_zk_production_common import *
from transcript_poseidon1 import *


OPT_STRUCTURED_ROWS = OPT_STRUCTURED_ROWS_VALUE
FIXED_ZERO_COLUMNS = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
FIXED_NONZERO_STARTS = [0, 32, 64, 96, 128, 160, 240, 248]
FIXED_NONZERO_LENGTHS = [25, 25, 25, 25, 25, 69, 5, 1]

PLAIN_A_DOMAIN_SEPARATOR = PLAIN_A_DOMAIN_SEPARATOR_PLACEHOLDER
PLAIN_B_DOMAIN_SEPARATOR = PLAIN_B_DOMAIN_SEPARATOR_PLACEHOLDER

# These constants come from the authenticated fixed/read WHIR configurations.
PLAIN_INITIAL_OOD_COUNTS = PLAIN_INITIAL_OOD_COUNTS_VALUE
PLAIN_ROUND_OOD_COUNTS = PLAIN_ROUND_OOD_COUNTS_VALUE
PLAIN_NUM_VARIABLES = PLAIN_NUM_VARIABLES_VALUE
PLAIN_STARTING_POW_BITS = PLAIN_STARTING_POW_BITS_VALUE
PLAIN_ROUND_NUM_VARIABLES = PLAIN_ROUND_NUM_VARIABLES_VALUE
PLAIN_ROUND_DOMAIN_BITS = PLAIN_ROUND_DOMAIN_BITS_VALUE
PLAIN_ROUND_GENERATORS = PLAIN_ROUND_GENERATORS_VALUE
PLAIN_ROUND_FOLDING_POW_BITS = PLAIN_ROUND_FOLDING_POW_BITS_VALUE
PLAIN_ROUND_POW_BITS = PLAIN_ROUND_POW_BITS_VALUE
PLAIN_FOLDING_FACTORS = PLAIN_FOLDING_FACTORS_VALUE
PLAIN_ROUND_QUERIES = PLAIN_QUERY_POSITIONS_VALUE
PLAIN_FINAL_QUERIES = PLAIN_FINAL_QUERY_POSITIONS_VALUE
PLAIN_FINAL_NUM_VARIABLES = PLAIN_FINAL_NUM_VARIABLES_VALUE
PLAIN_FINAL_DOMAIN_BITS = PLAIN_FINAL_DOMAIN_BITS_VALUE
PLAIN_FINAL_GENERATORS = PLAIN_FINAL_GENERATORS_VALUE
PLAIN_FINAL_POW_BITS = PLAIN_FINAL_POW_BITS_VALUE
PLAIN_FINAL_FOLDING_POW_BITS = PLAIN_FINAL_FOLDING_POW_BITS_VALUE
PLAIN_STRUCTURED_ROWS = PLAIN_STRUCTURED_ROWS_VALUE
PLAIN_FIXED_SIBLING_STORAGE = OPT_FIXED_SIBLING_STORAGE_VALUE


def copy_extension(source, destination):
    dot_product_ee(source, ef_one(), destination)
    return


def observe_plain_domain_separator(fs, profile: Const):
    current: Mut = fs
    if profile == 0:
        if OPT_TRANSCRIPT_BLOCKS == 1:
            plain_a_domain_separator_words = Array(len(PLAIN_A_DOMAIN_SEPARATOR))
            for i in unroll(0, len(PLAIN_A_DOMAIN_SEPARATOR)):
                plain_a_domain_separator_words[i] = PLAIN_A_DOMAIN_SEPARATOR[i]
            current = fs_observe_const(current, plain_a_domain_separator_words, len(PLAIN_A_DOMAIN_SEPARATOR))
        else:
            for i in unroll(0, len(PLAIN_A_DOMAIN_SEPARATOR)):
                current = fs_observe_one(current, PLAIN_A_DOMAIN_SEPARATOR[i])
    if profile == 1:
        if OPT_TRANSCRIPT_BLOCKS == 1:
            plain_b_domain_separator_words = Array(len(PLAIN_B_DOMAIN_SEPARATOR))
            for i in unroll(0, len(PLAIN_B_DOMAIN_SEPARATOR)):
                plain_b_domain_separator_words[i] = PLAIN_B_DOMAIN_SEPARATOR[i]
            current = fs_observe_const(current, plain_b_domain_separator_words, len(PLAIN_B_DOMAIN_SEPARATOR))
        else:
            for i in unroll(0, len(PLAIN_B_DOMAIN_SEPARATOR)):
                current = fs_observe_one(current, PLAIN_B_DOMAIN_SEPARATOR[i])
    return current


def parse_plain_commitment(
    proof,
    proof_start,
    root,
    fs,
    profile: Const,
    parse_ood: Const,
    num_variables: Const,
):
    current_fs: Mut = observe_plain_domain_separator(fs, profile)
    current_fs = fs_observe_const(current_fs, root, 8)
    ood_point = Array(PLAIN_INITIAL_OOD_COUNTS[profile] * num_variables * DIM)
    ood_eval = proof + proof_start + 1
    if parse_ood == 1:
        assert proof[proof_start] == PLAIN_INITIAL_OOD_COUNTS[profile]
        for sample in unroll(0, PLAIN_INITIAL_OOD_COUNTS[profile]):
            current_fs, ood_var = fs_sample_extension(current_fs)
            power: Mut = ef_copy(ood_var)
            for reverse_index in unroll(0, num_variables):
                index = num_variables - 1 - reverse_index
                copy_extension(power, ood_point + (sample * num_variables + index) * DIM)
                power = ef_square(power)
            current_fs = fs_observe_extension(current_fs, ood_eval + sample * DIM)
    return current_fs, ood_point, ood_eval


def verify_plain_sumcheck(proof, cursor_start, fs, claimed_sum, rounds: Const, pow_bits: Const):
    assert proof[cursor_start] == rounds
    wires = Array(rounds)
    for round_index in unroll(0, rounds):
        wire_offset = cursor_start + 1 + round_index * (1 + 2 * DIM)
        assert proof[wire_offset] == 2
        wires[round_index] = proof + wire_offset + 1
    pow_count_offset = cursor_start + 1 + rounds * (1 + 2 * DIM)
    pow_witnesses: Imm
    cursor_end: Imm
    if pow_bits != 0:
        assert proof[pow_count_offset] == rounds
        pow_witnesses = proof + pow_count_offset + 1
        cursor_end = pow_count_offset + 1 + rounds
    else:
        assert proof[pow_count_offset] == 0
        pow_witnesses = proof + pow_count_offset + 1
        cursor_end = pow_count_offset + 1
    randomness = Array(rounds * DIM)
    current_fs: Mut = fs
    current_claim: Mut = ef_copy(claimed_sum)
    for round_index in unroll(0, rounds):
        wire = wires[round_index]
        current_fs = fs_observe_const(current_fs, wire, 2 * DIM)
        if pow_bits != 0:
            current_fs = fs_check_pow(current_fs, pow_witnesses[round_index], pow_bits)
        current_fs, challenge = fs_sample_extension(current_fs)
        current_claim = extrapolate_01inf(
            wire,
            ef_sub(current_claim, wire),
            wire + DIM,
            challenge,
        )
        copy_extension(challenge, randomness + round_index * DIM)
    return cursor_end, current_fs, current_claim, randomness


def eq_expanded_univariate(var, point, length: Const):
    expanded = Array(length * DIM)
    power: Mut = ef_copy(var)
    for reverse_index in unroll(0, length):
        index = length - 1 - reverse_index
        copy_extension(power, expanded + index * DIM)
        power = ef_square(power)
    return eq_points(expanded, point, length)


def select_weight(base, point, length: Const):
    power: Mut = base
    result: Mut = ef_one()
    for reverse_index in unroll(0, length):
        coordinate = point + (length - 1 - reverse_index) * DIM
        factor = ef_add(ef_one(), ef_scale(coordinate, power - 1))
        result = ef_mul(result, factor)
        power *= power
    return result


def structured_base_digest(row, structure: Const):
    repeated: Imm
    if structure == 2:
        repeated = Array(8)
        for i in unroll(0, 8):
            repeated[i] = row[199]
    else:
        repeated = 0
    state: Mut = PRODUCTION_ZERO_PTR
    output = Array(8)
    for block in unroll(0, 32):
        block_ptr: Imm
        if structure == 2:
            if block < 25:
                block_ptr = row + block * 8
            else:
                block_ptr = repeated
        else:
            nonzero = 8 - FIXED_ZERO_COLUMNS[block * 8] - FIXED_ZERO_COLUMNS[block * 8 + 1] - FIXED_ZERO_COLUMNS[block * 8 + 2] - FIXED_ZERO_COLUMNS[block * 8 + 3] - FIXED_ZERO_COLUMNS[block * 8 + 4] - FIXED_ZERO_COLUMNS[block * 8 + 5] - FIXED_ZERO_COLUMNS[block * 8 + 6] - FIXED_ZERO_COLUMNS[block * 8 + 7]
            if nonzero == 8:
                block_ptr = row + block * 8
            else:
                if nonzero == 0:
                    block_ptr = PRODUCTION_ZERO_PTR
                else:
                    block_ptr = Array(8)
                    for i in unroll(0, 8):
                        if FIXED_ZERO_COLUMNS[block * 8 + i] == 1:
                            block_ptr[i] = 0
                        else:
                            block_ptr[i] = row[block * 8 + i]
        next_state: Imm
        if block == 31:
            poseidon16_permute_half(block_ptr, state + 8, output)
            next_state = output
        else:
            next_state = Array(16)
            poseidon16_permute(block_ptr, state + 8, next_state)
        state = next_state
    return output


def structured_base_fold(row, weights, tail_weight, ones, output, structure: Const):
    if structure == 1:
        partials = Array(8 * DIM)
        for chunk in unroll(0, 8):
            dot_product_be(row + FIXED_NONZERO_STARTS[chunk], weights + FIXED_NONZERO_STARTS[chunk] * DIM, partials + chunk * DIM, FIXED_NONZERO_LENGTHS[chunk])
        dot_product_be(ones, partials, output, 8)
    else:
        prefix = Array(DIM)
        tail = Array(DIM)
        dot_product_be(row, weights, prefix, 199)
        dot_product_be(row + 199, tail_weight, tail)
        add_ee(prefix, tail, output)
    return


def verify_plain_opening(
    proof,
    cursor_start,
    expected_root,
    fs,
    folding_randomness,
    folding: Const,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
    base_rows: Const,
    structure: Const,
):
    current_fs, positions = sample_sorted_queries_bounded(
        fs,
        query_count,
        domain_bits,
        max_draws,
    )
    if base_rows == 1:
        assert proof[cursor_start] == 0
    else:
        assert proof[cursor_start] == 1
    row_count_offset = cursor_start + 1
    assert proof[row_count_offset] == query_count
    rows_start = row_count_offset + 1
    row_digests = Array(query_count * 8)
    folded_values = Array(query_count * DIM)
    folding_weights = multilinear_weights(folding_randomness, folding)
    ones: Imm
    tail_weight: Imm
    if OPT_STRUCTURED_ROWS * PLAIN_STRUCTURED_ROWS * structure != 0:
        ones = Array(57)
        for i in unroll(0, 57):
            ones[i] = 1
        tail_weight = Array(DIM)
        dot_product_be(ones, folding_weights + 199 * DIM, tail_weight, 57)
    else:
        ones = 0
        tail_weight = 0
    cursor_steps = Array(query_count + 1)
    cursor_steps[0] = rows_start
    for row_index in range(0, query_count):
        row_cursor: Mut = cursor_steps[row_index]
        assert proof[row_cursor] == 2 ** folding
        row = proof + row_cursor + 1
        row_cursor += 1
        digest: Imm
        if base_rows == 1:
            row_cursor += 2 ** folding
            if OPT_STRUCTURED_ROWS * PLAIN_STRUCTURED_ROWS * structure != 0:
                digest = structured_base_digest(row, structure)
                structured_base_fold(row, folding_weights, tail_weight, ones, folded_values + row_index * DIM, structure)
            else:
                digest = base_row_digest(row, 2 ** folding)
                dot_product_be(
                    row,
                    folding_weights,
                    folded_values + row_index * DIM,
                    2 ** folding,
                )
        else:
            row_cursor += (2 ** folding) * DIM
            digest = extension_row_digest(row, 2 ** folding)
            dot_product_ee(
                row,
                folding_weights,
                folded_values + row_index * DIM,
                2 ** folding,
            )
        for i in unroll(0, 8):
            row_digests[row_index * 8 + i] = digest[i]
        cursor_steps[row_index + 1] = row_cursor
    sibling_count_offset = cursor_steps[query_count]
    sibling_count = proof[sibling_count_offset]
    siblings = proof + sibling_count_offset + 1
    cursor_end: Imm
    if PLAIN_FIXED_SIBLING_STORAGE == 1:
        capacity = fixed_merkle_sibling_capacity(query_count, domain_bits)
        assert sibling_count <= capacity
        cursor_end = sibling_count_offset + 1 + capacity * 8
    else:
        cursor_end = sibling_count_offset + 1 + sibling_count * 8
    verify_pruned_merkle_runtime(
        expected_root,
        positions,
        row_digests,
        query_count,
        domain_bits,
        siblings,
        sibling_count,
    )
    return cursor_end, current_fs, positions, folded_values


def plain_combine_continuation(claimed_sum, combination, ood_answer, folds, ood_count: Const, query_count: Const):
    # The carried claim has coefficient one; fresh constraints start at gamma.
    combination_power: Mut = ef_copy(combination)
    next_claim: Mut = ef_copy(claimed_sum)
    for sample in unroll(0, ood_count):
        next_claim = ef_add(next_claim, ef_mul(combination_power, ood_answer + sample * DIM))
        combination_power = ef_mul(combination_power, combination)
    for i in unroll(0, query_count):
        next_claim = ef_add(next_claim, ef_mul(combination_power, folds + i * DIM))
        combination_power = ef_mul(combination_power, combination)
    return next_claim


def verify_plain_round(
    proof,
    cursor_start,
    active_root,
    fs,
    claimed_sum,
    folding_randomness,
    folding: Const,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
    base_rows: Const,
    folding_pow_bits: Const,
    query_pow_bits: Const,
    next_folding: Const,
    structure: Const,
    ood_count: Const,
):
    assert proof[cursor_start] == 1
    assert proof[cursor_start + 1] == 1
    new_root = proof + cursor_start + 2
    ood_count_offset = cursor_start + 10
    assert proof[ood_count_offset] == ood_count
    ood_answer = proof + ood_count_offset + 1
    pow_witness_offset = ood_count_offset + 1 + ood_count * DIM
    opening_start = pow_witness_offset + 1

    current_fs: Mut = fs_observe_const(fs, new_root, 8)
    ood_vars = Array(ood_count * DIM)
    for sample in unroll(0, ood_count):
        current_fs, ood_var = fs_sample_extension(current_fs)
        copy_extension(ood_var, ood_vars + sample * DIM)
        current_fs = fs_observe_extension(current_fs, ood_answer + sample * DIM)
    if query_pow_bits != 0:
        current_fs = fs_check_pow(current_fs, proof[pow_witness_offset], query_pow_bits)
    current_fs, _checkpoint = fs_sample_base(current_fs)

    after_opening, current_fs, positions, folds = verify_plain_opening(
        proof,
        opening_start,
        active_root,
        current_fs,
        folding_randomness,
        folding,
        query_count,
        domain_bits,
        max_draws,
        base_rows,
        structure,
    )
    current_fs, combination = fs_sample_extension(current_fs)
    next_claim: Mut = plain_combine_continuation(claimed_sum, combination, ood_answer, folds, ood_count, query_count)

    cursor_end, current_fs, next_claim, next_randomness = verify_plain_sumcheck(
        proof,
        after_opening,
        current_fs,
        next_claim,
        next_folding,
        folding_pow_bits,
    )
    return cursor_end, current_fs, next_claim, new_root, ood_vars, combination, positions, next_randomness


def accumulate_plain_round_weight(
    weight,
    ood_var,
    local_point,
    combination,
    positions,
    query_count: Const,
    generator: Const,
    domain_bits: Const,
    local_len: Const,
    ood_count: Const,
):
    result: Mut = ef_copy(weight)
    combination_power: Mut = ef_copy(combination)
    for sample in unroll(0, ood_count):
        result = ef_add(result, ef_mul(combination_power, eq_expanded_univariate(ood_var + sample * DIM, local_point, local_len)))
        combination_power = ef_mul(combination_power, combination)
    for i in unroll(0, query_count):
        x = base_pow_index(generator, positions[i], domain_bits)
        result = ef_add(result, ef_mul(combination_power, select_weight(x, local_point, local_len)))
        combination_power = ef_mul(combination_power, combination)
    return result


def plain_evaluate_extension_table(values, point, point_len: Const):
    result: Imm
    if point_len == 0:
        result = values
    else:
        value_count = 2 ** point_len
        layers = Array(point_len * value_count * DIM)
        for round_index in unroll(0, point_len):
            source: Imm
            if round_index == 0:
                source = values
            else:
                source = layers + (round_index - 1) * value_count * DIM
            destination = layers + round_index * value_count * DIM
            active_count = 2 ** (point_len - round_index - 1)
            for i in unroll(0, active_count):
                difference = ef_sub(source + (i + active_count) * DIM, source + i * DIM)
                product = Array(DIM)
                dot_product_ee(point + round_index * DIM, difference, product)
                add_ee(source + i * DIM, product, destination + i * DIM)
        result = layers + (point_len - 1) * value_count * DIM
    return result


def verify_plain_whir(
    proof,
    proof_start,
    initial_root,
    fs,
    claim_points,
    claim_evals,
    claim_count: Const,
    direct_statement: Const,
    ood_prebound: Const,
    prebound_ood_point,
    prebound_ood_eval,
    profile: Const,
):
    num_variables = PLAIN_NUM_VARIABLES[profile]
    n_rounds = len(PLAIN_ROUND_NUM_VARIABLES[profile])
    final_num_variables = PLAIN_FINAL_NUM_VARIABLES[profile]
    final_domain_bits = PLAIN_FINAL_DOMAIN_BITS[profile]
    final_generator = PLAIN_FINAL_GENERATORS[profile]
    current_fs: Mut = fs

    initial_ood_count = PLAIN_INITIAL_OOD_COUNTS[profile]
    assert proof[proof_start] == initial_ood_count
    encoded_ood_eval = proof + proof_start + 1
    initial_sumcheck_start = proof_start + 1 + initial_ood_count * DIM
    initial_ood_point = Array(initial_ood_count * num_variables * DIM)
    if ood_prebound == 1:
        for sample in unroll(0, initial_ood_count):
            ef_assert_equal(encoded_ood_eval + sample * DIM, prebound_ood_eval + sample * DIM)
            for i in unroll(0, num_variables):
                copy_extension(prebound_ood_point + (sample * num_variables + i) * DIM, initial_ood_point + (sample * num_variables + i) * DIM)
    else:
        for sample in unroll(0, initial_ood_count):
            current_fs, ood_var = fs_sample_extension(current_fs)
            power: Mut = ef_copy(ood_var)
            for reverse_index in unroll(0, num_variables):
                index = num_variables - 1 - reverse_index
                copy_extension(power, initial_ood_point + (sample * num_variables + index) * DIM)
                power = ef_square(power)
            current_fs = fs_observe_extension(current_fs, encoded_ood_eval + sample * DIM)

    if direct_statement == 1:
        current_fs = fs_observe_one(current_fs, claim_count)
        for claim in unroll(0, claim_count):
            current_fs = fs_observe_const(
                current_fs,
                claim_points + claim * num_variables * DIM,
                num_variables * DIM,
            )
            current_fs = fs_observe_extension(current_fs, claim_evals + claim * DIM)
    else:
        for claim in unroll(0, claim_count):
            current_fs = fs_observe_extension(current_fs, claim_evals + claim * DIM)

    current_fs, initial_alpha = fs_sample_extension(current_fs)
    claimed_sum: Mut = ef_zero()
    alpha_power: Mut = ef_one()
    for claim in unroll(0, claim_count):
        claimed_sum = ef_add(
            claimed_sum,
            ef_mul(alpha_power, claim_evals + claim * DIM),
        )
        alpha_power = ef_mul(alpha_power, initial_alpha)
    for sample in unroll(0, initial_ood_count):
        claimed_sum = ef_add(claimed_sum, ef_mul(alpha_power, encoded_ood_eval + sample * DIM))
        alpha_power = ef_mul(alpha_power, initial_alpha)

    round_combinations = Array(n_rounds * DIM)
    round_ood_vars = Array(n_rounds)
    round_positions = Array(n_rounds)
    full_randomness = Array(num_variables * DIM)

    after_initial_sumcheck, current_fs, claim_after_initial, initial_randomness = verify_plain_sumcheck(
        proof,
        initial_sumcheck_start,
        current_fs,
        claimed_sum,
        PLAIN_FOLDING_FACTORS[profile][0],
        PLAIN_STARTING_POW_BITS[profile],
    )
    for i in unroll(0, PLAIN_FOLDING_FACTORS[profile][0]):
        copy_extension(initial_randomness + i * DIM, full_randomness + i * DIM)
    assert proof[after_initial_sumcheck] == n_rounds
    cursor: Mut = after_initial_sumcheck + 1
    active_root: Mut = initial_root
    folding_randomness: Mut = initial_randomness
    current_claim: Mut = claim_after_initial
    for round_index in unroll(0, n_rounds):
        base_rows: Imm
        structure: Imm
        if round_index == 0:
            base_rows = 1
            structure = 2 - direct_statement
        else:
            base_rows = 0
            structure = 0
        cursor, current_fs, current_claim, active_root, ood_var, combination, positions, folding_randomness = verify_plain_round(
            proof,
            cursor,
            active_root,
            current_fs,
            current_claim,
            folding_randomness,
            PLAIN_FOLDING_FACTORS[profile][round_index],
            PLAIN_ROUND_QUERIES[profile][round_index],
            PLAIN_ROUND_DOMAIN_BITS[profile][round_index],
            PLAIN_ROUND_QUERIES[profile][round_index] + 64,
            base_rows,
            PLAIN_ROUND_FOLDING_POW_BITS[profile][round_index],
            PLAIN_ROUND_POW_BITS[profile][round_index],
            PLAIN_FOLDING_FACTORS[profile][round_index + 1],
            structure,
            PLAIN_ROUND_OOD_COUNTS[profile][round_index],
        )
        round_ood_vars[round_index] = ood_var
        copy_extension(combination, round_combinations + round_index * DIM)
        round_positions[round_index] = positions
        point_offset = num_variables - PLAIN_ROUND_NUM_VARIABLES[profile][round_index]
        for i in unroll(0, PLAIN_FOLDING_FACTORS[profile][round_index + 1]):
            copy_extension(folding_randomness + i * DIM, full_randomness + (point_offset + i) * DIM)

    final_section_start = cursor
    assert proof[final_section_start] == 1
    assert proof[final_section_start + 1] == 2 ** final_num_variables
    final_poly = proof + final_section_start + 2
    final_pow_offset = final_section_start + 2 + (2 ** final_num_variables) * DIM
    current_fs = fs_observe_const(current_fs, final_poly, (2 ** final_num_variables) * DIM)
    if PLAIN_FINAL_POW_BITS[profile] != 0:
        current_fs = fs_check_pow(current_fs, proof[final_pow_offset], PLAIN_FINAL_POW_BITS[profile])
    final_opening_start = final_pow_offset + 1

    after_final_opening, current_fs, final_positions, final_folds = verify_plain_opening(
        proof,
        final_opening_start,
        active_root,
        current_fs,
        folding_randomness,
        PLAIN_FOLDING_FACTORS[profile][n_rounds],
        PLAIN_FINAL_QUERIES[profile],
        final_domain_bits,
        PLAIN_FINAL_QUERIES[profile] + 64,
        0,
        0,
    )
    for i in unroll(0, PLAIN_FINAL_QUERIES[profile]):
        x = base_pow_index(final_generator, final_positions[i], final_domain_bits)
        expected = evaluate_univariate_extension(final_poly, 2 ** final_num_variables, ef_from_base(x))
        ef_assert_equal(expected, final_folds + i * DIM)

    assert proof[after_final_opening] == 1
    final_sumcheck_start = after_final_opening + 1
    cursor_end, current_fs, final_claim, final_randomness = verify_plain_sumcheck(
        proof,
        final_sumcheck_start,
        current_fs,
        current_claim,
        final_num_variables,
        PLAIN_FINAL_FOLDING_POW_BITS[profile],
    )
    for i in unroll(0, final_num_variables):
        copy_extension(final_randomness + i * DIM, full_randomness + (num_variables - final_num_variables + i) * DIM)

    weight: Mut = ef_zero()
    alpha_power = ef_one()
    for claim in unroll(0, claim_count):
        weight = ef_add(
            weight,
            ef_mul(
                alpha_power,
                eq_points(
                    claim_points + claim * num_variables * DIM,
                    full_randomness,
                    num_variables,
                ),
            ),
        )
        alpha_power = ef_mul(alpha_power, initial_alpha)
    for sample in unroll(0, initial_ood_count):
        weight = ef_add(weight, ef_mul(alpha_power, eq_points(initial_ood_point + sample * num_variables * DIM, full_randomness, num_variables)))
        alpha_power = ef_mul(alpha_power, initial_alpha)
    for round_index in unroll(0, n_rounds):
        weight = accumulate_plain_round_weight(
            weight,
            round_ood_vars[round_index],
            full_randomness + (num_variables - PLAIN_ROUND_NUM_VARIABLES[profile][round_index]) * DIM,
            round_combinations + round_index * DIM,
            round_positions[round_index],
            PLAIN_ROUND_QUERIES[profile][round_index],
            PLAIN_ROUND_GENERATORS[profile][round_index],
            PLAIN_ROUND_DOMAIN_BITS[profile][round_index],
            PLAIN_ROUND_NUM_VARIABLES[profile][round_index],
            PLAIN_ROUND_OOD_COUNTS[profile][round_index],
        )

    final_value = plain_evaluate_extension_table(final_poly, final_randomness, final_num_variables)
    ef_assert_equal(final_claim, ef_mul(weight, final_value))
    return cursor_end, current_fs


def verify_plain_whir_a(
    proof,
    proof_start,
    initial_root,
    fs,
    claim_points,
    claim_evals,
    claim_count: Const,
    direct_statement: Const,
    ood_prebound: Const,
    prebound_ood_point,
    prebound_ood_eval,
):
    cursor, result_fs = verify_plain_whir(
        proof, proof_start, initial_root, fs, claim_points, claim_evals,
        claim_count, direct_statement, ood_prebound, prebound_ood_point, prebound_ood_eval, 0,
    )
    return cursor, result_fs


def verify_plain_whir_b(
    proof,
    proof_start,
    initial_root,
    fs,
    claim_points,
    claim_evals,
    claim_count: Const,
    direct_statement: Const,
    ood_prebound: Const,
    prebound_ood_point,
    prebound_ood_eval,
):
    cursor, result_fs = verify_plain_whir(
        proof, proof_start, initial_root, fs, claim_points, claim_evals,
        claim_count, direct_statement, ood_prebound, prebound_ood_point, prebound_ood_eval, 1,
    )
    return cursor, result_fs
