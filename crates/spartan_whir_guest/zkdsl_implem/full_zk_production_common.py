from snark_lib import *
from extension import *
from full_zk_common import *
from transcript_poseidon1 import *


FOLDING_SIZES_256 = [128, 64, 32, 16, 8, 4, 2, 1]
FOLDING_SIZES_32 = [16, 8, 4, 2, 1]
FOLDING_SIZES_16 = [8, 4, 2, 1]
FOLDING_SIZES_8 = [4, 2, 1]
PRODUCTION_ZERO_PTR = 8
OPT_QUERY_PRODUCT = OPT_QUERY_PRODUCT_VALUE
OPT_RADIX_PREFIX = OPT_RADIX_PREFIX_VALUE
OPT_QUERY_PERMUTATION = OPT_QUERY_PERMUTATION_VALUE
OPT_MERKLE_BITS = OPT_MERKLE_BITS_VALUE
OPT_MERKLE_PAIRED = OPT_MERKLE_PAIRED_VALUE


def fixed_merkle_sibling_capacity(query_count: Const, tree_height: Const):
    # Maximum pruned sibling frontier for at most query_count leaves.
    if tree_height == 0:
        return 0
    if 2 ** (tree_height - 1) < query_count:
        return 2 ** (tree_height - 1)
    return 2 ** log2_ceil(query_count) + (tree_height - log2_ceil(query_count) - 1) * query_count


def fs_check_pow(fs, witness, bit_count: Const):
    current: Mut = fs_observe_one(fs, witness)
    current, sampled = fs_sample_base(current)
    bits = checked_decompose_field(sampled)
    for i in unroll(0, bit_count):
        assert bits[30 - i] == 0
    return current


def sample_uniform_bits_with_decomposition(fs, bit_count: Const):
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
    return result_fs, value, bits


def sample_sorted_queries_bounded(
    fs,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
):
    current: Imm
    positions: Imm
    if OPT_QUERY_PERMUTATION == 1:
        current, positions = sample_sorted_queries_permutation(fs, query_count, domain_bits, max_draws)
    else:
        current, positions = sample_sorted_queries_quadratic(fs, query_count, domain_bits, max_draws)
    return current, positions


def verify_query_permutation(
    draws,
    first_occurrences,
    draw_bits,
    permutation,
    draw_count,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
):
    # The sampler has already checked each draw's range and the reconstruction
    # of its cached little-endian bits. This verifies ordering and multiplicity.
    assert 0 < query_count
    if domain_bits < 15:
        assert query_count <= 2**domain_bits
    assert 0 < domain_bits
    assert domain_bits <= 24
    assert query_count <= max_draws
    assert max_draws < 32768
    assert query_count <= draw_count
    assert draw_count <= max_draws
    assert first_occurrences[draw_count - 1] == 1
    inverse = Array(max_draws)
    counts = Array(max_draws + 1)
    counts[0] = 0
    sorted_queries = Array(query_count * (1 + OPT_MERKLE_BITS * domain_bits))
    for position in range(0, draw_count):
        index = permutation[position]
        assert index < draw_count
        # Distinct ranks cannot occupy one cell in write-once VM memory.
        # Together with the index bound this proves an exact permutation.
        inverse[index] = position
        first: Imm
        if position == 0:
            first = 1
        else:
            previous_index = permutation[position - 1]
            difference = draws[index] - draws[previous_index]
            # Candidates lie in [0, 2**domain_bits). A negative difference
            # wraps above this bound in KoalaBear and fails decomposition.
            difference_bits = checked_decompose_bits(difference, domain_bits)
            if difference == 0:
                assert previous_index < index
                first = 0
            else:
                first = 1
        assert first_occurrences[index] == first
        count = counts[position]
        if first == 1:
            assert count < query_count
            sorted_queries[count] = draws[index]
            if OPT_MERKLE_BITS == 1:
                for bit in unroll(0, domain_bits):
                    sorted_queries[query_count + count * domain_bits + bit] = draw_bits[index * domain_bits + bit]
        counts[position + 1] = count + first
    assert counts[draw_count] == query_count
    return sorted_queries


def sample_sorted_queries_permutation(
    fs,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
):
    draws = Array(max_draws)
    first_occurrences = Array(max_draws)
    draw_bits = Array(max_draws * domain_bits)
    counts = Array(max_draws + 1)
    counts[0] = 0
    draw_counts = Array(max_draws + 1)
    draw_counts[0] = 0
    fs_states = Array(max_draws + 1)
    fs_states[0] = fs
    for draw_index in range(0, max_draws):
        count = counts[draw_index]
        active = checked_less_than(count, query_count)
        if active == 1:
            next_fs, candidate, candidate_bits = sample_uniform_bits_with_decomposition(fs_states[draw_index], domain_bits)
            draws[draw_index] = candidate
            first: Imm
            hint_is_first_occurrence(draws, draw_index, candidate, first)
            assert first * (1 - first) == 0
            first_occurrences[draw_index] = first
            for bit in unroll(0, domain_bits):
                draw_bits[draw_index * domain_bits + bit] = candidate_bits[30 - bit]
            counts[draw_index + 1] = count + first
            draw_counts[draw_index + 1] = draw_index + 1
            fs_states[draw_index + 1] = next_fs
        else:
            counts[draw_index + 1] = count
            draw_counts[draw_index + 1] = draw_counts[draw_index]
            fs_states[draw_index + 1] = fs_states[draw_index]
    assert counts[max_draws] == query_count
    draw_count = draw_counts[max_draws]
    permutation = Array(max_draws)
    hint_sort_indices(draws, draw_count, permutation)
    positions = verify_query_permutation(
        draws, first_occurrences, draw_bits, permutation, draw_count,
        query_count, domain_bits, max_draws,
    )
    return fs_states[max_draws], positions


def sample_sorted_queries_quadratic(
    fs,
    query_count: Const,
    domain_bits: Const,
    max_draws: Const,
):
    queries = Array(query_count)
    counts = Array(max_draws + 1)
    counts[0] = 0
    fs_states = Array(max_draws + 1)
    fs_states[0] = fs
    draws = Array(max_draws)
    query_bits = Array(query_count * domain_bits)
    distinct_steps = Array(div_floor(max_draws * (max_draws + 1), 2))
    distinct_offsets = Array(max_draws + 1)
    distinct_offsets[0] = 0
    for i in range(0, max_draws):
        distinct_offsets[i + 1] = distinct_offsets[i] + i + 1

    for draw_index in range(0, max_draws):
        count = counts[draw_index]
        active = checked_less_than(count, query_count)
        if active == 1:
            next_fs, candidate, candidate_bits = sample_uniform_bits_with_decomposition(
                fs_states[draw_index],
                domain_bits,
            )
            draws[draw_index] = candidate
            fs_states[draw_index + 1] = next_fs
            distinct: Imm
            if OPT_QUERY_PRODUCT == 1:
                products = distinct_steps + distinct_offsets[draw_index]
                products[0] = 1
                for earlier in range(0, draw_index):
                    products[earlier + 1] = products[earlier] * (candidate - draws[earlier])
                distinct = products[draw_index]
            else:
                distinct_base = distinct_offsets[draw_index]
                distinct_steps[distinct_base] = 1
                for earlier in range(0, draw_index):
                    product: Mut = distinct_steps[distinct_base + earlier]
                    product *= candidate - draws[earlier]
                    distinct_steps[distinct_base + earlier + 1] = product
                distinct = distinct_steps[distinct_base + draw_index]
            next_count: Mut = count
            if distinct != 0:
                queries[count] = candidate
                for bit_index in unroll(0, domain_bits):
                    query_bits[count * domain_bits + bit_index] = candidate_bits[30 - bit_index]
                next_count += 1
            counts[draw_index + 1] = next_count
        else:
            draws[draw_index] = 0
            counts[draw_index + 1] = count
            fs_states[draw_index + 1] = fs_states[draw_index]
    assert counts[max_draws] == query_count

    orders = Array((domain_bits + 1) * query_count)
    for i in range(0, query_count):
        orders[i] = i
    if OPT_RADIX_PREFIX == 1:
        zero_prefixes = Array(domain_bits * (query_count + 1))
        for bit_index in unroll(0, domain_bits):
            source = orders + bit_index * query_count
            destination = orders + (bit_index + 1) * query_count
            prefixes = zero_prefixes + bit_index * (query_count + 1)
            prefixes[0] = 0
            for position in range(0, query_count):
                source_index = source[position]
                prefixes[position + 1] = prefixes[position] + 1 - query_bits[source_index * domain_bits + bit_index]
            zero_total = prefixes[query_count]
            for position in range(0, query_count):
                source_index = source[position]
                bit = query_bits[source_index * domain_bits + bit_index]
                destination_position: Mut = prefixes[position]
                if bit == 1:
                    destination_position = zero_total + position - prefixes[position]
                destination[destination_position] = source_index
    else:
        zero_counts = Array(domain_bits * (query_count + 1))
        zero_positions = Array(domain_bits * (query_count + 1))
        one_positions = Array(domain_bits * (query_count + 1))
        for bit_index in unroll(0, domain_bits):
            source = orders + bit_index * query_count
            destination = orders + (bit_index + 1) * query_count

            pass_base = bit_index * (query_count + 1)
            zero_counts[pass_base] = 0
            for position in range(0, query_count):
                source_index = source[position]
                bit = query_bits[source_index * domain_bits + bit_index]
                zero_counts[pass_base + position + 1] = (
                    zero_counts[pass_base + position] + 1 - bit
                )

            zero_positions[pass_base] = 0
            one_positions[pass_base] = 0
            zero_total = zero_counts[pass_base + query_count]
            for position in range(0, query_count):
                source_index = source[position]
                bit = query_bits[source_index * domain_bits + bit_index]
                zero_position = zero_positions[pass_base + position]
                one_position = one_positions[pass_base + position]
                destination_position: Mut = zero_position
                if bit == 1:
                    destination_position = zero_total + one_position
                destination[destination_position] = source_index
                zero_positions[pass_base + position + 1] = zero_position + 1 - bit
                one_positions[pass_base + position + 1] = one_position + bit

    final_order = orders + domain_bits * query_count
    # Cached bits remain in little-endian order after the sorted positions.
    sorted_queries = Array(query_count * (1 + OPT_MERKLE_BITS * domain_bits))
    for i in range(0, query_count):
        sorted_queries[i] = queries[final_order[i]]
        if OPT_MERKLE_BITS == 1:
            for bit_index in unroll(0, domain_bits):
                sorted_queries[query_count + i * domain_bits + bit_index] = (
                    query_bits[final_order[i] * domain_bits + bit_index]
                )
    return fs_states[max_draws], sorted_queries


def multilinear_weights(point, point_len: Const):
    tree = Array((2 ** (point_len + 1) - 1) * DIM)
    root = tree
    root[0] = 1
    for coefficient in unroll(1, DIM):
        root[coefficient] = 0
    for level in unroll(0, point_len):
        source = tree + (2**level - 1) * DIM
        destination = tree + (2 ** (level + 1) - 1) * DIM
        coordinate = point + (point_len - 1 - level) * DIM
        for i in unroll(0, 2**level):
            left = destination + i * DIM
            right = destination + (2**level + i) * DIM
            dot_product_ee(coordinate, source + i * DIM, right)
            for coefficient in unroll(0, DIM):
                left[coefficient] = source[i * DIM + coefficient] - right[coefficient]
    return tree + (2**point_len - 1) * DIM


def evaluate_extension_table(values, value_count: Const, point, point_len: Const):
    layers = Array(point_len * value_count * DIM)
    for round_index in unroll(0, point_len):
        source: Imm
        if round_index == 0:
            source = values
        else:
            source = layers + (round_index - 1) * value_count * DIM
        destination = layers + round_index * value_count * DIM
        active_count: Imm
        if value_count == 256:
            active_count = FOLDING_SIZES_256[round_index]
        if value_count == 32:
            active_count = FOLDING_SIZES_32[round_index]
        if value_count == 16:
            active_count = FOLDING_SIZES_16[round_index]
        if value_count == 8:
            active_count = FOLDING_SIZES_8[round_index]
        for i in unroll(0, active_count):
            difference = ef_sub(
                source + (i + active_count) * DIM,
                source + i * DIM,
            )
            product = Array(DIM)
            dot_product_ee(point + round_index * DIM, difference, product)
            add_ee(source + i * DIM, product, destination + i * DIM)
    return layers + (point_len - 1) * value_count * DIM


def evaluate_univariate_extension(coefficients, count: Const, point):
    result: Mut = ef_zero()
    for i in unroll(0, count):
        result = ef_add(
            ef_mul(result, point),
            coefficients + (count - 1 - i) * DIM,
        )
    return result


def extension_row_digest(row, extension_count: Const):
    return poseidon1_leaf_hash(row, extension_count * DIM, PRODUCTION_ZERO_PTR)


def base_row_digest(row, base_count: Const):
    return poseidon1_leaf_hash(row, base_count, PRODUCTION_ZERO_PTR)


def verify_pruned_merkle_runtime(
    expected_root,
    indices,
    row_digests,
    query_count: Const,
    tree_height: Const,
    sibling_digests,
    sibling_count,
):
    level_indices = Array((tree_height + 1) * query_count)
    level_digests = Array((tree_height + 1) * query_count * 8)
    level_counts = Array(tree_height + 1)
    level_sibling_cursors = Array(tree_height + 1)
    level_representatives: Imm
    if OPT_MERKLE_BITS == 1:
        level_representatives = Array((tree_height + 1) * query_count)
    else:
        level_representatives = 0
    level_counts[0] = query_count
    level_sibling_cursors[0] = 0
    for i in range(0, query_count):
        level_indices[i] = indices[i]
        if OPT_MERKLE_BITS == 1:
            level_representatives[i] = i
        for j in unroll(0, 8):
            level_digests[i * 8 + j] = row_digests[i * 8 + j]

    cursor_steps = Array(tree_height * (query_count + 1))
    count_steps = Array(tree_height * (query_count + 1))
    sibling_steps = Array(tree_height * (query_count + 1))
    for level in unroll(0, tree_height):
        step_base = level * (query_count + 1)
        cursor_steps[step_base] = 0
        count_steps[step_base] = 0
        sibling_steps[step_base] = level_sibling_cursors[level]
        current_indices = level_indices + level * query_count
        current_digests = level_digests + level * query_count * 8
        next_indices = level_indices + (level + 1) * query_count
        next_digests = level_digests + (level + 1) * query_count * 8
        current_count = level_counts[level]

        for step in range(0, query_count):
            cursor = cursor_steps[step_base + step]
            next_count = count_steps[step_base + step]
            sibling_cursor = sibling_steps[step_base + step]
            next_cursor: Mut = cursor
            next_sibling_cursor: Mut = sibling_cursor
            next_output_count: Mut = next_count
            has_node = checked_less_than(cursor, current_count)
            if has_node == 1:
                index = current_indices[cursor]
                parent: Imm
                parity: Imm
                if OPT_MERKLE_BITS == 1:
                    representative = level_representatives[level * query_count + cursor]
                    parity = indices[query_count + representative * tree_height + level]
                    parent = (index - parity) * 1065353217
                else:
                    parent, parity = checked_parent(index, tree_height - level)
                paired: Mut = 0
                has_next = checked_less_than(cursor + 1, current_count)
                if has_next == 1:
                    if OPT_MERKLE_BITS == 1:
                        if parity == 0:
                            if current_indices[cursor + 1] == index + 1:
                                paired = 1
                    else:
                        next_parent, next_parity = checked_parent(
                            current_indices[cursor + 1],
                            tree_height - level,
                        )
                        if next_parent == parent:
                            assert parity == 0
                            assert next_parity == 1
                            paired = 1

                parent_digest: Imm
                if paired == 1:
                    parent_digest = poseidon1_compress(
                        current_digests + cursor * 8,
                        current_digests + (cursor + 1) * 8,
                    )
                    next_cursor += 2
                else:
                    assert sibling_cursor < sibling_count
                    sibling = sibling_digests + sibling_cursor * 8
                    if parity == 0:
                        parent_digest = poseidon1_compress(current_digests + cursor * 8, sibling)
                    else:
                        parent_digest = poseidon1_compress(sibling, current_digests + cursor * 8)
                    next_sibling_cursor += 1
                    next_cursor += 1

                next_indices[next_count] = parent
                if OPT_MERKLE_BITS == 1:
                    level_representatives[(level + 1) * query_count + next_count] = (
                        level_representatives[level * query_count + cursor]
                    )
                for j in unroll(0, 8):
                    next_digests[next_count * 8 + j] = parent_digest[j]
                next_output_count += 1

            cursor_steps[step_base + step + 1] = next_cursor
            count_steps[step_base + step + 1] = next_output_count
            sibling_steps[step_base + step + 1] = next_sibling_cursor

        level_counts[level + 1] = count_steps[step_base + query_count]
        level_sibling_cursors[level + 1] = sibling_steps[step_base + query_count]

    assert level_counts[tree_height] == 1
    assert level_indices[tree_height * query_count] == 0
    assert level_sibling_cursors[tree_height] == sibling_count
    for i in unroll(0, 8):
        assert level_digests[tree_height * query_count * 8 + i] == expected_root[i]
    return


def verify_pruned_merkle_pair(
    expected_root_a,
    expected_root_b,
    indices,
    row_digests_a,
    row_digests_b,
    query_count: Const,
    tree_height: Const,
    sibling_digests_a,
    sibling_count_a,
    sibling_digests_b,
    sibling_count_b,
):
    # Equal query positions and tree heights fix the same sibling schedule.
    assert sibling_count_a == sibling_count_b
    level_indices = Array((tree_height + 1) * query_count)
    level_digests_a = Array((tree_height + 1) * query_count * 8)
    level_digests_b = Array((tree_height + 1) * query_count * 8)
    level_counts = Array(tree_height + 1)
    level_sibling_cursors = Array(tree_height + 1)
    level_representatives: Imm
    if OPT_MERKLE_BITS == 1:
        level_representatives = Array((tree_height + 1) * query_count)
    else:
        level_representatives = 0
    level_counts[0] = query_count
    level_sibling_cursors[0] = 0
    for i in range(0, query_count):
        level_indices[i] = indices[i]
        if OPT_MERKLE_BITS == 1:
            level_representatives[i] = i
        for j in unroll(0, 8):
            level_digests_a[i * 8 + j] = row_digests_a[i * 8 + j]
            level_digests_b[i * 8 + j] = row_digests_b[i * 8 + j]

    cursor_steps = Array(tree_height * (query_count + 1))
    count_steps = Array(tree_height * (query_count + 1))
    sibling_steps = Array(tree_height * (query_count + 1))
    for level in unroll(0, tree_height):
        step_base = level * (query_count + 1)
        cursor_steps[step_base] = 0
        count_steps[step_base] = 0
        sibling_steps[step_base] = level_sibling_cursors[level]
        current_indices = level_indices + level * query_count
        current_digests_a = level_digests_a + level * query_count * 8
        current_digests_b = level_digests_b + level * query_count * 8
        next_indices = level_indices + (level + 1) * query_count
        next_digests_a = level_digests_a + (level + 1) * query_count * 8
        next_digests_b = level_digests_b + (level + 1) * query_count * 8
        current_count = level_counts[level]

        for step in range(0, query_count):
            cursor = cursor_steps[step_base + step]
            next_count = count_steps[step_base + step]
            sibling_cursor = sibling_steps[step_base + step]
            next_cursor: Mut = cursor
            next_sibling_cursor: Mut = sibling_cursor
            next_output_count: Mut = next_count
            has_node = checked_less_than(cursor, current_count)
            if has_node == 1:
                index = current_indices[cursor]
                parent: Imm
                parity: Imm
                if OPT_MERKLE_BITS == 1:
                    representative = level_representatives[level * query_count + cursor]
                    parity = indices[query_count + representative * tree_height + level]
                    parent = (index - parity) * 1065353217
                else:
                    parent, parity = checked_parent(index, tree_height - level)
                paired: Mut = 0
                has_next = checked_less_than(cursor + 1, current_count)
                if has_next == 1:
                    if OPT_MERKLE_BITS == 1:
                        if parity == 0:
                            if current_indices[cursor + 1] == index + 1:
                                paired = 1
                    else:
                        next_parent, next_parity = checked_parent(
                            current_indices[cursor + 1],
                            tree_height - level,
                        )
                        if next_parent == parent:
                            assert parity == 0
                            assert next_parity == 1
                            paired = 1

                parent_digest_a: Imm
                parent_digest_b: Imm
                if paired == 1:
                    parent_digest_a = poseidon1_compress(
                        current_digests_a + cursor * 8,
                        current_digests_a + (cursor + 1) * 8,
                    )
                    parent_digest_b = poseidon1_compress(
                        current_digests_b + cursor * 8,
                        current_digests_b + (cursor + 1) * 8,
                    )
                    next_cursor += 2
                else:
                    assert sibling_cursor < sibling_count_a
                    sibling_a = sibling_digests_a + sibling_cursor * 8
                    sibling_b = sibling_digests_b + sibling_cursor * 8
                    if parity == 0:
                        parent_digest_a = poseidon1_compress(current_digests_a + cursor * 8, sibling_a)
                        parent_digest_b = poseidon1_compress(current_digests_b + cursor * 8, sibling_b)
                    else:
                        parent_digest_a = poseidon1_compress(sibling_a, current_digests_a + cursor * 8)
                        parent_digest_b = poseidon1_compress(sibling_b, current_digests_b + cursor * 8)
                    next_sibling_cursor += 1
                    next_cursor += 1

                next_indices[next_count] = parent
                if OPT_MERKLE_BITS == 1:
                    level_representatives[(level + 1) * query_count + next_count] = (
                        level_representatives[level * query_count + cursor]
                    )
                for j in unroll(0, 8):
                    next_digests_a[next_count * 8 + j] = parent_digest_a[j]
                    next_digests_b[next_count * 8 + j] = parent_digest_b[j]
                next_output_count += 1

            cursor_steps[step_base + step + 1] = next_cursor
            count_steps[step_base + step + 1] = next_output_count
            sibling_steps[step_base + step + 1] = next_sibling_cursor

        level_counts[level + 1] = count_steps[step_base + query_count]
        level_sibling_cursors[level + 1] = sibling_steps[step_base + query_count]

    assert level_counts[tree_height] == 1
    assert level_indices[tree_height * query_count] == 0
    assert level_sibling_cursors[tree_height] == sibling_count_a
    for i in unroll(0, 8):
        assert level_digests_a[tree_height * query_count * 8 + i] == expected_root_a[i]
        assert level_digests_b[tree_height * query_count * 8 + i] == expected_root_b[i]
    return
