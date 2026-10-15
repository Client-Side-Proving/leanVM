from snark_lib import *


POSEIDON16_EXTERNAL_INITIAL = POSEIDON16_EXTERNAL_INITIAL_PLACEHOLDER
POSEIDON16_INTERNAL = POSEIDON16_INTERNAL_PLACEHOLDER
POSEIDON16_EXTERNAL_FINAL = POSEIDON16_EXTERNAL_FINAL_PLACEHOLDER
POSEIDON16_INTERNAL_DIAGONAL = POSEIDON16_INTERNAL_DIAGONAL_PLACEHOLDER

POSEIDON24_EXTERNAL_INITIAL = POSEIDON24_EXTERNAL_INITIAL_PLACEHOLDER
POSEIDON24_INTERNAL = POSEIDON24_INTERNAL_PLACEHOLDER
POSEIDON24_EXTERNAL_FINAL = POSEIDON24_EXTERNAL_FINAL_PLACEHOLDER
POSEIDON24_INTERNAL_DIAGONAL = POSEIDON24_INTERNAL_DIAGONAL_PLACEHOLDER


@inline
def _mds_light_16(state):
    transformed = Array(16)
    for chunk in unroll(0, 4):
        base = chunk * 4
        x0 = state[base]
        x1 = state[base + 1]
        x2 = state[base + 2]
        x3 = state[base + 3]
        transformed[base] = 2 * x0 + 3 * x1 + x2 + x3
        transformed[base + 1] = x0 + 2 * x1 + 3 * x2 + x3
        transformed[base + 2] = x0 + x1 + 2 * x2 + 3 * x3
        transformed[base + 3] = 3 * x0 + x1 + x2 + 2 * x3
    sums = Array(4)
    for residue in unroll(0, 4):
        sums[residue] = (
            transformed[residue]
            + transformed[residue + 4]
            + transformed[residue + 8]
            + transformed[residue + 12]
        )
    result = Array(16)
    for i in unroll(0, 16):
        result[i] = transformed[i] + sums[i % 4]
    return result


@inline
def _mds_light_24(state):
    transformed = Array(24)
    for chunk in unroll(0, 6):
        base = chunk * 4
        x0 = state[base]
        x1 = state[base + 1]
        x2 = state[base + 2]
        x3 = state[base + 3]
        transformed[base] = 2 * x0 + 3 * x1 + x2 + x3
        transformed[base + 1] = x0 + 2 * x1 + 3 * x2 + x3
        transformed[base + 2] = x0 + x1 + 2 * x2 + 3 * x3
        transformed[base + 3] = 3 * x0 + x1 + x2 + 2 * x3
    sums = Array(4)
    for residue in unroll(0, 4):
        sums[residue] = (
            transformed[residue]
            + transformed[residue + 4]
            + transformed[residue + 8]
            + transformed[residue + 12]
            + transformed[residue + 16]
            + transformed[residue + 20]
        )
    result = Array(24)
    for i in unroll(0, 24):
        result[i] = transformed[i] + sums[i % 4]
    return result


def _external_initial_round_16(state, round_index: Const):
    sboxed = Array(16)
    for i in unroll(0, 16):
        value = state[i] + POSEIDON16_EXTERNAL_INITIAL[round_index * 16 + i]
        sboxed[i] = value * value * value
    return _mds_light_16(sboxed)


def _external_final_round_16(state, round_index: Const):
    sboxed = Array(16)
    for i in unroll(0, 16):
        value = state[i] + POSEIDON16_EXTERNAL_FINAL[round_index * 16 + i]
        sboxed[i] = value * value * value
    return _mds_light_16(sboxed)


def _external_initial_round_24(state, round_index: Const):
    sboxed = Array(24)
    for i in unroll(0, 24):
        value = state[i] + POSEIDON24_EXTERNAL_INITIAL[round_index * 24 + i]
        sboxed[i] = value * value * value
    return _mds_light_24(sboxed)


def _external_final_round_24(state, round_index: Const):
    sboxed = Array(24)
    for i in unroll(0, 24):
        value = state[i] + POSEIDON24_EXTERNAL_FINAL[round_index * 24 + i]
        sboxed[i] = value * value * value
    return _mds_light_24(sboxed)


def poseidon2_permute_16(state_in):
    state: Mut = _mds_light_16(state_in)
    for round_index in unroll(0, 4):
        state = _external_initial_round_16(state, round_index)
    for round_index in unroll(0, 20):
        partial = Array(16)
        value = state[0] + POSEIDON16_INTERNAL[round_index]
        partial[0] = value * value * value
        for i in unroll(1, 16):
            partial[i] = state[i]
        total: Mut = partial[0]
        for i in unroll(1, 16):
            total += partial[i]
        next_state = Array(16)
        for i in unroll(0, 16):
            next_state[i] = total + POSEIDON16_INTERNAL_DIAGONAL[i] * partial[i]
        state = next_state
    for round_index in unroll(0, 4):
        state = _external_final_round_16(state, round_index)
    return state


def poseidon2_permute_24(state_in):
    state: Mut = _mds_light_24(state_in)
    for round_index in unroll(0, 4):
        state = _external_initial_round_24(state, round_index)
    for round_index in unroll(0, 23):
        partial = Array(24)
        value = state[0] + POSEIDON24_INTERNAL[round_index]
        partial[0] = value * value * value
        for i in unroll(1, 24):
            partial[i] = state[i]
        total: Mut = partial[0]
        for i in unroll(1, 24):
            total += partial[i]
        next_state = Array(24)
        for i in unroll(0, 24):
            next_state[i] = total + POSEIDON24_INTERNAL_DIAGONAL[i] * partial[i]
        state = next_state
    for round_index in unroll(0, 4):
        state = _external_final_round_24(state, round_index)
    return state


def poseidon2_digest(state):
    digest = Array(8)
    for i in unroll(0, 8):
        digest[i] = state[i]
    return digest


def poseidon2_leaf_hash(row):
    return poseidon2_leaf_hash_2(row)


def poseidon2_leaf_hash_2(row):
    state = Array(24)
    for i in unroll(0, 2):
        state[i] = row[i]
    for i in unroll(2, 24):
        state[i] = 0
    return poseidon2_digest(poseidon2_permute_24(state))


def poseidon2_leaf_hash_5(row):
    state = Array(24)
    for i in unroll(0, 5):
        state[i] = row[i]
    for i in unroll(5, 24):
        state[i] = 0
    return poseidon2_digest(poseidon2_permute_24(state))


def poseidon2_leaf_hash_10(row):
    state = Array(24)
    for i in unroll(0, 10):
        state[i] = row[i]
    for i in unroll(10, 24):
        state[i] = 0
    return poseidon2_digest(poseidon2_permute_24(state))


def poseidon2_leaf_hash_20(row):
    first = Array(24)
    for i in unroll(0, 16):
        first[i] = row[i]
    for i in unroll(16, 24):
        first[i] = 0
    state: Mut = poseidon2_permute_24(first)
    final = Array(24)
    for i in unroll(0, 4):
        final[i] = row[16 + i]
    for i in unroll(4, 24):
        final[i] = state[i]
    return poseidon2_digest(poseidon2_permute_24(final))


def poseidon2_leaf_hash_40(row):
    first = Array(24)
    for i in unroll(0, 16):
        first[i] = row[i]
    for i in unroll(16, 24):
        first[i] = 0
    state: Mut = poseidon2_permute_24(first)
    second = Array(24)
    for i in unroll(0, 16):
        second[i] = row[16 + i]
    for i in unroll(16, 24):
        second[i] = state[i]
    state = poseidon2_permute_24(second)
    final = Array(24)
    for i in unroll(0, 8):
        final[i] = row[32 + i]
    for i in unroll(8, 24):
        final[i] = state[i]
    return poseidon2_digest(poseidon2_permute_24(final))


def poseidon2_compress(left, right):
    state = Array(16)
    for i in unroll(0, 8):
        state[i] = left[i]
        state[i + 8] = right[i]
    permuted = poseidon2_permute_16(state)
    digest = Array(8)
    for i in unroll(0, 8):
        digest[i] = permuted[i]
    return digest
