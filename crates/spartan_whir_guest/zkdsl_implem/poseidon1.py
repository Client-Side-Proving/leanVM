from snark_lib import *


def poseidon1_permute_16(state):
    output = Array(16)
    poseidon16_permute(state, state + 8, output)
    return output


def poseidon1_leaf_hash_to(row, length: Const, zero_state, output):
    state: Mut = zero_state

    full_blocks = div_floor(length, 8)
    remainder = length % 8
    for block in unroll(0, full_blocks):
        next_state: Imm
        if block + 1 == full_blocks:
            if remainder == 0:
                poseidon16_permute_half(row + block * 8, state + 8, output)
                next_state = output
            else:
                full_state = Array(16)
                poseidon16_permute(row + block * 8, state + 8, full_state)
                next_state = full_state
        else:
            full_state = Array(16)
            poseidon16_permute(row + block * 8, state + 8, full_state)
            next_state = full_state
        state = next_state

    if remainder != 0:
        partial = Array(8)
        for i in unroll(0, remainder):
            partial[i] = row[full_blocks * 8 + i]
        for i in unroll(remainder, 8):
            partial[i] = state[i]
        poseidon16_permute_half(partial, state + 8, output)
        state = output

    return


def poseidon1_leaf_hash(row, length: Const, zero_state):
    output = Array(8)
    poseidon1_leaf_hash_to(row, length, zero_state, output)
    return output


def poseidon1_leaf_hash_2(row, zero_state):
    return poseidon1_leaf_hash(row, 2, zero_state)


def poseidon1_leaf_hash_5(row, zero_state):
    return poseidon1_leaf_hash(row, 5, zero_state)


def poseidon1_leaf_hash_10(row, zero_state):
    return poseidon1_leaf_hash(row, 10, zero_state)


def poseidon1_leaf_hash_10_to(row, zero_state, output):
    poseidon1_leaf_hash_to(row, 10, zero_state, output)
    return


def poseidon1_leaf_hash_20(row, zero_state):
    return poseidon1_leaf_hash(row, 20, zero_state)


def poseidon1_compress(left, right):
    output = Array(8)
    poseidon16_permute_half(left, right, output)
    return output


def poseidon1_compress_to(left, right, output):
    poseidon16_permute_half(left, right, output)
    return
