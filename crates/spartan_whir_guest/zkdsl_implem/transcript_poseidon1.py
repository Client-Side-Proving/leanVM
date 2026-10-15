from snark_lib import *
from poseidon1 import *


OPT_TRANSCRIPT_BLOCKS = OPT_TRANSCRIPT_BLOCKS_VALUE
FS_STATE = 0
FS_PENDING = 16
FS_PENDING_LEN = 24
FS_OUTPUT_COUNT = 25
FS_SIZE = 26


def fs_new():
    fs = Array(FS_SIZE)
    for i in unroll(0, 24):
        fs[i] = 0
    fs[FS_PENDING_LEN] = 0
    fs[FS_OUTPUT_COUNT] = 0
    return fs


def fs_clone(fs):
    result = Array(FS_SIZE)
    for i in unroll(0, FS_SIZE):
        result[i] = fs[i]
    return result


def _fs_duplex(fs):
    state = Array(16)
    pending_len = fs[FS_PENDING_LEN]
    if pending_len != 0:
        for i in range(0, pending_len):
            state[i] = fs[FS_PENDING + i]
        for i in range(pending_len, 8):
            state[i] = 0
    else:
        for i in unroll(0, 8):
            state[i] = fs[FS_STATE + i]
    state[8] = fs[FS_STATE + 8] + pending_len
    for i in unroll(9, 16):
        state[i] = fs[FS_STATE + i]
    permuted = poseidon1_permute_16(state)
    result = Array(FS_SIZE)
    for i in unroll(0, 16):
        result[FS_STATE + i] = permuted[i]
    for i in unroll(0, 8):
        result[FS_PENDING + i] = 0
    result[FS_PENDING_LEN] = 0
    result[FS_OUTPUT_COUNT] = 8
    return result


def fs_observe_one(fs, value):
    pending_len = fs[FS_PENDING_LEN]
    result: Imm
    if pending_len == 7:
        with_value = Array(FS_SIZE)
        for i in unroll(0, 16):
            with_value[FS_STATE + i] = fs[FS_STATE + i]
        for i in unroll(0, 7):
            with_value[FS_PENDING + i] = fs[FS_PENDING + i]
        with_value[FS_PENDING + 7] = value
        with_value[FS_PENDING_LEN] = 8
        with_value[FS_OUTPUT_COUNT] = 0
        result = _fs_duplex(with_value)
    else:
        result = Array(FS_SIZE)
        for i in unroll(0, 16):
            result[FS_STATE + i] = fs[FS_STATE + i]
        for i in range(0, pending_len):
            result[FS_PENDING + i] = fs[FS_PENDING + i]
        result[FS_PENDING + pending_len] = value
        for i in range(pending_len + 1, 8):
            result[FS_PENDING + i] = 0
        result[FS_PENDING_LEN] = pending_len + 1
        result[FS_OUTPUT_COUNT] = 0
    return result


def fs_observe_short_unflushed(fs, values, length: Const):
    pending_len = fs[FS_PENDING_LEN]
    result = Array(FS_SIZE)
    for i in unroll(0, 16):
        result[FS_STATE + i] = fs[FS_STATE + i]
    for i in range(0, pending_len):
        result[FS_PENDING + i] = fs[FS_PENDING + i]
    for i in unroll(0, length):
        result[FS_PENDING + pending_len + i] = values[i]
    for i in range(pending_len + length, 8):
        result[FS_PENDING + i] = 0
    result[FS_PENDING_LEN] = pending_len + length
    result[FS_OUTPUT_COUNT] = 0
    return result


def fs_observe_full_blocks(fs, values, length: Const, extra_block):
    pending_len = fs[FS_PENDING_LEN]
    first_count = 8 - pending_len
    first_input = Array(16)
    for i in range(0, pending_len):
        first_input[i] = fs[FS_PENDING + i]
    for i in range(0, first_count):
        first_input[pending_len + i] = values[i]
    first_input[8] = fs[FS_STATE + 8] + 8
    for i in unroll(9, 16):
        first_input[i] = fs[FS_STATE + i]
    states = Array(div_floor(length, 8) + 1)
    states[0] = poseidon1_permute_16(first_input)
    additional_blocks = div_floor(length, 8) - 1 + extra_block
    for block in range(0, additional_blocks):
        previous = states[block]
        block_input = Array(16)
        for i in unroll(0, 8):
            block_input[i] = values[first_count + block * 8 + i]
        block_input[8] = previous[8] + 8
        for i in unroll(9, 16):
            block_input[i] = previous[i]
        states[block + 1] = poseidon1_permute_16(block_input)
    last = states[additional_blocks]
    consumed = first_count + additional_blocks * 8
    remaining = length - consumed
    result = Array(FS_SIZE)
    for i in unroll(0, 16):
        result[FS_STATE + i] = last[i]
    for i in range(0, remaining):
        result[FS_PENDING + i] = values[consumed + i]
    for i in range(remaining, 8):
        result[FS_PENDING + i] = 0
    result[FS_PENDING_LEN] = remaining
    if remaining == 0:
        result[FS_OUTPUT_COUNT] = 8
    else:
        result[FS_OUTPUT_COUNT] = 0
    return result


def fs_observe_const_blocks(fs, values, length: Const):
    result: Imm
    if length == 0:
        result = fs
    else:
        extra_terms = Array(length % 8)
        for pending in unroll(8 - length % 8, 8):
            if fs[FS_PENDING_LEN] == pending:
                extra_terms[pending - (8 - length % 8)] = 1
            else:
                extra_terms[pending - (8 - length % 8)] = 0
        extra_block: Mut = 0
        for i in unroll(0, length % 8):
            extra_block = extra_block + extra_terms[i]
        if length < 8:
            if extra_block == 0:
                result = fs_observe_short_unflushed(fs, values, length)
            else:
                result = fs_observe_full_blocks(fs, values, length, extra_block)
        else:
            result = fs_observe_full_blocks(fs, values, length, extra_block)
    return result


def fs_observe_const(fs, values, length: Const):
    current: Mut = fs
    if OPT_TRANSCRIPT_BLOCKS == 1:
        current = fs_observe_const_blocks(fs, values, length)
    else:
        for i in unroll(0, length):
            current = fs_observe_one(current, values[i])
    return current


@inline
def fs_observe_extension(fs, value):
    return fs_observe_const(fs, value, 5)


def fs_sample_base(fs):
    current: Imm
    if fs[FS_PENDING_LEN] != 0:
        current = _fs_duplex(fs)
    else:
        if fs[FS_OUTPUT_COUNT] == 0:
            current = _fs_duplex(fs)
        else:
            current = fs
    output_count = current[FS_OUTPUT_COUNT]
    value = current[FS_STATE + output_count - 1]
    result = Array(FS_SIZE)
    for i in unroll(0, 24):
        result[i] = current[i]
    result[FS_PENDING_LEN] = 0
    result[FS_OUTPUT_COUNT] = output_count - 1
    return result, value


def fs_sample_extension_block(fs):
    current: Imm
    if fs[FS_PENDING_LEN] != 0:
        current = _fs_duplex(fs)
    else:
        if fs[FS_OUTPUT_COUNT] == 0:
            current = _fs_duplex(fs)
        else:
            current = fs
    available = current[FS_OUTPUT_COUNT]
    value = Array(5)
    result = Array(FS_SIZE)
    # current has one through eight output words and no pending observations.
    if (available - 1) * (available - 2) * (available - 3) * (available - 4) == 0:
        for i in range(0, available):
            value[i] = current[FS_STATE + available - 1 - i]
        permuted = _fs_duplex(current)
        for i in range(available, 5):
            value[i] = permuted[FS_STATE + 7 + available - i]
        for i in unroll(0, 24):
            result[i] = permuted[i]
        result[FS_PENDING_LEN] = 0
        result[FS_OUTPUT_COUNT] = available + 3
    else:
        for i in unroll(0, 5):
            value[i] = current[FS_STATE + available - 1 - i]
        for i in unroll(0, 24):
            result[i] = current[i]
        result[FS_PENDING_LEN] = 0
        result[FS_OUTPUT_COUNT] = available - 5
    return result, value


def fs_sample_extension(fs):
    current: Mut = fs
    value: Imm
    if OPT_TRANSCRIPT_BLOCKS == 1:
        current, value = fs_sample_extension_block(current)
    else:
        value = Array(5)
        for i in unroll(0, 5):
            current, value[i] = fs_sample_base(current)
    return current, value


def fs_finalize(fs):
    current = _fs_duplex(fs)
    digest = Array(8)
    for i in unroll(0, 8):
        digest[i] = current[FS_STATE + i]
    return digest
