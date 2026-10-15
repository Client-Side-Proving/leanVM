from snark_lib import *
from poseidon2 import *


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
    permuted = poseidon2_permute_16(state)
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


def fs_observe_const(fs, values, length: Const):
    current: Mut = fs
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


def fs_sample_extension(fs):
    current: Mut = fs
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
