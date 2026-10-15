from snark_lib import *
from poseidon1 import *
from transcript_poseidon1 import *


PRIMITIVE_WORDS = 91


def main():
    words = Array(PRIMITIVE_WORDS)
    hint_witness("primitive_words", words)
    zero_state = Array(16)
    for i in unroll(0, 16):
        zero_state[i] = 0

    fs: Mut = fs_new()
    for i in unroll(0, 23):
        fs = fs_observe_one(fs, words[i])
    for i in unroll(0, 12):
        fs, sample = fs_sample_base(fs)
        assert sample == words[23 + i]

    leaf = poseidon1_leaf_hash(words + 35, 24, zero_state)
    for i in unroll(0, 8):
        assert leaf[i] == words[59 + i]

    node = poseidon1_compress(words + 67, words + 75)
    for i in unroll(0, 8):
        assert node[i] == words[83 + i]
    return
