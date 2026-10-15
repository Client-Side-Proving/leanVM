"""Check the grinding transition against direct Poseidon permutations."""

import unittest

from verifier import EF, FiatShamir, Fp, POSEIDON16, Proof


class GrindingTests(unittest.TestCase):
    @staticmethod
    def make_state(capacity, transcript):
        state = FiatShamir(Proof(transcript, []), capacity)
        state.duplex()
        return state

    def test_positive_work_refreshes_extension_and_query_samples(self):
        # Fixed capacities exercise distinct accepted transcripts; this compares
        # exact permutations, not statistical evidence of independence.
        for seed in range(8):
            capacity = [Fp(seed * 8 + i + 1) for i in range(8)]
            initial = POSEIDON16.permute(capacity + [Fp(0)] * 8)
            for nonce in range(4096):
                transcript = [Fp(nonce)] + [Fp(0)] * 7
                checked = POSEIDON16.permute(initial[:8] + transcript)
                fresh = POSEIDON16.permute(checked[:8] + [Fp(0)] * 8)
                if checked[8].value & 15 == 0 and fresh[8].value & 15 != 0:
                    break
            else:
                self.fail("deterministic nonce search exhausted")
            with self.subTest(seed=seed, nonce=nonce):
                state = self.make_state(capacity, transcript)
                state.check_pow_grinding(4)
                self.assertEqual(state.state, fresh)
                self.assertEqual(state.offset, 8)
                self.assertNotEqual(state.state[8], checked[8])
                self.assertEqual(state.sample_ef(), EF(fresh[8:13]))
                query_state = self.make_state(capacity, transcript)
                query_state.check_pow_grinding(4)
                self.assertEqual(query_state.sample_in_range(8, 8), [x.value & 255 for x in fresh[8:]])
                self.assertNotEqual(fresh[8].value & 15, 0)

    def test_invalid_nonce_rejects_before_refresh(self):
        capacity = [Fp(i + 1) for i in range(8)]
        initial = POSEIDON16.permute(capacity + [Fp(0)] * 8)
        for nonce in range(256):
            transcript = [Fp(nonce)] + [Fp(0)] * 7
            checked = POSEIDON16.permute(initial[:8] + transcript)
            if checked[8].value & 15 != 0:
                break
        else:
            self.fail("no invalid deterministic nonce")
        state = self.make_state(capacity, transcript)
        with self.assertRaisesRegex(AssertionError, "Invalid Grinding Witness"):
            state.check_pow_grinding(4)
        self.assertEqual(state.state, checked)

    def test_zero_work_preserves_state_and_transcript(self):
        state = self.make_state([Fp(i + 1) for i in range(8)], [])
        initial = state.state[:]
        state.check_pow_grinding(0)
        self.assertEqual(state.state, initial)
        self.assertEqual(state.offset, 0)
        self.assertTrue(state.rate_fresh)
        self.assertEqual(state.sample_ef(), EF(initial[8:13]))


if __name__ == "__main__":
    unittest.main()
