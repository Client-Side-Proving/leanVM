"""Focused GKR denominator checks without generating an execution proof."""

import unittest

from verifier import EF, Fp, N_VARS_TO_SEND_GKR_COEFFS, ONE, ZERO, verify_gkr_quotient


class ReachedFirstChallenge(Exception):
    pass


class QuotientTranscript:
    def __init__(self, numerators, denominators):
        self.arrays = iter((numerators, denominators))

    def next_extension_scalars_vec(self, length):
        values = next(self.arrays)
        assert len(values) == length
        return values

    def sample_many_ef(self, length):
        raise ReachedFirstChallenge


class GkrQuotientTests(unittest.TestCase):
    def test_zero_denominator_rejected_before_challenges(self):
        count = 1 << N_VARS_TO_SEND_GKR_COEFFS
        for index in range(count):
            for numerator in (ZERO, ONE):
                with self.subTest(index=index, numerator=numerator):
                    numerators, denominators = [ONE] * count, [ONE] * count
                    numerators[index], denominators[index] = numerator, ZERO
                    with self.assertRaisesRegex(AssertionError, "GKR quotient: zero denominator"):
                        verify_gkr_quotient(QuotientTranscript(numerators, denominators), N_VARS_TO_SEND_GKR_COEFFS + 1)

    def test_nonzero_denominators_reach_challenges(self):
        count = 1 << N_VARS_TO_SEND_GKR_COEFFS
        denominators = [EF([Fp(i + j + 2) for j in range(EF.DIMENSION)]) for i in range(count)]
        numerators = [ZERO] + [ONE] * (count - 1)
        with self.assertRaises(ReachedFirstChallenge):
            verify_gkr_quotient(QuotientTranscript(numerators, denominators), N_VARS_TO_SEND_GKR_COEFFS + 1)


if __name__ == "__main__":
    unittest.main()
