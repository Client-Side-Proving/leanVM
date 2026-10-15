import unittest

from verifier import EF, Fp, ONE, ZERO, SparseStatements, combine_whir_constraints, ef_powers


class WhirBatchingTests(unittest.TestCase):
    def test_continuation_residual_cannot_cancel_first_fresh_claim(self):
        values = [EF(19), EF(23), EF(31)]
        constraints = [SparseStatements(1, [ZERO], [(0, value)]) for value in values]
        carry, error = EF(11), EF(7)
        altered = [SparseStatements(1, [ZERO], [(0, value)]) for value in [values[0] - error, *values[1:]]]
        for gamma in (ZERO, ONE, EF(2), EF([Fp(i + 2) for i in range(5)])):
            with self.subTest(gamma=gamma):
                true_sum, coefficients = combine_whir_constraints(carry, constraints, gamma, True)
                false_sum, false_coefficients = combine_whir_constraints(carry + error, altered, gamma, True)
                self.assertEqual(coefficients, ef_powers(gamma, len(values) + 1)[1:])
                self.assertEqual(coefficients, false_coefficients)
                self.assertEqual(false_sum - true_sum, error * (ONE - gamma))
                self.assertEqual(false_sum == true_sum, gamma == ONE)

                # Initial batching still starts at one; reusing it with a carry loses the residual.
                old_true, initial_coefficients = combine_whir_constraints(carry, constraints, gamma, False)
                old_false, _ = combine_whir_constraints(carry + error, altered, gamma, False)
                self.assertEqual(initial_coefficients, ef_powers(gamma, len(values)))
                self.assertEqual(old_true, old_false)


if __name__ == "__main__":
    unittest.main()
