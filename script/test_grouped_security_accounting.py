import itertools
import json
import math
from pathlib import Path
import tempfile
import unittest

import grouped_security_accounting as accounting
import security_accounting as legacy


class GroupedSecurityArithmetic(unittest.TestCase):
    def test_query_bound_matches_exhaustive_agreement_sets(self):
        for p, domain in [(17, 4), (17, 8), (97, 8)]:
            for work in range(7):
                for queries in [1, 2, 3]:
                    for size in range(1, domain + 1):
                        maximum = 0
                        for subset in itertools.combinations(range(domain), size):
                            good = set(subset)
                            passing = sum(x % (1 << work) == 0 for x in range(p)) / p
                            ordinary = sum(x % domain in good for x in range(p)) / p
                            maximum = max(maximum, passing * ordinary**queries)
                        self.assertAlmostEqual(
                            maximum, accounting.query_joint_bound(p, domain, size, queries, work),
                            places=14)

    def test_reused_coordinate_does_not_amplify_root_zero(self):
        # Zero is the unique root of r in every extension field. The work check
        # always accepts its first coordinate, so its joint mass stays 1/p^2.
        p = 17
        samples = list(itertools.product(range(p), repeat=2))
        for work in range(1, 6):
            passing = [r for r in samples if r[0] % (1 << work) == 0]
            joint = sum(r == (0, 0) for r in passing) / len(samples)
            self.assertEqual(joint, 1 / p**2)
            self.assertGreater(joint, len(passing) / len(samples) / p**2)

    def test_separate_work_word_amplifies_root_zero(self):
        p = 17
        for work in range(1, 5):
            joint = sum(x % (1 << work) == 0 and y == z == 0
                        for x, y, z in itertools.product(range(p), repeat=3)) / p**3
            passing = ((p - 1) // (1 << work) + 1) / p
            self.assertAlmostEqual(joint, passing / p**2)

    def test_poseidon_queries_keep_full_support_after_grinding(self):
        row = accounting.query_event(20, 39, 24, 14, 4, "poseidon")
        self.assertEqual(row["first_query_support"], 1 << 20)
        self.assertAlmostEqual(row["query_joint_error"],
                               row["pow_pass_probability"] * row["ordinary_agreement_mass"]**39)

    def test_poseidon_folding_uses_exact_independent_work_probability(self):
        profile = legacy.Profile(100, 22, 1, 6, 4, 2, 5)
        _, phases, _, final = legacy.whir_events("direct", profile, 29, "poseidon")
        schedule = accounting.native_schedule(profile, phases, final)
        row = accounting.phase_events(phases[0], schedule, 0, 23, "poseidon")
        plain = accounting.mca_error(1 << phases[0]["query_domain_bits"],
                                     1 << (29 - 6), 23, 1 << 6)
        passing = ((accounting.P - 1) // (1 << 8) + 1) / accounting.P
        self.assertAlmostEqual(row["folding_mca_joint_error"] / plain, passing)

    def test_native_schedule_matches_rust_capture(self):
        # Independently captured from WhirConfig::new on 2026-10-15.
        cases = [
            (legacy.Profile(100, 22, 1, 6, 4, 2, 5), 29,
             [159, 32, 20, 15, 12, 10], [22, 22, 22, 21, 19, 18], [8, 0, 0, 0, 0, 3]),
            (legacy.Profile(100, 24, 4, 5, 4, 1, 3), 23,
             [39, 20, 14, 11, 9], [24, 24, 24, 24, 24], [0, 0, 3, 5, 12]),
            (legacy.Profile(100, 28, 6, 5, 4, 1, 6), 23,
             [25, 15, 12, 10], [28, 28, 25, 23], [0, 0, 0, 4]),
        ]
        for profile, n, queries, query_pows, folding_pows in cases:
            _, phases, _, final = legacy.whir_events("test", profile, n, "poseidon")
            schedule = accounting.native_schedule(profile, phases, final)
            self.assertEqual(schedule["queries"], queries)
            self.assertEqual(schedule["query_pows"], query_pows)
            self.assertEqual(schedule["folding_pows"], folding_pows)

    def test_three_polynomial_residual_has_at_most_two_roots(self):
        # Once the diagonal/cross claims are fixed, a false original claim
        # makes one residual a nonzero polynomial in lambda of degree <=2.
        p = 7
        for coefficients in itertools.product(range(p), repeat=3):
            if not any(coefficients):
                continue
            roots = sum(sum(a * r**i for i, a in enumerate(coefficients)) % p == 0
                        for r in range(p))
            self.assertLessEqual(roots, 2)

    def test_grouped_lifting_charges_degree_and_independent_work(self):
        result = accounting.grouped_events(5)
        scalar_interleaved = accounting.mca_error(1 << 24, 1 << 18, 5, 32)
        self.assertEqual(result["curve_lifting_interactive_error"], 2 * scalar_interleaved)
        self.assertEqual(result["curve_lifting_joint_error"], scalar_interleaved / 8)
        self.assertEqual(result["list_bound"], 320)
        self.assertGreater(result["transition_upper_bound"], result["curve_lifting_joint_error"])

    def test_same_transition_errors_are_added(self):
        result = accounting.layer_account("lift", legacy.Profile(100, 24, 4, 5, 4, 1, 3), 23)
        for row in result["optimized_radius"]["phases"]:
            self.assertEqual(row["folding_transition_error"],
                             row["folding_mca_joint_error"] + row["folding_sumcheck_joint_error"])
            self.assertEqual(row["shift_transition_error"],
                             row["query_joint_error"] + row["continuation_combination_error"])
            self.assertAlmostEqual(row["transition_bits"], -math.log2(max(
                row["folding_transition_error"], row["shift_transition_error"], row["ood_error"])))

    def test_invalid_query_geometry_is_rejected(self):
        for args in [(17, 3, 1, 1, 0), (19, 8, 1, 1, 0), (17, 8, 0, 1, 0),
                     (17, 8, 9, 1, 0), (17, 8, 1, 0, 0), (17, 8, 1, 1, -1)]:
            with self.assertRaises(ValueError):
                accounting.query_joint_bound(*args)

    def test_report_cannot_substitute_duplicate_children_or_program_geometry(self):
        def fixture():
            return dict(complete=True, node_arity=2,
                        profiles=dict(terminal_grouped_logup=True, terminal_keccak=True),
                        layers=[dict(layer=name, stacked_num_variables=n,
                                     bytecode_padded_instructions=1 << program_log)
                                for name, n, program_log in [
                                    ("direct_left", 29, 18), ("direct_right", 29, 18),
                                    ("lift_left", 23, 17), ("lift_right", 23, 17),
                                    ("binary_root_grouped_logup", 23, 17)]])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "report.json"
            bad_labels = fixture()
            bad_labels["layers"][1]["layer"] = "direct_left"
            bad_program = fixture()
            bad_program["layers"][0]["bytecode_padded_instructions"] = 1 << 19
            for report in [bad_labels, bad_program]:
                path.write_text(json.dumps(report))
                with self.assertRaises(ValueError):
                    accounting.account(path, [])


if __name__ == "__main__":
    unittest.main()
