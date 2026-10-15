import math
import unittest

import security_accounting as accounting
import client_security_accounting as client


class SecurityAccountingTests(unittest.TestCase):
    def test_native_config_reference_queries(self):
        # These sequences were independently produced by WhirConfig::new.
        profiles = accounting.candidate_profiles("no-grinding-113-115")
        _, direct, _, final = accounting.whir_events("direct", profiles["direct"], 29, "poseidon")
        self.assertEqual([p["queries"] for p in direct], [343, 268, 81, 48, 34, 27])
        self.assertEqual(final, 8)
        _, lift, _, final = accounting.whir_events("lift", profiles["lift"], 23, "poseidon")
        self.assertEqual([p["queries"] for p in lift], [134, 125, 61, 40, 31])
        self.assertEqual(final, 6)

    def test_query_bias_uses_maximum_point_mass(self):
        for b in (0, 1, 13, 24):
            size = 1 << b
            expected = math.ceil(accounting.MODULUS / size) * size / accounting.MODULUS
            self.assertEqual(accounting.query_density(b, "poseidon"), expected)
            self.assertEqual(accounting.query_density(b, "keccak"), 1)
        self.assertGreater(accounting.query_density(24, "poseidon"), 1)

    def test_stronger_theorem_and_exact_field_never_increase_bits(self):
        for n, r, m in [(29, 1, 4), (23, 6, 3), (7, 9, 4)]:
            strong = accounting.proximity_bits(n, r, m)
            ordinary = accounting.proximity_bits(n, r, m, list_agreement=False)
            rounded = accounting.proximity_bits(n, r, m, field_bits=155)
            self.assertLess(strong, ordinary)
            self.assertAlmostEqual(rounded - strong, 155 - accounting.FIELD_BITS)

    def test_composition_counts_and_no_guarantee(self):
        result = accounting.account(accounting.candidate_profiles("no-grinding-113-115"),
                                    29, 23, 116, (22, 21, 21))
        self.assertEqual(result["proof_counts"], dict(client=2, direct=2, lift=2, node=1))
        self.assertEqual(sum(e["count"] for e in result["events"] if e["layer"] == "bytecode"), 4)
        self.assertLess(result["composed_interactive_accounting_bits"],
                        result["backend_interactive_accounting_bits"])
        self.assertFalse(result["whole_chain_guarantee_established"])
        self.assertIsNone(result["classical_work_bits"])
        self.assertGreater(result["composed_interactive_accounting_bits"], 102.9)
        self.assertLess(result["composed_interactive_accounting_bits"], 103)

    def test_unsupported_recursive_shapes_reject(self):
        for profile in [accounting.Profile(114, 0, 1, 6, 2, 6, 5),
                        accounting.Profile(114, 0, 1, 6, 3, 6, 11)]:
            with self.assertRaises(ValueError):
                accounting.whir_events("invalid", profile, 29, "poseidon")
        with self.assertRaises(ValueError):
            accounting.account(accounting.candidate_profiles("no-grinding-113-115"),
                               29, 23, 116, (23, 21, 21))

    def test_mixed_lift_and_root_dimensions(self):
        profiles = accounting.candidate_profiles("no-grinding-113-111-115")
        result = accounting.account(profiles, 29, 24, 104.64685051238511, (22, 21, 21),
                                    root_variables=23)
        lift, root = result["layers"]["lift"], result["layers"]["node"]
        self.assertEqual((lift["stack_variables"], root["stack_variables"]), (24, 23))
        self.assertEqual([p["queries"] for p in lift["phases"]], [63, 59, 39, 29, 24])
        self.assertEqual([p["queries"] for p in root["phases"]], [134, 125, 61, 40, 31])
        self.assertEqual((lift["final_coefficients"], root["final_coefficients"]), (128, 64))
        self.assertAlmostEqual(result["composed_interactive_accounting_bits"], 101.41430242, places=7)
        # Root capacity applies independently of the larger lifted proof.
        with self.assertRaisesRegex(ValueError, "terminal polynomial capacity"):
            accounting.account(profiles, 29, 24, 116, (23, 22, 22), root_variables=23)

    def test_fixed_program_zero_padding_uses_actual_root_geometry(self):
        profiles = accounting.candidate_profiles("no-grinding-113-111-115")
        expected = {24: ([139, 125, 61, 41, 31], 128, 101.41446490288334),
                    25: ([148, 127, 62, 41, 31], 256, 101.41796465062417)}
        for dimension, (queries, coefficients, composed_bits) in expected.items():
            result = accounting.account(profiles, 29, 24, 104.64685051238511, (22, 21, 21),
                                        root_variables=dimension)
            root = result["layers"]["node"]
            self.assertEqual(root["stack_variables"], dimension)
            self.assertEqual([p["queries"] for p in root["phases"]], queries)
            self.assertEqual(root["final_coefficients"], coefficients)
            self.assertAlmostEqual(result["composed_interactive_accounting_bits"], composed_bits)
            reductions = [e for e in result["events"] if e["layer"] == "bytecode"]
            self.assertEqual(sum(e["count"] for e in reductions), 4)
        with self.assertRaisesRegex(ValueError, "program dimensions"):
            accounting.account(profiles, 29, 24, 116, (22, 21, 20), root_variables=24)

    def test_report_infers_each_proofs_own_dimension(self):
        data = dict(profiles={"node_child_num_variables": 24}, layers=[
            dict(layer="direct_left", stacked_num_variables=29),
            dict(layer="direct_right", stacked_num_variables=29),
            dict(layer="lift_left", stacked_num_variables=24),
            dict(layer="lift_right", stacked_num_variables=24),
            dict(layer="binary_root_c1", stacked_num_variables=23),
        ])
        self.assertEqual(accounting.report_dimensions(data, None, None, None), (29, 24, 23))
        with self.assertRaisesRegex(ValueError, "supplied root dimension differs"):
            accounting.report_dimensions(data, None, None, 24)
        data["layers"].pop()
        with self.assertRaisesRegex(ValueError, "no root proof dimension"):
            accounting.report_dimensions(data, None, None, None)
        self.assertEqual(accounting.report_dimensions(data, None, None, 23), (29, 24, 23))
        data["layers"][3]["stacked_num_variables"] = 23
        with self.assertRaisesRegex(ValueError, "lift proof dimensions differ"):
            accounting.report_dimensions(data, None, None, 23)

    def test_distinct_queries_use_hypergeometric_probability(self):
        # The rounded agreement set has seven of sixteen positions here.
        expected = math.comb(7, 3) / math.comb(16, 3)
        actual = client.query_error(16, 2, 3, 3)
        self.assertAlmostEqual(actual, expected, places=12)
        self.assertLess(actual, (7 / 16)**3)
        self.assertEqual(client.query_error(16, 2, 16, 3), 0)

    def test_hiding_randomness_changes_actual_code_rate(self):
        # Exported first hiding code: 16 interleaved columns, 8192 positions,
        # each column containing 4096 message and 268 random coefficients.
        config = dict(folding_factor=4, domain_size=131072, num_variables=12,
                      num_queries=268, query_positions=268)
        hidden = client.phase_shape(config, 268)
        plain = client.phase_shape(config)
        self.assertEqual(hidden["dimension"], 4364)
        self.assertEqual(hidden["length"], 8192)
        self.assertGreater(hidden["query_error"], plain["query_error"])
        self.assertEqual(hidden["m"], 15)

    def test_interleaved_mca_charges_every_coordinate(self):
        scalar = accounting.rs_mca_bits(2048, 636, 33)
        interleaved = accounting.rs_mca_bits(2048, 636, 33, 8)
        self.assertAlmostEqual(scalar - interleaved, 3)

    def test_plain_client_rejects_unversioned_continuation(self):
        with self.assertRaisesRegex(ValueError, "continuation version"):
            client.plain_events("old", {"domain_separator": [17104896, 22]})


if __name__ == "__main__":
    unittest.main()
