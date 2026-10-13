"""Fail-closed controls for the P09/P07 gate theorem-interface ledger."""

import copy
import unittest
from unittest.mock import patch

from scripts.release.pcs_fri_gate_error_ledger import ledger_from_gate, main
from scripts.release.pcs_fri_gate_final_domain import derive_gate
from scripts.tests.test_pcs_fri_gate_final_domain import NAMES, gate_report


def reviewed_shape():
    logs = (20, 19, 18, 18, 18, 18, 18, 18, 18, 18, 18)
    return derive_gate(gate_report(logs), [(name, 1) for name in NAMES])


class GateErrorLedgerTests(unittest.TestCase):
    def test_conditional_inputs_never_become_security_bits(self):
        report = ledger_from_gate(reviewed_shape())
        observations = report["source_bound_observations"]
        self.assertEqual(observations["fri_input_domain_rows"], 1 << 21)
        self.assertEqual(observations["raw_query_draws"], 70)
        self.assertEqual(report["conditional_circle_query_comparison"]
                         ["candidate_rho_if_N_equals_max_trace_rows"], "1048577/2097152")
        self.assertEqual(report["conditional_circle_query_comparison"]
                         ["ideal_m31_masked_max_positive_set_bias"], "1/2147483648")
        self.assertIsNone(report["theorem_parameter_mapping"]["circle_N_degree_parameter"])
        self.assertIsNone(report["theorem_parameter_mapping"]["circle_D_standard_position_coset"])
        self.assertIsNone(report["noninteractive_rom_bcs"]["T_adversary_hash_query_budget"])
        self.assertIsNone(report["noninteractive_rom_bcs"]["R_transformation_round_count"])
        self.assertIsNone(report["noninteractive_rom_bcs"]["lambda_theorem_oracle_output_bits"])
        self.assertIsNone(report["noninteractive_rom_bcs"]["native_merkle_binding_failure_bound"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertIsNone(report["whole_proof_error_bound"])
        self.assertFalse(report["proven_release_admissible"])

    def test_reject_unreviewed_profile_and_unsupported_gate_size(self):
        baseline = reviewed_shape()
        changes = (
            ("fold", lambda row: row["fri"].__setitem__("fold_step", 4)),
            ("query", lambda row: row["fri"].__setitem__("raw_queries", 69)),
            ("key", lambda row: row["package_checks"].__setitem__("native_check_key", "rejected")),
            ("domain", lambda row: row["gate_final_domain"].__setitem__("fri_input_domain_rows", 1 << 20)),
            ("theorem_input", lambda row: row["theorem_inputs"].__setitem__("D_final_fri_domain", 1 << 20)),
            ("unclosed", lambda row: row.__setitem__("proven_release_admissible", True)),
            ("lowering", lambda row: row.__setitem__("lowering", "chip")),
        )
        for name, alter in changes:
            with self.subTest(name=name):
                row = copy.deepcopy(baseline)
                alter(row)
                with self.assertRaises(ValueError):
                    ledger_from_gate(row)
        small = derive_gate(gate_report((4, 7, 5, 4, 7, 4, 5, 4, 4, 4, 4)),
                            [(name, 1) for name in NAMES])
        with self.assertRaisesRegex(ValueError, r"2\^20/2\^21"):
            ledger_from_gate(small)

    def test_cli_proven_admission_remains_closed(self):
        with patch("scripts.release.pcs_fri_gate_error_ledger.extract_gate",
                   return_value=reviewed_shape()), patch("sys.stdout"):
            self.assertEqual(main(["/trusted-only-by-test", "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
