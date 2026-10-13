"""Exact Johnson-regime necessity and fail-closed gate-package controls."""

from __future__ import annotations

import copy
import unittest
from fractions import Fraction
from unittest.mock import patch

from scripts.release.pcs_fri_gate_conservative_feasibility import (
    feasibility_from_gate, main, minimum_johnson_draws,
)
from scripts.tests.test_pcs_fri_gate_error_ledger import reviewed_shape
from scripts.release.pcs_fri_proven_preflight import Candidate, remark26_leading_interval


class ConservativeFeasibilityTests(unittest.TestCase):
    def test_sealed_gate_96_bit_necessary_bounds(self) -> None:
        result = feasibility_from_gate(reviewed_shape())
        self.assertEqual(result["status"], "published_proven_johnson_envelope_fails_target")
        self.assertEqual(result["source_bound_gate"]["conditional_fri_input_rows"], 1 << 21)
        self.assertEqual(result["source_bound_gate"]["raw_query_draws"], 70)
        johnson = result["stwo_proven_johnson_query_necessity"]
        self.assertEqual(johnson["without_grinding_query_exponent_strictly_below"], "35/1")
        self.assertEqual(johnson["even_if_full_pow_were_query_credit_exponent_strictly_below"], "61/1")
        self.assertEqual(johnson["minimum_draws_at_johnson_limit_without_grinding"], 193)
        self.assertEqual(johnson["minimum_draws_at_johnson_limit_with_full_hypothetical_query_credit"], 141)
        self.assertTrue(johnson["current_draws_cannot_meet_target_even_with_full_hypothetical_query_credit"])
        circle = result["circle_single_domain_candidate"]
        self.assertEqual(circle["candidate_rate"], "1048577/2097152")
        self.assertEqual(circle["m3_minimum_ungrinded_draws"], 346)
        self.assertEqual(circle["largest_m_minimum_ungrinded_draws"], 193)
        self.assertEqual(circle["largest_m_minimum_ideal_masked_draws_if_independent_raw_words"], 193)
        self.assertEqual(circle["m3_minimum_draws_with_full_hypothetical_query_credit"], 253)
        self.assertEqual(circle["largest_m_minimum_draws_with_full_hypothetical_query_credit"], 141)
        self.assertEqual(circle["m3_candidate_query_term_integer_bits"], 19)
        self.assertEqual(circle["largest_m_candidate_query_term_integer_bits"], 34)
        self.assertTrue(circle["favorable_remark26_leading_upper_envelope_alone_exceeds_target"])
        self.assertTrue(circle["every_such_remark26_upper_envelope_exceeds_target"])
        self.assertEqual(circle["remark26_leading_envelope_lower_floor_for_all_B_ge_2_m_ge_3_L_ge_1"],
                         circle["favorable_remark26_leading_upper_envelope_L1_m3_lower_endpoint"])
        self.assertIsNone(result["native_proven_security_bits"])
        self.assertFalse(result["proven_release_admissible"])

    def test_strict_johnson_boundary_and_query_only_design_space(self) -> None:
        self.assertEqual(minimum_johnson_draws(1, 96), 193)
        self.assertEqual(minimum_johnson_draws(1, 96, 26), 141)
        self.assertEqual(minimum_johnson_draws(2, 96, 26), 71)
        self.assertEqual(minimum_johnson_draws(3, 96), 65)
        self.assertEqual(minimum_johnson_draws(1, 26, 26), 1)
        result = feasibility_from_gate(reviewed_shape())
        self.assertEqual([row["hypothetical_blowup"] for row in
                          result["hypothetical_query_only_design_space"]], [2, 4, 8, 16, 32])
        self.assertTrue(all(row["native_supported_or_admissible"] is None for row in
                            result["hypothetical_query_only_design_space"]))
        smaller = feasibility_from_gate(reviewed_shape(), 60)
        self.assertEqual(smaller["status"], "query_necessity_not_excluded_but_native_mapping_open")
        self.assertFalse(smaller["proven_release_admissible"])

    def test_universal_remark26_floor_crosses_96_bits_at_256_rows(self) -> None:
        target = Fraction(1, 1 << 96)
        for rows, expected in ((128, False), (256, True), (512, True), (1 << 20, True)):
            floor, _ = remark26_leading_interval(Candidate(rows, 2, 70, 3, 1))
            self.assertEqual(floor > target, expected)

    def test_bad_geometry_or_target_rejected(self) -> None:
        baseline = reviewed_shape()
        for change in (
            lambda row: row["fri"].__setitem__("raw_queries", 71),
            lambda row: row["fri"].__setitem__("fold_step", 4),
            lambda row: row["gate_final_domain"].__setitem__("fri_input_domain_rows", 1 << 20),
            lambda row: row["package_checks"].__setitem__("native_check_key", "rejected"),
        ):
            row = copy.deepcopy(baseline)
            change(row)
            with self.assertRaises(ValueError):
                feasibility_from_gate(row)
        for target in (0, 513, 96.0, True):
            with self.assertRaises(ValueError):
                feasibility_from_gate(baseline, target)

    def test_cli_requires_proven_even_if_query_necessity_is_not_excluded(self) -> None:
        with patch("scripts.release.pcs_fri_gate_conservative_feasibility.extract_gate",
                   return_value=reviewed_shape()), patch("sys.stdout"):
            self.assertEqual(main(["/trusted-by-test", "--target-bits", "60", "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
