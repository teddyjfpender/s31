"""Exact theorem-envelope arithmetic and fail-closed native projection."""

from __future__ import annotations

import copy
import unittest
from fractions import Fraction
from unittest.mock import patch

from scripts.release.pcs_fri_stwo_multidomain import (
    F_ORDER, first_fold_johnson_floor, main, minimum_udr_queries,
    multidomain_from_gate, sqrt_upper,
)
from scripts.tests.test_pcs_fri_gate_error_ledger import reviewed_shape


class StwoMultidomainTests(unittest.TestCase):
    def test_exact_sqrt_upper(self) -> None:
        for value in (Fraction(1, 2), Fraction(1, 4), Fraction(524289, 1048576)):
            upper = sqrt_upper(value)
            self.assertGreaterEqual(upper * upper, value)
            self.assertLess((upper - Fraction(1, 2**32)) ** 2, value)

    def test_first_fold_johnson_envelope_and_udr_options(self) -> None:
        result = multidomain_from_gate(reviewed_shape())
        self.assertFalse(result["proven_release_admissible"])
        self.assertIsNone(result["native_proven_security_bits"])
        self.assertTrue(result["johnson_universal_floor_exceeds_96_bit_target"])
        rows = result["candidate_theorem_arithmetic"]
        self.assertEqual([r["hypothetical_blowup"] for r in rows], [2, 4, 8, 16, 32])
        self.assertEqual([r["udr_minimum_queries_at_excluded_boundary"] for r in rows],
                         [232, 142, 116, 106, 101])
        self.assertTrue(all(r["johnson_first_fold_envelope_exceeds_target"] for r in rows))
        self.assertTrue(all(r["udr_first_fold_bound_meets_target_alone"] for r in rows))
        self.assertTrue(all(r["udr_bcs_first_fold_contribution_exceeds_target"] for r in rows))
        self.assertEqual([r["udr_necessary_max_T_if_R_at_least_1_other_terms_ignored"]
                          for r in rows], [84, 41, 20, 9, 4])
        self.assertEqual([r["native_configured"] for r in rows],
                         [True, False, False, False, False])
        self.assertTrue(all(r["native_supported_or_admissible"] is None for r in rows))
        self.assertEqual(rows[0]["candidate_first_line_code_rate"], "524289/1048576")
        self.assertEqual(rows[0]["johnson_query_lower_floor_for_70_draws"], "1/34359738368")
        self.assertEqual(rows[0]["udr_first_fold_published_bound"],
                         f"{3 * 2**20}/{F_ORDER}")

    def test_strict_query_boundary_and_target_variation(self) -> None:
        self.assertEqual(minimum_udr_queries(2, 96), 232)
        self.assertEqual(minimum_udr_queries(4, 96), 142)
        self.assertGreater(first_fold_johnson_floor(2**20, 2), Fraction(1, 2**96))
        result = multidomain_from_gate(reviewed_shape(), 128)
        self.assertFalse(result["proven_release_admissible"])
        self.assertTrue(result["johnson_universal_floor_exceeds_96_bit_target"])

    def test_rejects_changed_geometry_and_invalid_limits(self) -> None:
        baseline = reviewed_shape()
        changed = copy.deepcopy(baseline)
        changed["fri"]["raw_queries"] = 71
        with self.assertRaises(ValueError):
            multidomain_from_gate(changed)
        for bits, queries in ((0, 1), (257, 1), (96.0, 1), (96, 0), (96, True)):
            with self.assertRaises(ValueError):
                multidomain_from_gate(baseline, bits, queries)
        with self.assertRaises(ValueError):
            first_fold_johnson_floor(2**20, 3)

    def test_require_proven_is_closed(self) -> None:
        with patch("scripts.release.pcs_fri_stwo_multidomain.extract_gate",
                   return_value=reviewed_shape()), patch("sys.stdout"):
            self.assertEqual(main(["/trusted-by-test", "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
