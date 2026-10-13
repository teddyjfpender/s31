"""Exact arithmetic and fail-closed controls for the published-bound preflight."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

from scripts.release.pcs_fri_proven_preflight import (
    Candidate, alpha_squared, assess, ideal_m31_masked_query_upper,
    masked_m31_max_set_bias, minimum_ideal_m31_masked_queries,
    minimum_queries, query_meets, remark26_leading_interval, sqrt_upper,
)


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/release/pcs_fri_proven_preflight.py"


class ProvenPreflightTests(unittest.TestCase):
    def setUp(self) -> None:
        self.current = Candidate(512, 2, 70, 3, 1)

    def test_exact_current_query_threshold_and_no_native_claim(self) -> None:
        report = assess(self.current)
        self.assertEqual(report["minimum_ungrinded_queries_for_target"], 348)
        self.assertFalse(report["ungrinded_query_term_meets_target"])
        self.assertFalse(report["proven_release_admissible"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertFalse(query_meets(self.current, 96, 347))
        self.assertTrue(query_meets(self.current, 96, 348))

    def test_blowup_and_multiplicity_change_threshold(self) -> None:
        four = replace(self.current, blowup=4)
        large_m = replace(self.current, multiplicity=256)
        self.assertLess(minimum_queries(four), minimum_queries(self.current))
        self.assertLess(minimum_queries(large_m), minimum_queries(self.current))
        self.assertFalse(assess(replace(four, raw_queries=512))["proven_release_admissible"])

    def test_native_m31_masked_query_bias_and_outward_interval(self) -> None:
        # Exact toy-field enumeration tests the same Mersenne reduction and
        # power-of-two mask, with every raw word visited rather than sampled.
        bits = 3
        modulus = (1 << bits) - 1
        for k in range(bits + 1):
            size = 1 << k
            counts = [0] * size
            for word in range(1 << (bits + 1)):
                counts[(word % modulus) & (size - 1)] += 1
            uniform = (1 << (bits + 1)) // size
            positive_excess = sum(max(0, count - uniform) for count in counts)
            self.assertEqual(masked_m31_max_set_bias(k) * (1 << 32),
                             positive_excess)
        a2 = alpha_squared(self.current)
        upper = sqrt_upper(a2)
        self.assertGreaterEqual(upper * upper, a2)
        self.assertLess((upper - Fraction(1, 1 << 192)) ** 2, a2)
        adjusted = ideal_m31_masked_query_upper(self.current)
        self.assertEqual(adjusted, upper + Fraction(1, 1 << 31))
        self.assertGreaterEqual(minimum_ideal_m31_masked_queries(self.current),
                                minimum_queries(self.current))
        self.assertIsNone(assess(self.current)["native_proven_security_bits"])

    def test_remark26_outward_interval_and_target(self) -> None:
        lower, upper = remark26_leading_interval(self.current)
        self.assertLess(lower, upper)
        self.assertGreater(lower, Fraction(1, 1 << 96))
        square = replace(self.current, blowup=4)
        lower, upper = remark26_leading_interval(square)
        self.assertEqual(lower, upper)

    def test_theorem_preconditions_and_unproved_fold_schedule(self) -> None:
        for change in (
            {"trace_rows": 513}, {"blowup": 3}, {"multiplicity": 2},
            {"multiplicity": 257}, {"fold_step": 4},
            {"trace_rows": 1 << 29, "blowup": 2},
        ):
            with self.subTest(change=change), self.assertRaises(ValueError):
                assess(replace(self.current, **change))

    def test_require_proven_exits_nonzero_even_if_query_term_is_small(self) -> None:
        result = subprocess.run(
            [sys.executable, "-B", str(SCRIPT), "--raw-queries", "512",
             "--require-proven"], capture_output=True, text=True, cwd=ROOT,
        )
        self.assertEqual(result.returncode, 2)
        report = json.loads(result.stdout)
        self.assertTrue(report["ungrinded_query_term_meets_target"])
        self.assertFalse(report["proven_release_admissible"])


if __name__ == "__main__":
    unittest.main()
