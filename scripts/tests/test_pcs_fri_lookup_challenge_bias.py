"""Exact finite-count and source-drift checks for the conditional P07 pair."""

from fractions import Fraction
from pathlib import Path
import unittest

from scripts.release.pcs_fri_lookup_challenge_bias import (
    ENGINE_GITLINK, MAX_LOOKUP_NUMERATOR, P, ROOT, SOURCE_SHA256,
    WORD_SPACE, audit, classify,
)


class LookupChallengeBiasTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {name: (ROOT / name).read_bytes() for name in SOURCE_SHA256}

    def test_pinned_native_sources_and_fail_closed_report(self) -> None:
        report = audit(ROOT)
        self.assertEqual("conditional_fixed_prefix_counting_only", report["status"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertFalse(report["proven_release_admissible"])
        self.assertFalse(report["p07_discharged"])
        self.assertFalse(report["p09_discharged"])

    def test_exact_ratio_and_existing_lookup_budget(self) -> None:
        report = classify(self.sources, ENGINE_GITLINK)
        self.assertEqual(WORD_SPACE, 2 * P + 2)
        self.assertEqual(WORD_SPACE, 3 + 3 + 2 * (P - 2))
        max_ratio = Fraction((3 * P) ** 8, WORD_SPACE ** 8)
        uniform = Fraction(MAX_LOOKUP_NUMERATOR, P**4)
        biased = max_ratio * uniform
        self.assertEqual(str(max_ratio), report["max_density_ratio_over_uniform_QM31_squared"])
        self.assertEqual(str(uniform), report["mixed_n1_n8_conditional_uniform_lookup_bound"])
        self.assertEqual(str(biased), report["mixed_n1_n8_conditional_biased_lookup_bound"])
        self.assertGreater(biased, uniform)
        self.assertLess(biased, Fraction(1, 2**97))
        self.assertGreater(biased, Fraction(1, 2**98))

    def test_singleton_all_zero_attains_ratio(self) -> None:
        raw_all_zero = Fraction(3**8, WORD_SPACE**8)
        uniform_singleton = Fraction(1, P**8)
        reported = Fraction(classify(self.sources, ENGINE_GITLINK)[
            "max_density_ratio_over_uniform_QM31_squared"])
        self.assertEqual(reported, raw_all_zero / uniform_singleton)

    def test_source_or_gitlink_drift_refused(self) -> None:
        with self.assertRaisesRegex(ValueError, "gitlink"):
            classify(self.sources, "0" * 40)
        path = "deps/stwo-zig/src/core/channel/blake2s.zig"
        changed = dict(self.sources)
        changed[path] += b"\n// unintended draw change\n"
        with self.assertRaisesRegex(ValueError, "source changed"):
            classify(changed, ENGINE_GITLINK)
        changed = dict(self.sources)
        changed.pop(path)
        with self.assertRaisesRegex(ValueError, "roster changed"):
            classify(changed, ENGINE_GITLINK)


if __name__ == "__main__":
    unittest.main()
