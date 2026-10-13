"""Fail-closed controls for the pinned OOD seed geometry diagnostic."""

from __future__ import annotations

import unittest
from fractions import Fraction

from scripts.release.pcs_fri_ood_seed_geometry import (
    ENGINE_GITLINK, Q, ROOT, SOURCE_SHA256, audit, classify,
)


class OodSeedGeometryTests(unittest.TestCase):
    def test_pinned_source_and_exact_counts(self) -> None:
        report = audit()
        self.assertEqual(report["schema"], "s31-pcs-fri-ood-seed-geometry-v1")
        self.assertEqual(report["quadratic_subfield_nonexceptional_seed_count"], Q**2 - 2)
        self.assertEqual(Fraction(report["quadratic_subfield_nonexceptional_fraction_if_uniform"]),
                         Fraction(Q**2 - 2, Q**4))
        self.assertEqual(Fraction(report["base_field_seed_fraction_if_uniform"]),
                         Fraction(1, Q**3))
        self.assertFalse(report["published_ood_distribution_instantiated"])
        self.assertIsNone(report["native_proven_security_bits"])

    def test_source_and_gitlink_mutations_require_new_review(self) -> None:
        sources = {name: (ROOT / name).read_bytes() for name in SOURCE_SHA256}
        with self.assertRaisesRegex(ValueError, "gitlink changed"):
            classify(sources, "0" * 40)
        for name in SOURCE_SHA256:
            changed = dict(sources)
            changed[name] += b"\n"
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "source changed"):
                classify(changed, ENGINE_GITLINK)
        with self.assertRaisesRegex(ValueError, "roster changed"):
            classify({name: data for name, data in sources.items()
                      if name != next(iter(SOURCE_SHA256))}, ENGINE_GITLINK)


if __name__ == "__main__":
    unittest.main()
