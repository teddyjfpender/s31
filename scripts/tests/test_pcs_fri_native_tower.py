"""Mutation controls for the native tower-formula source guard."""

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_native_tower import check_sources


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


@unittest.skipUnless((CORE / "fields/qm31.zig").is_file(),
                     "engine submodule not checked out")
class NativeTowerSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = [
            (CORE / name).read_text()
            for name in ("fields/cm31.zig", "fields/qm31.zig", "circle.zig")
        ]

    def test_pinned_formulas(self):
        check_sources(*self.sources)

    def test_semantic_mutations_rejected(self):
        mutations = (
            (0, ".a = ac.sub(bd),", ".a = ac.add(bd),"),
            (0, ".b = ab.add(ab),", ".b = ab.sub(ab),"),
            (1, ".a = two_a.sub(value.b),", ".a = two_a.add(value.b),"),
            (1, "return self.c0.b.isZero() and self.c1.isZero();",
             "return self.c0.b.isZero() or self.c1.isZero();"),
            (1, ".c0 = a2.add(mulByR(b2)),", ".c0 = a2.sub(mulByR(b2)),"),
            (2, "const lhs = self.x.square().add(self.y.square());",
             "const lhs = self.x.square().sub(self.y.square());"),
        )
        for index, old, new in mutations:
            with self.subTest(index=index, old=old):
                sources = self.sources.copy()
                self.assertIn(old, sources[index])
                sources[index] = sources[index].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(*sources)


if __name__ == "__main__":
    unittest.main()
