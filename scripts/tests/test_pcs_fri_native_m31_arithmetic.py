"""Source-pin controls for native M31 field arithmetic."""

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_native_m31_arithmetic import (
    SIGNATURES, body, check_source,
)

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "deps/stwo-zig/src/core/fields/m31.zig"


@unittest.skipUnless(SOURCE.is_file(), "engine submodule not checked out")
class NativeM31ArithmeticSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = SOURCE.read_text()

    def test_reviewed_source(self):
        check_source(self.source)

    def test_semantic_mutations_rejected(self):
        mutations = (
            ("canonical constructor", "x < Modulus", "x <= Modulus"),
            ("scalar add", "s >= Modulus", "s > Modulus"),
            ("scalar sub", "a.v + Modulus", "a.v + 0"),
            ("scalar mul", "@as(u64, a.v) * @as(u64, b.v)",
             "@as(u64, a.v) + @as(u64, b.v)"),
            ("u64 reduction", "t >> 31", "t >> 30"),
            ("product reduction", "r >= Modulus", "r > Modulus"),
            ("AArch64 vector mul", "sqdmulh", "sqrdmulh"),
            ("vector add", "@min(sum, sum -% P_VEC)",
             "@max(sum, sum -% P_VEC)"),
            ("vector sub", "@min(d, d +% P_VEC)",
             "@max(d, d +% P_VEC)"),
            ("vector mul dispatch", "return mulVec4Aarch64(a, b);",
             "return addVec4(a, b);"),
            ("vector product reduction", "folded = (x & p64) + (x >>",
             "folded = (x & p64) - (x >>"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name):
                signature = SIGNATURES[name]
                start = self.source.index(signature) + len(signature)
                original = body(self.source, signature)
                self.assertIn(old, original)
                mutated = original.replace(old, new, 1)
                source = (self.source[:start] + mutated +
                          self.source[start + len(original):])
                with self.assertRaises(ValueError):
                    check_source(source)

    def test_modulus_mutation_rejected(self):
        source = self.source.replace("Modulus: u32 = 0x7fffffff",
                                     "Modulus: u32 = 0x7ffffffe", 1)
        with self.assertRaises(ValueError):
            check_source(source)


if __name__ == "__main__":
    unittest.main()
