"""Mutation controls for the native M31 query sampler source contract."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_m31_query import check_sources


CORE = Path(__file__).resolve().parents[2] / "deps/stwo-zig/src/core"


class M31QuerySourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "queries": (CORE / "queries.zig").read_text(),
            "channel": (CORE / "channel/blake2s.zig").read_text(),
            "hasher": (CORE / "vcs/blake2_hash.zig").read_text(),
            "m31": (CORE / "fields/m31.zig").read_text(),
        }

    def test_pinned_source(self) -> None:
        check_sources(**self.sources)

    def test_mutations_are_rejected(self) -> None:
        mutations = (
            ("queries", "word & query_mask", "word % query_mask"),
            ("queries", "channel.drawU32s()", "channel.drawBaseFelts()"),
            ("channel", "Blake2sChannelGeneric(true)", "Blake2sChannelGeneric(false)"),
            ("channel", "out[i] = readU32Le(hash[base .. base + 4]);",
             "out[i] = readU32Le(hash[base .. base + 4]) + 1;"),
            ("hasher", "if (is_m31_output) out = reduceToM31(out);",
             "if (false) out = reduceToM31(out);"),
            ("hasher", "const reduced = @select(u32, folded >= p, folded -% p, folded);",
             "const reduced = folded;"),
            ("m31", "pub const Modulus: u32 = 0x7fffffff;",
             "pub const Modulus: u32 = 0x7ffffffe;"),
            ("m31", "return @min(r, r -% Modulus);", "return r;"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                sources = dict(self.sources)
                self.assertIn(old, sources[name])
                sources[name] = sources[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(**sources)


if __name__ == "__main__":
    unittest.main()
