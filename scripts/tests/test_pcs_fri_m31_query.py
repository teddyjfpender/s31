"""Mutation controls for the native M31 query sampler source contract."""
from itertools import product
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_m31_query import check_sources


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


class M31QuerySourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "queries": (CORE / "queries.zig").read_text(),
            "channel": (CORE / "channel/blake2s.zig").read_text(),
            "hasher": (CORE / "vcs/blake2_hash.zig").read_text(),
            "m31": (CORE / "fields/m31.zig").read_text(),
            "profile": (CORE / "vcs_lifted/channel_profile.zig").read_text(),
            "verifier": (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
            "fri": (CORE / "fri.zig").read_text(),
            "pcs_verifier": (CORE / "pcs/verifier.zig").read_text(),
        }

    def test_pinned_source(self) -> None:
        check_sources(**self.sources)

    def test_exhaustive_small_two_block_reduce_then_mask_schedule(self) -> None:
        # Four 4-bit raw words in two 2-lane blocks, q=7=2^3-1.
        # Check every raw stream, every prefix length and every valid mask.
        q = 7
        for raw in product(range(16), repeat=4):
            for n in range(5):
                for k in range(3):
                    mask = (1 << k) - 1
                    output = []
                    blocks_drawn = 0
                    while len(output) < n:
                        block = raw[2 * blocks_drawn:2 * blocks_drawn + 2]
                        blocks_drawn += 1
                        for word in block:
                            output.append((word % q) & mask)
                            if len(output) == n:
                                break
                    indexed = [(raw[j] % q) & mask for j in range(n)]
                    self.assertEqual(output, indexed)
                    self.assertEqual(blocks_drawn, (n + 1) // 2)

    def test_mutations_are_rejected(self) -> None:
        mutations = (
            ("queries", "word & query_mask", "word % query_mask"),
            ("queries", "channel.drawU32s()", "channel.drawBaseFelts()"),
            ("queries", "while (produced < n_queries) {", "while (produced + 1 < n_queries) {"),
            ("queries", "if (produced == n_queries) break;", "if (produced + 1 == n_queries) break;"),
            ("channel", "pub const FELTS_PER_HASH: usize = 8;", "pub const FELTS_PER_HASH: usize = 4;"),
            ("channel", "Blake2sChannelGeneric(true)", "Blake2sChannelGeneric(false)"),
            ("channel", "out[i] = readU32Le(hash[base .. base + 4]);",
             "out[i] = readU32Le(hash[base .. base + 4]) + 1;"),
            ("channel", "const base = i * 4;", "const base = (7 - i) * 4;"),
            ("hasher", "if (is_m31_output) out = reduceToM31(out);",
             "if (false) out = reduceToM31(out);"),
            ("hasher", "const reduced = @select(u32, folded >= p, folded -% p, folded);",
             "const reduced = folded;"),
            ("hasher", "const folded = (input & p) +% (input >> @as(V4, @splat(31)));",
             "const folded = (input & p) -% (input >> @as(V4, @splat(31)));"),
            ("m31", "pub const Modulus: u32 = 0x7fffffff;",
             "pub const Modulus: u32 = 0x7ffffffe;"),
            ("m31", "return @min(r, r -% Modulus);", "return r;"),
            ("profile", ".m31_channel = true,", ".m31_channel = false,"),
            ("verifier", "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;",
             "const MC = cpu.prove.profiles.Blake2sMerkleChannel;"),
            ("fri", "self.config.n_queries,", "self.config.n_queries - 1,"),
            ("fri", "const retained_raw = try allocator.dupe(usize, raw);",
             "const retained_raw = try allocator.dupe(usize, unique);"),
            ("pcs_verifier", "fri_verifier.sampleQueryPositionsWithRaw(",
             "fri_verifier.sampleQueryPositions("),
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
