"""Mutation controls for the opt-in raw Gate query source route."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_raw_query import check_sources


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


class RawGateQuerySourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "queries": (CORE / "queries.zig").read_text(),
            "channel": (CORE / "channel/blake2s.zig").read_text(),
            "hasher": (CORE / "vcs/blake2_hash.zig").read_text(),
            "profile": (CORE / "vcs_lifted/channel_profile.zig").read_text(),
            "verifier": (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
            "runtime": (ROOT / "src/frontends/s31/runtime/mvp_runtime.zig").read_text(),
            "fri": (CORE / "fri.zig").read_text(),
            "pcs_verifier": (CORE / "pcs/verifier.zig").read_text(),
        }

    def test_selected_sources(self) -> None:
        check_sources(**self.sources)

    def test_each_index_has_same_number_of_raw_preimages(self) -> None:
        for width in range(1, 9):
            for k in range(width + 1):
                counts = [0] * (1 << k)
                for word in range(1 << width):
                    counts[word & ((1 << k) - 1)] += 1
                self.assertEqual(counts, [1 << (width - k)] * (1 << k))

    def test_route_mutations_are_rejected(self) -> None:
        mutations = (
            ("queries", "word & query_mask", "word % query_mask"),
            ("queries", "channel.drawU32s()", "channel.drawBaseFelts()"),
            ("channel", "Blake2sHasherGeneric(is_m31_output)", "Blake2sHasherGeneric(true)"),
            ("channel", "out[i] = readU32Le(hash[base .. base + 4]);",
             "out[i] = readU32Le(hash[base .. base + 4]) + 1;"),
            ("hasher", "if (is_m31_output) out = reduceToM31(out);",
             "out = reduceToM31(out);"),
            ("profile", ".m31_channel = false,", ".m31_channel = true,"),
            ("verifier", "const RawMC = cpu.prove.profiles.Blake2sMerkleChannel;",
             "const RawMC = cpu.prove.profiles.Blake2sM31MerkleChannel;"),
            ("runtime", "(if (raw_gate_channel) cpu.Root else cpu.Internal).prove(",
             "cpu.Internal.prove("),
            ("runtime", "try native.verifyRawGate(", "try native.verify("),
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
