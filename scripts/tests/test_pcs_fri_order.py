"""Mutation controls for the pinned PCS/FRI transcript source contract."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import check_sources

ROOT = Path(__file__).resolve().parents[2]
ENGINE = ROOT / "deps/stwo-zig/src/core"


def sources() -> tuple[str, str, str, str, str]:
    return tuple((ENGINE / path).read_text() for path in (
        "pcs/verifier.zig", "fri.zig", "queries.zig",
        "channel/blake2s.zig", "vcs_lifted/blake2_merkle.zig",
    ))


class PcsFriOrderTest(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check_sources(*sources())

    def test_deep_challenge_before_sample_absorption_rejected(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "channel.mixFelts(sampled_values_flat);\n            const deep_randomness = channel.drawSecureFelt();"
        after = "const deep_randomness = channel.drawSecureFelt();\n            channel.mixFelts(sampled_values_flat);"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS DEEP"):
            check_sources(pcs.replace(before, after, 1), fri, queries, channel, merkle)

    def test_fri_alpha_before_root_rejected(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "MC.mixRoot(channel, proof_in.first_layer.commitment);"
        after = "const premature_alpha = channel.drawSecureFelt();\n            " + before
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI commitment"):
            check_sources(pcs, fri.replace(before, after, 1), queries, channel, merkle)

    def test_fri_capture_accepts_only_sampled_raw_queries(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "if (!std.mem.eql(usize, positions, sampled))"
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI capture query custody"):
            check_sources(pcs, fri.replace(before, "if (false)", 1),
                          queries, channel, merkle)

    def test_fri_sampled_raw_retention_required(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "self.sampled_raw_queries = retained_raw;"
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI raw query ownership"):
            check_sources(pcs, fri.replace(before, "// raw draw forgotten", 1),
                          queries, channel, merkle)

    def test_missing_query_counter_encoding_rejected(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "@memcpy(hash_input[32..36], counter[0..]);"
        self.assertIn(before, channel)
        with self.assertRaisesRegex(ValueError, "Blake2s query"):
            check_sources(pcs, fri, queries, channel.replace(before, "// omitted", 1), merkle)

    def test_missing_exported_root_binding_rejected(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "if (!std.meta.eql(tree.root, commitment))"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS DEEP"):
            check_sources(pcs.replace(before, "if (false)", 1), fri, queries, channel, merkle)

    def test_extra_zero_fold_round_guard_removed_rejected(self) -> None:
        pcs, fri, queries, channel, merkle = sources()
        before = "proof_in.inner_layers.len != config_mod.nFoldSteps("
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI commitment"):
            check_sources(pcs, fri.replace(before, "false and (", 1), queries, channel, merkle)


if __name__ == "__main__":
    unittest.main()
