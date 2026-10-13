"""Mutation controls for the finite v0.1 raw-query counter epoch audit."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_query_epoch import (
    CONFIG_SOURCES, ENGINE, audit, audit_sources,
)

ROOT = Path(__file__).resolve().parents[2]


def sources() -> tuple[str, str, str, str, str, str, tuple[str, ...]]:
    engine = ROOT / ENGINE
    return (
        (engine / "pcs/verifier.zig").read_text(),
        (engine / "fri.zig").read_text(),
        (engine / "queries.zig").read_text(),
        (engine / "channel/blake2s.zig").read_text(),
        (engine / "pcs/config_v2.zig").read_text(),
        (engine / "protocol_revision.zig").read_text(),
        tuple((ROOT / path).read_text() for path in CONFIG_SOURCES),
    )


class QueryEpochTests(unittest.TestCase):
    def test_pinned_native_epoch_has_nine_distinct_counter_inputs(self) -> None:
        report = audit_sources(*sources())
        self.assertEqual(report["raw_queries"], 70)
        self.assertEqual(report["hash_draws"], 9)
        self.assertEqual(report["counter_inputs"], list(range(9)))
        self.assertFalse(report["counter_wrap_in_this_epoch"])
        self.assertFalse(report["full_transcript_counter_wrap_proven"])
        self.assertFalse(report["random_oracle_independence_proven"])
        bound = audit(ROOT)
        self.assertEqual(bound["hash_draws"], 9)
        self.assertEqual(len(bound["source_sha256"]), 10)
        self.assertTrue(all(len(digest) == 64 for digest in bound["source_sha256"].values()))

    def test_missing_nonce_reset_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        self.assertIn("self.n_draws = 0;", channel)
        changed = channel.replace("self.n_draws = 0;", "self.n_draws = self.n_draws;", 1)
        with self.assertRaisesRegex(ValueError, "counter reset"):
            audit_sources(pcs, fri, queries, changed, config, revision, profiles)

    def test_extra_query_draw_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        anchor = "const words = channel.drawU32s();"
        self.assertIn(anchor, queries)
        changed = queries.replace(anchor, "_ = channel.drawU32s();\n        " + anchor, 1)
        with self.assertRaisesRegex(ValueError, "channel draw or mix"):
            audit_sources(pcs, fri, changed, channel, config, revision, profiles)

    def test_changed_query_count_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        mutated = list(profiles)
        mutated[0] = mutated[0].replace(
            "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)",
            "FriConfigV2.init(26, 0, 1, 71, fri_fold_step)", 1,
        )
        with self.assertRaisesRegex(ValueError, "nominal query count"):
            audit_sources(pcs, fri, queries, channel, config, revision, tuple(mutated))

    def test_changed_fri_query_forwarding_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        self.assertIn("self.config.n_queries,", fri)
        changed = fri.replace("self.config.n_queries,", "70,", 1)
        with self.assertRaisesRegex(ValueError, "configured raw queries"):
            audit_sources(pcs, changed, queries, channel, config, revision, profiles)

    def test_extra_operation_after_nonce_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        anchor = "channel.mixU64(proof.proof_of_work);"
        self.assertIn(anchor, pcs)
        changed = pcs.replace(anchor, anchor + "\n            _ = channel.drawU32s();", 1)
        with self.assertRaisesRegex(ValueError, "unexpected channel operation"):
            audit_sources(changed, fri, queries, channel, config, revision, profiles)

    def test_ignored_pow_nonce_result_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        anchor = "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {"
        self.assertIn(anchor, pcs)
        changed = pcs.replace(anchor, "if (channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {", 1)
        with self.assertRaisesRegex(ValueError, "verified PoW nonce barrier"):
            audit_sources(changed, fri, queries, channel, config, revision, profiles)

    def test_revision_query_bridge_changed_rejected(self) -> None:
        pcs, fri, queries, channel, config, revision, profiles = sources()
        anchor = ".fri_config = fri.folding(),"
        self.assertIn(anchor, revision)
        changed = revision.replace(anchor, ".fri_config = other_config,", 1)
        with self.assertRaisesRegex(ValueError, "protocol revision query bridge"):
            audit_sources(pcs, fri, queries, channel, config, changed, profiles)


if __name__ == "__main__":
    unittest.main()
