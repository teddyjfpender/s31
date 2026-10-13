"""Hostile source edits for successful PCS/FRI challenge capture custody."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_challenge_custody import check_sources

ROOT = Path(__file__).resolve().parents[2]
ENGINE = ROOT / "deps/stwo-zig/src/core"


def sources() -> tuple[str, str]:
    return ((ENGINE / "pcs/verifier.zig").read_text(), (ENGINE / "fri.zig").read_text())


class ChallengeCustodyTest(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check_sources(*sources())

    def test_deep_capture_substitution_rejected(self) -> None:
        pcs, fri = sources()
        before = ".deep_randomness = deep_randomness,"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS DEEP custody"):
            check_sources(pcs.replace(before, ".deep_randomness = QM31.zero(),", 1), fri)

    def test_deep_quotient_substitution_rejected(self) -> None:
        pcs, fri = sources()
        before = "                deep_randomness,\n                query_positions,"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS DEEP custody"):
            check_sources(pcs.replace(before, "                QM31.zero(),\n                query_positions,", 1), fri)

    def test_pow_check_bypass_rejected(self) -> None:
        pcs, fri = sources()
        before = "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS verified nonce custody"):
            check_sources(pcs.replace(before, "if (false) {", 1), fri)

    def test_pow_mix_or_capture_substitution_rejected(self) -> None:
        pcs, fri = sources()
        before = "channel.mixU64(proof.proof_of_work);"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS verified nonce custody"):
            check_sources(pcs.replace(before, "channel.mixU64(0);", 1), fri)
        before = ".proof_of_work = proof.proof_of_work,"
        self.assertIn(before, pcs)
        with self.assertRaisesRegex(ValueError, "PCS verified nonce custody"):
            check_sources(pcs.replace(before, ".proof_of_work = 0,", 1), fri)

    def test_fri_capture_alpha_substitution_rejected(self) -> None:
        pcs, fri = sources()
        before = "self.proof.commitment,\n                    self.folding_alpha,"
        self.assertEqual(2, fri.count(before))
        with self.assertRaisesRegex(ValueError, "FRI first captured alpha"):
            check_sources(pcs, fri.replace(before,
                                           "self.proof.commitment,\n                    QM31.zero(),", 1))
        prefix, suffix = fri.rsplit(before, 1)
        with self.assertRaisesRegex(ValueError, "FRI inner captured alpha"):
            check_sources(pcs, prefix + "self.proof.commitment,\n                    QM31.zero()," + suffix)

    def test_fri_fold_alpha_substitution_rejected(self) -> None:
        pcs, fri = sources()
        before = "self.folding_alpha,\n                self.domain,"
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI inner alpha fold"):
            check_sources(pcs, fri.replace(before, "QM31.zero(),\n                self.domain,", 1))

    def test_fri_terminal_bypass_rejected(self) -> None:
        pcs, fri = sources()
        before = "try self.decommitLastLayer(allocator, layer_queries, layer_query_evals);"
        self.assertIn(before, fri)
        with self.assertRaisesRegex(ValueError, "FRI first alpha use"):
            check_sources(pcs, fri.replace(before, "// skipped terminal check", 1))


if __name__ == "__main__":
    unittest.main()
