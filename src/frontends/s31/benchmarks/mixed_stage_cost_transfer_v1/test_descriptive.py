"""Mutation checks for the independent, descriptive compact-corpus replay."""

from __future__ import annotations

import json
import unittest

from descriptive import CORPUS_DIR, LANGUAGE, analyze, canonical, digest


class DescriptiveReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.raw = [path.read_bytes() for path in (
            LANGUAGE / "mixed-stage-cost-transfer-v1-protocol.json",
            CORPUS_DIR / "phase-root.json", CORPUS_DIR / "corpus.json",
            CORPUS_DIR / "audit.json",
            LANGUAGE / "mixed-stage-cost-transfer-v1-unscored-evidence-anchor.json")]

    def test_complete_saved_corpus_and_deterministic_result(self) -> None:
        result = analyze(*self.raw)
        self.assertEqual(result["verified_trials"], 360)
        self.assertEqual(len(result["programs"]), 12)
        self.assertEqual(result["status"], "descriptive_only_frozen_model_unavailable")
        self.assertFalse(result["prediction_error_reported"])
        self.assertEqual(canonical(result), canonical(analyze(*self.raw)))
        self.assertEqual(canonical(result),
                         (LANGUAGE / "mixed-stage-cost-transfer-v1-descriptive-replay.json").read_bytes())

    def test_changed_corpus_rejected_before_analysis(self) -> None:
        raw = self.raw.copy()
        changed = json.loads(raw[2])
        changed["records"][0]["trials"][0]["proof_bytes"] += 1
        raw[2] = canonical(changed)
        with self.assertRaisesRegex(ValueError, "audit or corpus digest mismatch"):
            analyze(*raw)

    def test_changed_timing_rejected_even_when_compact_hashes_are_updated(self) -> None:
        raw = self.raw.copy()
        changed = json.loads(raw[2])
        changed["records"][0]["trials"][0]["prover_internal_stages_ns"]["package_total_ns"] += 1
        raw[2] = canonical(changed)
        audit = json.loads(raw[3]); audit["corpus_sha256"] = digest(raw[2]); raw[3] = canonical(audit)
        seal = json.loads(raw[4]); seal["corpus_sha256"] = digest(raw[2]); seal["audit_sha256"] = digest(raw[3]); raw[4] = canonical(seal)
        with self.assertRaisesRegex(ValueError, "package stage partition changed"):
            analyze(*raw)

    def test_changed_statement_rejected_even_when_compact_hashes_are_updated(self) -> None:
        raw = self.raw.copy()
        changed = json.loads(raw[2])
        changed["records"][0]["trials"][0]["typed_statement_sha256"] = "0" * 64
        raw[2] = canonical(changed)
        audit = json.loads(raw[3]); audit["corpus_sha256"] = digest(raw[2]); raw[3] = canonical(audit)
        seal = json.loads(raw[4]); seal["corpus_sha256"] = digest(raw[2]); seal["audit_sha256"] = digest(raw[3]); raw[4] = canonical(seal)
        with self.assertRaisesRegex(ValueError, "trial identity changed"):
            analyze(*raw)


if __name__ == "__main__":
    unittest.main()
