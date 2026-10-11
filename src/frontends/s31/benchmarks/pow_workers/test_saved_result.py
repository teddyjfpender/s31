#!/usr/bin/env python3
"""Audit the retained paired native-proof evidence without rerunning proofs."""

import hashlib
import json
from pathlib import Path
import unittest

from fresh_assignments import PROTOCOL_SHA256, summary

HERE = Path(__file__).resolve().parent
SAVED = HERE / "results/fresh-statements-20261011.json"


class SavedFreshAssignmentEvidence(unittest.TestCase):
    def test_complete_native_verified_paired_corpus(self) -> None:
        report = json.loads(SAVED.read_bytes())
        self.assertEqual(report["schema"], "s31-mixed-pow-workers-fresh-statements-v1")
        self.assertEqual(report["protocol"]["sha256"], PROTOCOL_SHA256)
        self.assertEqual(report["script_sha256"], hashlib.sha256(
            (HERE / "fresh_assignments.py").read_bytes()).hexdigest())
        self.assertEqual(report["workers"], [16, 18, 24, 32])
        self.assertEqual(report["rounds"], 2)
        self.assertEqual(report["assignments_per_shape"], 30)
        self.assertEqual(len(report["records"]), 480)
        self.assertEqual(set(report["changed_claim_verifier_diagnostics"].values()),
                         {"error: InvalidMixedInteractionNonce"})
        self.assertTrue(all(row["native_verifier_accepted"] for row in report["records"]))
        for shape in ("control_n2", "control_n6"):
            rows = [row for row in report["records"] if row["shape"] == shape]
            self.assertEqual(len(rows), 240)
            for assignment in range(30):
                paired = [row for row in rows if row["assignment"] == assignment]
                self.assertEqual({row["proof_sha256"] for row in paired},
                                 {paired[0]["proof_sha256"]})
                self.assertEqual({row["proof_bytes"] for row in paired},
                                 {paired[0]["proof_bytes"]})
                self.assertEqual({(row["round"], row["workers"]) for row in paired},
                                 {(round_id, worker) for round_id in range(2)
                                  for worker in (16, 18, 24, 32)})
            self.assertEqual(len({row["proof_sha256"] for row in rows}), 30)
        self.assertEqual(report["summary"], summary(report["records"],
                                                     report["workers"], 30, 2))


if __name__ == "__main__":
    unittest.main()
