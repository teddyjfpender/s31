"""Git-only arithmetic check of the published compact cost evidence.

This cannot replay proofs: raw proof bytes remain in ignored local evidence.
"""

from __future__ import annotations

import hashlib
import json
import statistics
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAVED = HERE / "results-2026-10-11"


def read(name: str) -> dict:
    return json.loads((SAVED / name).read_bytes())


def sha(name: str) -> str:
    return hashlib.sha256((SAVED / name).read_bytes()).hexdigest()


def metric(row: dict, name: str) -> float:
    if name == "paired_after_pow_seconds":
        return (row["paired_wall_seconds"] -
                (row["fri_pow_seconds"] + row["interaction_pow_seconds"]))
    return row[name]


class SavedGeometryTransferTests(unittest.TestCase):
    def test_compact_ledger_reproduces_frozen_score(self) -> None:
        plan, calibration, score, audit, ledger = (
            read(name) for name in ("plan.json", "calibration.json",
                                    "heldout-score.json", "audit.json",
                                    "compact-trials.json"))
        self.assertEqual(calibration["plan_sha256"], sha("plan.json"))
        self.assertEqual(calibration["train_report_sha256"], sha("train-report.json"))
        self.assertEqual(score["calibration_sha256_before_heldout"], sha("calibration.json"))
        self.assertEqual(score["heldout_report_sha256"], sha("heldout-report.json"))
        self.assertEqual(audit["heldout_score_sha256"], sha("heldout-score.json"))
        self.assertEqual(ledger["native_replay_audit_sha256"], sha("audit.json"))
        self.assertEqual((audit["replayed_accepted_proofs"],
                          audit["replayed_rejected_changed_claims"]), (72, 72))
        rows = ledger["trials"]
        self.assertEqual(len(rows), 72)
        self.assertEqual(len({(r["phase"], r["gates"], r["sample"]) for r in rows}), 72)
        for row in rows:
            self.assertEqual(row["assignment_sha256"], plan["sources"][str(row["gates"])][
                "assignment_sha256"][row["sample"]])
            self.assertEqual(row["padded_qm31_rows"], plan["sources"][str(row["gates"])][
                "expected_padded_qm31_rows"])
            self.assertTrue(row["native_verifier_accepted"])
            self.assertTrue(row["changed_public_statement_rejected"])
            self.assertEqual(row["independent_value_oracle_status"], "passed")
        for size in ("512", "1024"):
            for name, model in calibration["model"][size].items():
                counts = (32, 192) if size == "512" else (384,)
                source_medians = {str(count): statistics.median(
                    metric(row, name) for row in rows if row["gates"] == count)
                    for count in counts}
                self.assertEqual(model["training_program_medians"], source_medians)
                self.assertAlmostEqual(model["center"],
                                       statistics.median(source_medians.values()))
        for count in (96, 256, 448):
            size = str(plan["sources"][str(count)]["expected_padded_qm31_rows"])
            for name, measured in score["cases"][str(count)]["metrics"].items():
                observed = statistics.median(metric(row, name) for row in rows
                                             if row["gates"] == count)
                center = calibration["model"][size][name]["center"]
                self.assertAlmostEqual(measured["observed"]["median"], observed)
                self.assertAlmostEqual(measured["predicted_center"], center)
                self.assertAlmostEqual(measured["relative_median_error"],
                                       abs(center - observed) / observed)
                self.assertEqual(score["diagnostic_gates"][name], all(
                    score["cases"][str(g)]["metrics"][name]["relative_median_error"] <=
                    plan["diagnostic_relative_median_error_limits"][name]
                    for g in (96, 256, 448)))


if __name__ == "__main__":
    unittest.main()
