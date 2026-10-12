"""Git-only arithmetic check of the published operation-mix compact ledger."""

from __future__ import annotations

import hashlib
import json
import statistics
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SAVED = HERE / "results-2026-10-11"
PRIOR = HERE.parent / "geometry_transfer_v1" / "results-2026-10-11"


def read(path: Path) -> dict:
    return json.loads(path.read_bytes())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def value(row: dict, name: str) -> float:
    if name == "paired_after_pow_seconds":
        return row["paired_wall_seconds"] - (row["fri_pow_seconds"] +
                                              row["interaction_pow_seconds"])
    return row[name]


class SavedOperationMixTests(unittest.TestCase):
    def test_compact_ledger_reproduces_frozen_transfer_score(self) -> None:
        plan = read(SAVED / "plan.json")
        report = read(SAVED / "heldout-report.json")
        score = read(SAVED / "heldout-score.json")
        audit = read(SAVED / "audit.json")
        ledger = read(SAVED / "compact-trials.json")
        calibration = read(PRIOR / "calibration.json")
        self.assertEqual(plan["prior_calibration_sha256"], sha(PRIOR / "calibration.json"))
        self.assertEqual(report["plan_sha256"], sha(SAVED / "plan.json"))
        self.assertEqual(score["heldout_report_sha256"], sha(SAVED / "heldout-report.json"))
        self.assertEqual(audit["heldout_score_sha256"], sha(SAVED / "heldout-score.json"))
        self.assertEqual(ledger["native_replay_audit_sha256"], sha(SAVED / "audit.json"))
        self.assertEqual((audit["replayed_accepted_proofs"],
                          audit["replayed_rejected_changed_claims"]), (72, 72))
        rows = ledger["trials"]
        self.assertEqual(len(rows), 72)
        self.assertEqual(len({(r["operation"], r["gates"], r["sample"]) for r in rows}), 72)
        for row in rows:
            label = f"{row['operation']}-{row['gates']}"
            self.assertEqual(row["assignment_sha256"],
                             plan["sources"][label]["assignment_sha256"][row["sample"]])
            self.assertEqual(row["padded_qm31_rows"],
                             plan["sources"][label]["expected_padded_qm31_rows"])
            self.assertTrue(row["native_verifier_accepted"])
            self.assertTrue(row["changed_public_statement_rejected"])
            self.assertEqual(row["independent_value_oracle_status"], "passed")
        for op in ("add", "mul"):
            for gates in (96, 256, 448):
                label = f"{op}-{gates}"
                size = str(plan["sources"][label]["expected_padded_qm31_rows"])
                for name, saved in score["cases"][label]["metrics"].items():
                    observed = statistics.median(value(row, name) for row in rows
                                                 if (row["operation"], row["gates"]) ==
                                                    (op, gates))
                    predicted = calibration["model"][size][name]["center"]
                    error = abs(predicted - observed) / observed
                    self.assertAlmostEqual(saved["observed"]["median"], observed)
                    self.assertAlmostEqual(saved["predicted_center"], predicted)
                    self.assertAlmostEqual(saved["relative_median_error"], error)
                    self.assertEqual(score["diagnostic_gates"][name], all(
                        score["cases"][f"{operation}-{count}"]["metrics"][name][
                            "relative_median_error"] <=
                        plan["diagnostic_relative_median_error_limits"][name]
                        for operation in ("add", "mul") for count in (96, 256, 448)))


if __name__ == "__main__":
    unittest.main()
