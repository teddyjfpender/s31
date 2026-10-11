"""Offline integrity and independent arithmetic check of the local holdout."""

from __future__ import annotations

import hashlib
import json
import statistics
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def read(name: str) -> tuple[dict, str]:
    data = (HERE / name).read_bytes()
    return json.loads(data), hashlib.sha256(data).hexdigest()


def value(trial: dict, metric: str) -> float:
    wall = trial["prove_seconds"] + trial["verify_seconds"]
    pow_total = (trial["prover_stages"]["fri_pow_seconds"] +
                 trial["prover_stages"]["interaction_pow_seconds"])
    return {"paired_wall_seconds": wall,
            "paired_after_pow_seconds": wall - pow_total,
            "pow_seconds": pow_total,
            "proof_bytes": trial["proof_bytes"],
            "prover_peak_rss_bytes": trial["prover_peak_rss_bytes"]}[metric]


class SavedProspectiveAudit(unittest.TestCase):
    def test_sealed_roster_and_heldout_arithmetic(self) -> None:
        plan, plan_sha = read("prospective-plan-2026-10-11.json")
        calibration, calibration_sha = read("prospective-calibration-2026-10-11.json")
        score, score_sha = read("prospective-heldout-2026-10-11.json")
        train_report, train_report_sha = read("prospective-train-report-2026-10-11.json")
        heldout_report, heldout_report_sha = read("prospective-heldout-report-2026-10-11.json")
        trials, _ = read("prospective-trials-2026-10-11.json")
        self.assertEqual(plan["train"], [1, 4, 16])
        self.assertEqual(plan["heldout"], [2, 8, 12])
        self.assertEqual(plan["samples_per_program"], 12)
        self.assertEqual(calibration["plan_sha256"], plan_sha)
        self.assertEqual(score["plan_sha256"], plan_sha)
        self.assertEqual(score["calibration_sha256_before_heldout"], calibration_sha)
        self.assertEqual(calibration["train_report_sha256"], train_report_sha)
        self.assertEqual(score["heldout_report_sha256"], heldout_report_sha)
        self.assertEqual(trials["plan_sha256"], plan_sha)
        self.assertEqual(trials["calibration_sha256"], calibration_sha)
        self.assertEqual(trials["score_sha256"], score_sha)
        self.assertEqual(trials["split_reports_sha256"], {
            "train": train_report_sha, "heldout": heldout_report_sha})
        self.assertEqual(set(trials["splits"]), {"train", "heldout"})
        self.assertEqual(set(plan["sources"]),
                         {str(gates) for gates in (*plan["train"], *plan["heldout"])})
        all_assignments = set()
        for split, report, gates_set in (("train", train_report, plan["train"]),
                                         ("heldout", heldout_report, plan["heldout"])):
            self.assertEqual(set(trials["splits"][split]),
                             {str(gates) for gates in gates_set})
            self.assertEqual(set(report["cases"]),
                             {str(gates) for gates in gates_set})
            for gates in gates_set:
                key = str(gates)
                case = trials["splits"][split][key]
                summary = report["cases"][key]
                self.assertEqual(case["source_sha256"], plan["sources"][key]["source_sha256"])
                self.assertEqual(case["source_sha256"], summary["source_sha256"])
                self.assertEqual(case["compiler_sha256"], plan["compiler_sha256"])
                self.assertEqual(case["compiler_sha256"], summary["compiler_sha256"])
                self.assertFalse(summary["package_reused"])
                self.assertEqual(summary["cost_report"]["padded"]["qm31_ops"], 512)
                self.assertEqual(summary["cost_report"]["preprocessed_cells"], 4096)
                self.assertEqual(len(case["trials"]), 12)
                for sample, item in enumerate(case["trials"]):
                    self.assertEqual(item["assignment_sha256"],
                                     plan["sources"][key]["assignment_sha256"][sample])
                    self.assertNotIn(item["assignment_sha256"], all_assignments)
                    all_assignments.add(item["assignment_sha256"])
                    self.assertEqual(item["trial_report_sha256"],
                                     summary["trial_report_sha256"][sample])
                    self.assertEqual(item["proof_sha256"], summary["proof_sha256"][sample])
                    self.assertIs(item["native_verifier_accepted"], True)
                    self.assertTrue(item["changed_public_statement_rejected"])
                    self.assertEqual(item["independent_value_oracle"]["status"], "passed")
        self.assertEqual(len(all_assignments), 72)
        self.assertEqual(calibration["status"], "sealed-before-heldout-measurement")
        self.assertEqual(score["status"], "local-heldout-diagnostic")
        for metric, prediction in calibration["predictions"].items():
            program_medians = {}
            for gates in plan["train"]:
                program_medians[str(gates)] = statistics.median(
                    value(item, metric) for item in trials["splits"]["train"][str(gates)]["trials"])
            self.assertEqual(prediction["training_program_medians"], program_medians)
            self.assertEqual(prediction["center"], statistics.median(program_medians.values()))
            for gates in plan["heldout"]:
                measured = statistics.median(value(item, metric) for item in
                                             trials["splits"]["heldout"][str(gates)]["trials"])
                scored = score["cases"][str(gates)][metric]
                self.assertEqual(scored["observed"]["median"], measured)
                self.assertEqual(scored["predicted_center"], prediction["center"])
                self.assertAlmostEqual(scored["relative_median_error"],
                                       abs(measured - prediction["center"]) / measured)
        self.assertEqual(score["diagnostic_gates"], {
            metric: all(score["cases"][str(gates)][metric]["relative_median_error"] <= limit
                        for gates in plan["heldout"])
            for metric, limit in plan["diagnostic_relative_median_error_limits"].items()})
        self.assertTrue(score["all_diagnostic_gates_pass"])


if __name__ == "__main__":
    unittest.main()
