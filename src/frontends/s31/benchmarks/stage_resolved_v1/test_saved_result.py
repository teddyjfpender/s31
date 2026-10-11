#!/usr/bin/env python3
"""Check the committed compact result without local Zig packages or proofs."""

from __future__ import annotations

import hashlib
import json
import math
import unittest
from pathlib import Path

from posthoc_calibration_audit import replay

HERE = Path(__file__).resolve().parent
SAVED = HERE / "results-2026-10-11"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class SavedResult(unittest.TestCase):
    def test_36_trial_evidence_and_accounting(self) -> None:
        plan = json.loads((SAVED / "plan.json").read_bytes())
        report = json.loads((SAVED / "heldout-report.json").read_bytes())
        score = json.loads((SAVED / "heldout-score.json").read_bytes())
        audit = json.loads((SAVED / "audit.json").read_bytes())
        ledger = json.loads((SAVED / "compact-trials.json").read_bytes())
        self.assertEqual(score["plan_sha256"], sha(SAVED / "plan.json"))
        self.assertEqual(report["plan_sha256"], sha(SAVED / "plan.json"))
        self.assertEqual(score["heldout_report_sha256"], sha(SAVED / "heldout-report.json"))
        self.assertEqual(audit["heldout_score_sha256"], sha(SAVED / "heldout-score.json"))
        self.assertEqual(ledger["native_replay_audit_sha256"], sha(SAVED / "audit.json"))
        self.assertEqual((audit["replayed_accepted_proofs"],
                          audit["replayed_rejected_changed_claims"]), (36, 36))
        self.assertEqual(len(ledger["trials"]), 36)
        self.assertTrue(score["evaluation"]["all_diagnostic_gates_pass"])
        coverage = {target: 0 for target in ("wall", "after", "proof", "rss")}
        target_name = {"wall": "first_verified_wall_seconds",
                       "after": "after_reported_pow_seconds",
                       "proof": "proof_bytes", "rss": "prover_peak_rss_bytes"}
        grouped = {count: [] for count in (96, 256, 448)}
        for row in ledger["trials"]:
            count, sample = row["gates"], row["sample"]
            grouped[count].append(sample)
            self.assertEqual(row["assignment_sha256"],
                             plan["sources"][str(count)]["assignment_sha256"][sample])
            self.assertEqual(row["trial_report_sha256"],
                             report["cases"][str(count)]["trial_report_sha256"][sample])
            self.assertEqual(row["proof_sha256"],
                             report["cases"][str(count)]["proof_sha256"][sample])
            self.assertTrue(row["native_verifier_accepted"])
            self.assertTrue(row["changed_public_statement_rejected"])
            self.assertEqual(row["independent_value_oracle_status"], "passed")
            self.assertTrue(math.isclose(row["paired_wall_seconds"],
                row["prover_process_seconds"] + row["verifier_process_seconds"],
                abs_tol=1e-9))
            stages = sum(row[key] for key in (
                "witness_seconds", "setup_seconds", "native_nonpow_prove_seconds",
                "native_pow_seconds", "native_runtime_other_seconds",
                "prover_process_residual_seconds", "verifier_process_seconds"))
            self.assertTrue(math.isclose(stages, row["paired_wall_seconds"], abs_tol=1e-5))
            phase = "first" if sample == 0 else "later"
            metrics = score["evaluation"]["cases"][str(count)]["metrics_by_phase"][phase]
            observed = {"wall": row["paired_wall_seconds"],
                        "after": row["paired_wall_seconds"] - row["native_pow_seconds"],
                        "proof": row["proof_bytes"], "rss": row["prover_peak_rss_bytes"]}
            if phase == "later":
                for target, value in observed.items():
                    bounds = metrics[target_name[target]]["predicted"]
                    coverage[target] += bounds["lower"] <= value <= bounds["upper"]
        self.assertTrue(all(sorted(samples) == list(range(12)) for samples in grouped.values()))
        self.assertEqual(coverage, {"wall": 31, "after": 30, "proof": 30, "rss": 32})

    def test_posthoc_historical_replay(self) -> None:
        saved = json.loads((SAVED / "posthoc-calibration-audit.json").read_bytes())
        self.assertEqual(saved, replay())
        self.assertFalse(saved["prospectively_pinned"])


if __name__ == "__main__":
    unittest.main()
