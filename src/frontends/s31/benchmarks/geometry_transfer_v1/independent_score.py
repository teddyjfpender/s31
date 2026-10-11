#!/usr/bin/env python3
"""Second-source arithmetic check of saved geometry-transfer cost evidence.

No imports from study.py or the S31 package. It reads the raw trial ledgers,
recomputes training centers and held-out errors, and checks saved score gates.
Native proof replay is a separate `study.py audit` step.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

TRAIN = (32, 192, 384)
HELDOUT = (96, 256, 448)
STRATUM = {32: "512", 96: "512", 192: "512",
           256: "1024", 384: "1024", 448: "1024"}
METRICS = ("paired_wall_seconds", "paired_after_pow_seconds", "proof_bytes",
           "prover_peak_rss_bytes")
SCHEMA = "s31-direct-gate-geometry-transfer-v1"


def file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def value(record: dict, metric: str) -> float:
    if (record.get("native_verifier_accepted") is not True or
            not record.get("changed_public_statement_rejected") or
            record.get("independent_value_oracle", {}).get("status") != "passed"):
        raise ValueError("trial lacks native verifier, changed claim, or oracle control")
    if metric in ("paired_wall_seconds", "paired_after_pow_seconds"):
        number = record["prove_seconds"] + record["verify_seconds"]
        if metric == "paired_after_pow_seconds":
            timers = record.get("prover_stages") or {}
            number -= timers["fri_pow_seconds"] + timers["interaction_pow_seconds"]
    else:
        number = record[metric]
    if type(number) not in (float, int) or not math.isfinite(number) or number <= 0:
        raise ValueError(f"invalid {metric}")
    return float(number)


def rows(root: Path, phase: str, count: int, samples: int,
         report: dict) -> list[dict]:
    folder = root / phase / f"gates-{count}"
    reports = []
    for index in range(samples):
        trial_dir = folder / "trials" / f"{index:03}"
        report_path = trial_dir / "trial-report.json"
        record = json.loads(report_path.read_bytes())
        if (file_sha(report_path) != report["cases"][str(count)]["trial_report_sha256"][index] or
                file_sha(trial_dir / "proof.bin") != record["proof_sha256"] or
                record["padded"]["qm31_ops"] != int(STRATUM[count])):
            raise ValueError("saved trial hash or row geometry mismatch")
        for metric in METRICS:
            value(record, metric)
        reports.append(record)
    return reports


def check(root: Path) -> dict:
    plan = json.loads((root / "plan.json").read_bytes())
    calibration = json.loads((root / "calibration.json").read_bytes())
    train_report = json.loads((root / "train-report.json").read_bytes())
    held_report = json.loads((root / "heldout-report.json").read_bytes())
    score = json.loads((root / "heldout-score.json").read_bytes())
    if (plan.get("schema") != SCHEMA or plan.get("train") != list(TRAIN) or
            plan.get("heldout") != list(HELDOUT) or
            plan.get("samples_per_program") != 12 or
            plan.get("identity", {}).get("independent_scorer_sha256") !=
                file_sha(Path(__file__)) or
            calibration.get("plan_sha256") != file_sha(root / "plan.json") or
            calibration.get("train_report_sha256") != file_sha(root / "train-report.json") or
            score.get("plan_sha256") != file_sha(root / "plan.json") or
            score.get("calibration_sha256_before_heldout") !=
                file_sha(root / "calibration.json") or
            score.get("heldout_report_sha256") != file_sha(root / "heldout-report.json") or
            train_report.get("phase") != "train" or held_report.get("phase") != "heldout"):
        raise ValueError("saved protocol, scorer, or phase hash mismatch")
    saved_model = calibration["model"]
    training = {count: rows(root, "train", count, 12, train_report)
                for count in TRAIN}
    heldout = {count: rows(root, "heldout", count, 12, held_report)
               for count in HELDOUT}
    for stratum in ("512", "1024"):
        counts = [n for n in TRAIN if STRATUM[n] == stratum]
        for metric in METRICS:
            centers = {str(n): statistics.median(value(row, metric)
                                                 for row in training[n]) for n in counts}
            expected = statistics.median(centers.values())
            saved = saved_model[stratum][metric]
            if (saved["training_program_medians"] != centers or
                    not math.isclose(saved["center"], expected, rel_tol=1e-12)):
                raise ValueError("training-only prediction differs from raw trial reports")
    gate = {}
    for metric in METRICS:
        limit = plan["diagnostic_relative_median_error_limits"][metric]
        errors = []
        for count in HELDOUT:
            observed = statistics.median(value(row, metric) for row in heldout[count])
            predicted = saved_model[STRATUM[count]][metric]["center"]
            error = abs(predicted - observed) / observed
            saved = score["cases"][str(count)]["metrics"][metric]
            if (not math.isclose(saved["observed"]["median"], observed, rel_tol=1e-12) or
                    not math.isclose(saved["predicted_center"], predicted, rel_tol=1e-12) or
                    not math.isclose(saved["relative_median_error"], error, rel_tol=1e-12)):
                raise ValueError("held-out median or error differs from raw trial reports")
            errors.append(error)
        gate[metric] = all(error <= limit for error in errors)
    if gate != score["diagnostic_gates"] or all(gate.values()) != score["all_diagnostic_gates_pass"]:
        raise ValueError("saved diagnostic gate differs from second-source calculation")
    return {"schema": SCHEMA, "phase": "independent-score-check",
            "trial_reports_checked": 72, "train_programs": len(TRAIN),
            "heldout_programs": len(HELDOUT), "diagnostic_gates": gate,
            "all_diagnostic_gates_pass": all(gate.values())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.out.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
