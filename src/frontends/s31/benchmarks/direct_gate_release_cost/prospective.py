#!/usr/bin/env python3
"""Small prospective, same-stack held-out check for bounded direct-gate cost.

This is independent of the frozen V8r1 protocol/model. `plan` seals the fixed
train/held-out source and witness rosters before either native measurement.
`train` seals simple constant predictions before `heldout` builds any package.
The empirical training ranges are descriptive, not confidence intervals.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
sys.path.insert(0, str(S31 / "python"))

import s31
from measure import assignment_for, measure, source_for
from runtime.cost_model import distribution

TRAIN = (1, 4, 16)
HELDOUT = (2, 8, 12)
SAMPLES = 12
METRICS = ("paired_wall_seconds", "paired_after_pow_seconds", "proof_bytes",
           "prover_peak_rss_bytes", "pow_seconds")
DIAGNOSTIC_LIMITS = {
    "paired_wall_seconds": .50,
    "paired_after_pow_seconds": .25,
    "proof_bytes": .10,
    "prover_peak_rss_bytes": .10,
}
SCHEMA = "s31-bounded-direct-gate-prospective-v1"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def host() -> dict:
    return {"platform": platform.platform(), "machine": platform.machine(),
            "python": platform.python_version(),
            "zig": s31.invoke("zig", "version").strip()}


def planned_sources() -> dict:
    result = {}
    with tempfile.TemporaryDirectory(prefix="s31-cost-plan-") as directory:
        temp = Path(directory)
        for gates in (*TRAIN, *HELDOUT):
            digests = []
            for sample in range(SAMPLES):
                assignment = temp / f"{gates}-{sample}.json"
                s31.write_json(assignment, assignment_for(gates, sample))
                digests.append(s31.assignment_digest(assignment))
            result[str(gates)] = {
                "source_sha256": sha(source_for(gates).encode()),
                "assignment_sha256": digests,
            }
    return result


def plan_payload() -> dict:
    return {
        "schema": SCHEMA, "status": "local-premeasurement-plan",
        "compiler_sha256": s31.compiler_fingerprint(),
        "measurement_script_sha256": s31.file_hash(HERE / "measure.py"),
        "prospective_script_sha256": s31.file_hash(Path(__file__)),
        "host": host(), "train": list(TRAIN), "heldout": list(HELDOUT),
        "samples_per_program": SAMPLES, "sources": planned_sources(),
        "prediction_rule": ("For each metric, predict the median of three training-program "
                            "medians; use pooled training-trial min/max only as a "
                            "descriptive range. No coefficients, selection, or refitting."),
        "diagnostic_relative_median_error_limits": DIAGNOSTIC_LIMITS,
        "status_limit": ("The gates are local diagnostics on three related held-out "
                         "programs, not a general accuracy certificate."),
    }


def create_plan(out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    path = out / "plan.json"
    if path.exists() or any((out / split).exists() for split in ("train", "heldout")):
        raise ValueError("prospective evidence already exists; use a fresh output root")
    s31.write_json(path, plan_payload())


def checked_plan(out: Path) -> dict:
    path = out / "plan.json"
    saved = json.loads(path.read_bytes())
    if saved != plan_payload():
        raise ValueError("plan, host, compiler, script, or planned inputs changed")
    return saved


def target(trial: dict, name: str) -> float:
    stages = trial.get("prover_stages") or {}
    pow_seconds = stages.get("fri_pow_seconds", None)
    interaction = stages.get("interaction_pow_seconds", None)
    if name in ("pow_seconds", "paired_after_pow_seconds"):
        if pow_seconds is None or interaction is None:
            raise ValueError("native PoW timers are required")
        total_pow = pow_seconds + interaction
    if name == "pow_seconds":
        value = total_pow
    elif name == "paired_wall_seconds":
        value = trial["prove_seconds"] + trial["verify_seconds"]
    elif name == "paired_after_pow_seconds":
        value = trial["prove_seconds"] + trial["verify_seconds"] - total_pow
    elif name == "proof_bytes":
        value = trial["proof_bytes"]
    elif name == "prover_peak_rss_bytes":
        value = trial["prover_peak_rss_bytes"]
    else:
        raise ValueError(f"unknown cost target: {name}")
    if value is None or not math.isfinite(value) or value <= 0:
        raise ValueError(f"missing or invalid {name}")
    return float(value)


def read_measured(out: Path, split: str, plan: dict) -> dict[int, list[dict]]:
    report_path = out / split / "exploratory-report.json"
    report = json.loads(report_path.read_bytes())
    gates_set = TRAIN if split == "train" else HELDOUT
    if (report.get("schema") != "s31-exploratory-bounded-direct-gate-cost-v1" or
        report.get("measurement_script_sha256") != plan["measurement_script_sha256"] or
        report.get("samples_per_case") != SAMPLES or
        set(report.get("cases", {})) != {str(gates) for gates in gates_set}):
        raise ValueError("measured report does not match prospective plan")
    measured = {}
    for gates in gates_set:
        case = report["cases"][str(gates)]
        planned = plan["sources"][str(gates)]
        if (case["source_sha256"] != planned["source_sha256"] or
            case["assignment_sha256"] != planned["assignment_sha256"] or
            case["compiler_sha256"] != plan["compiler_sha256"] or
            case["package_reused"] is not False or
            case["cost_report"]["profile"] != "direct-m31-v4" or
            case["cost_report"]["padded"]["qm31_ops"] != 512 or
            case["cost_report"]["preprocessed_cells"] != 4096):
            raise ValueError(f"{split}/{gates}: wrong compiler, inputs, or AIR geometry")
        trials = []
        for sample, expected_digest in enumerate(case["trial_report_sha256"]):
            path = out / split / f"gates-{gates:02d}" / "trials" / f"{sample:03d}" / "trial-report.json"
            if s31.file_hash(path) != expected_digest:
                raise ValueError(f"{split}/{gates}/{sample}: trial report changed")
            trial = json.loads(path.read_bytes())
            if (trial.get("native_verifier_accepted") is not True or
                trial.get("independent_value_oracle", {}).get("status") != "passed" or
                not trial.get("changed_public_statement_rejected") or
                trial.get("proof_sha256") != case["proof_sha256"][sample]):
                raise ValueError(f"{split}/{gates}/{sample}: native proof control failed")
            for metric in METRICS:
                target(trial, metric)
            trials.append(trial)
        if len(trials) != SAMPLES:
            raise ValueError(f"{split}/{gates}: wrong trial count")
        measured[gates] = trials
    return measured


def calibration(measured: dict[int, list[dict]]) -> dict:
    if set(measured) != set(TRAIN):
        raise ValueError("calibration requires all predeclared train programs")
    predictions = {}
    for metric in METRICS:
        per_program = {str(gates): statistics.median(target(trial, metric)
                            for trial in measured[gates]) for gates in TRAIN}
        pooled = [target(trial, metric) for gates in TRAIN for trial in measured[gates]]
        predictions[metric] = {
            "center": statistics.median(per_program.values()),
            "training_program_medians": per_program,
            "descriptive_training_min": min(pooled),
            "descriptive_training_max": max(pooled),
            "training_trials": len(pooled),
        }
    return predictions


def score(predictions: dict, measured: dict[int, list[dict]]) -> dict:
    if set(measured) != set(HELDOUT):
        raise ValueError("score requires all predeclared held-out programs")
    cases = {}
    for gates in HELDOUT:
        metrics = {}
        for name in METRICS:
            values = [target(trial, name) for trial in measured[gates]]
            center = predictions[name]["center"]
            observed = statistics.median(values)
            metrics[name] = {
                "predicted_center": center, "observed": distribution(values),
                "relative_median_error": abs(center - observed) / observed,
                "descriptive_training_range_covered_trials": sum(
                    predictions[name]["descriptive_training_min"] <= value <=
                    predictions[name]["descriptive_training_max"] for value in values),
                "trials": len(values),
            }
        cases[str(gates)] = metrics
    gate = {name: all(cases[str(gates)][name]["relative_median_error"] <= limit
                      for gates in HELDOUT)
            for name, limit in DIAGNOSTIC_LIMITS.items()}
    return {"cases": cases, "diagnostic_gates": gate,
            "all_diagnostic_gates_pass": all(gate.values())}


def run_phase(out: Path, phase: str) -> None:
    plan = checked_plan(out)
    if phase == "train":
        if (out / "train").exists() or (out / "calibration.json").exists():
            raise ValueError("train evidence already exists")
        measure(TRAIN, SAMPLES, out / "train")
        measured = read_measured(out, "train", plan)
        s31.write_json(out / "calibration.json", {
            "schema": SCHEMA, "status": "sealed-before-heldout-measurement",
            "plan_sha256": s31.file_hash(out / "plan.json"),
            "train_report_sha256": s31.file_hash(out / "train/exploratory-report.json"),
            "predictions": calibration(measured),
        })
    elif phase == "heldout":
        saved = json.loads((out / "calibration.json").read_bytes())
        if (saved.get("schema") != SCHEMA or
            saved.get("status") != "sealed-before-heldout-measurement" or
            saved.get("plan_sha256") != s31.file_hash(out / "plan.json") or
            saved.get("train_report_sha256") != s31.file_hash(out / "train/exploratory-report.json") or
            saved.get("predictions") != calibration(read_measured(out, "train", plan))):
            raise ValueError("training calibration changed before held-out work")
        if (out / "heldout").exists() or (out / "heldout-score.json").exists():
            raise ValueError("held-out evidence already exists")
        calibration_sha = s31.file_hash(out / "calibration.json")
        measure(HELDOUT, SAMPLES, out / "heldout")
        measured = read_measured(out, "heldout", plan)
        result = score(saved["predictions"], measured)
        s31.write_json(out / "heldout-score.json", {
            "schema": SCHEMA, "status": "local-heldout-diagnostic",
            "plan_sha256": saved["plan_sha256"],
            "calibration_sha256_before_heldout": calibration_sha,
            "heldout_report_sha256": s31.file_hash(out / "heldout/exploratory-report.json"),
            **result,
        })
    else:
        raise ValueError("unknown phase")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("plan", "train", "heldout"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    if args.phase == "plan":
        create_plan(out)
    else:
        run_phase(out, args.phase)
    print(out / ("plan.json" if args.phase == "plan" else
                 "calibration.json" if args.phase == "train" else "heldout-score.json"))


if __name__ == "__main__":
    main()
