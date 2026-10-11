#!/usr/bin/env python3
"""Second-source score for a frozen geometry model on new operation families."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "geometry_transfer_v1" / "results-2026-10-11"
SCHEMA = "s31-operation-mix-transfer-v1"
OPS = ("add", "mul")
COUNTS = (96, 256, 448)
STRATUM = {96: "512", 256: "1024", 448: "1024"}
METRICS = ("paired_wall_seconds", "paired_after_pow_seconds", "proof_bytes",
           "prover_peak_rss_bytes")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assignment_sha(path: Path) -> str:
    value = json.loads(path.read_bytes())
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def measurement(row: dict, name: str) -> float:
    if (row.get("native_verifier_accepted") is not True or
            not row.get("changed_public_statement_rejected") or
            row.get("independent_value_oracle", {}).get("status") != "passed"):
        raise ValueError("saved trial lacks required native and value controls")
    if name in ("paired_wall_seconds", "paired_after_pow_seconds"):
        result = row["prove_seconds"] + row["verify_seconds"]
        if name == "paired_after_pow_seconds":
            stage = row.get("prover_stages") or {}
            result -= stage["fri_pow_seconds"] + stage["interaction_pow_seconds"]
    else:
        result = row[name]
    if type(result) not in (int, float) or not math.isfinite(result) or result <= 0:
        raise ValueError(f"invalid measured {name}")
    return float(result)


def check(root: Path) -> dict:
    plan = json.loads((root / "plan.json").read_bytes())
    report = json.loads((root / "heldout-report.json").read_bytes())
    score = json.loads((root / "heldout-score.json").read_bytes())
    old_plan = json.loads((PRIOR / "plan.json").read_bytes())
    calibration = json.loads((PRIOR / "calibration.json").read_bytes())
    if (plan.get("schema") != SCHEMA or plan.get("phase") != "planned-before-native-work" or
            plan.get("operations") != list(OPS) or plan.get("counts") != list(COUNTS) or
            plan.get("samples_per_program") != 12 or
            plan.get("identity", {}).get("independent_scorer_sha256") != sha(Path(__file__)) or
            plan.get("prior_plan_sha256") != sha(PRIOR / "plan.json") or
            plan.get("prior_calibration_sha256") != sha(PRIOR / "calibration.json") or
            calibration.get("plan_sha256") != sha(PRIOR / "plan.json") or
            plan["identity"]["compiler_sha256"] != old_plan["identity"]["compiler_sha256"] or
            plan["identity"]["engine_commit"] != old_plan["identity"]["engine_commit"] or
            plan["identity"]["host"] != old_plan["identity"]["host"] or
            report.get("plan_sha256") != sha(root / "plan.json") or
            score.get("plan_sha256") != sha(root / "plan.json") or
            score.get("heldout_report_sha256") != sha(root / "heldout-report.json") or
            score.get("prior_calibration_sha256") != sha(PRIOR / "calibration.json")):
        raise ValueError("sealed transfer protocol, prior model, or report hash mismatch")
    observed = {}
    gate = {name: True for name in METRICS}
    families = {op: {name: True for name in METRICS} for op in OPS}
    for op in OPS:
        for count in COUNTS:
            label = f"{op}-{count}"
            folder = root / "heldout" / label
            case_report = report["cases"][label]
            if (sha(folder / f"operation_mix_{op}_{count}.s31") !=
                    plan["sources"][label]["source_sha256"] or
                    sha(folder / "package" / "manifest.json") !=
                    case_report["package_manifest_sha256"] or
                    case_report["padded_qm31_rows"] != int(STRATUM[count])):
                raise ValueError("saved source, package, or geometry mismatch")
            rows = []
            for index in range(12):
                trial_dir = folder / "trials" / f"{index:03}"
                path = trial_dir / "trial-report.json"
                row = json.loads(path.read_bytes())
                if (assignment_sha(folder / "assignments" / f"{index:03}.json") !=
                        plan["sources"][label]["assignment_sha256"][index] or
                        sha(path) != case_report["trial_report_sha256"][index] or
                        sha(trial_dir / "proof.bin") != row["proof_sha256"] or
                        row["padded"]["qm31_ops"] != int(STRATUM[count]) or
                        row.get("independent_value_oracle_provenance") !=
                        plan["identity"]["independent_oracle_provenance"]):
                    raise ValueError("saved assignment, trial, proof, geometry, or oracle provenance mismatch")
                rows.append(row)
            observed[label] = {}
            for name in METRICS:
                median = statistics.median(measurement(row, name) for row in rows)
                predicted = calibration["model"][STRATUM[count]][name]["center"]
                error = abs(predicted - median) / median
                saved = score["cases"][label]["metrics"][name]
                if (not math.isclose(saved["predicted_center"], predicted, rel_tol=1e-12) or
                        not math.isclose(saved["observed"]["median"], median, rel_tol=1e-12) or
                        not math.isclose(saved["relative_median_error"], error, rel_tol=1e-12)):
                    raise ValueError("held-out transfer score differs from raw trials")
                observed[label][name] = error
                passed = error <= plan["diagnostic_relative_median_error_limits"][name]
                gate[name] &= passed
                families[op][name] &= passed
    if (gate != score["diagnostic_gates"] or
            families != score["operation_family_gates"] or
            all(gate.values()) != score["all_diagnostic_gates_pass"]):
        raise ValueError("saved operation family gates differ from independent score")
    return {"schema": SCHEMA, "phase": "independent-score-check",
            "case_count": 6, "trial_count": 72, "diagnostic_gates": gate,
            "operation_family_gates": families,
            "all_diagnostic_gates_pass": all(gate.values())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.out.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
