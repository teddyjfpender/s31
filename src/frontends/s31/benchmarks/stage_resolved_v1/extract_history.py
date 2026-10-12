#!/usr/bin/env python3
"""Extract pinned, audited prior native trials into a stage training ledger.

This is a post hoc extraction of earlier studies, completed before the new
lagged-topology prospective protocol. No old result or frozen model is refit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BENCH = HERE.parent
GEOMETRY = BENCH / "geometry_transfer_v1" / "results-2026-10-11"
MIX = BENCH / "operation_mix_transfer_v1" / "results-2026-10-11"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assignment_sha(path: Path) -> str:
    value = json.loads(path.read_bytes())
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def load(path: Path) -> dict:
    return json.loads(path.read_bytes())


def components(report: dict) -> dict[str, float]:
    native = report["prover_stages"]
    keys = ("witness_seconds", "setup_seconds", "prove_seconds",
            "prove_excluding_pow_seconds", "fri_pow_seconds",
            "interaction_pow_seconds", "runtime_other_seconds",
            "total_through_verification_seconds")
    if (any(type(native.get(key)) not in (float, int) or native[key] < 0
            for key in keys) or
            report.get("native_verifier_accepted") is not True or
            not report.get("changed_public_statement_rejected") or
            report.get("independent_value_oracle", {}).get("status") != "passed"):
        raise ValueError("historical trial lacks nonnegative native stages or controls")
    pow_seconds = native["fri_pow_seconds"] + native["interaction_pow_seconds"]
    if (not math.isclose(native["prove_seconds"],
                         native["prove_excluding_pow_seconds"] + pow_seconds,
                         abs_tol=1e-5) or
            not math.isclose(native["total_through_verification_seconds"],
                             native["witness_seconds"] + native["setup_seconds"] +
                             native["prove_seconds"] + native["runtime_other_seconds"],
                             abs_tol=1e-5)):
        raise ValueError("native stage timers do not partition native work")
    process_residual = report["prove_seconds"] - native["total_through_verification_seconds"]
    if process_residual < 0:
        raise ValueError("native package timer exceeds prover process wall")
    stages = {
        "witness": float(native["witness_seconds"]),
        "setup": float(native["setup_seconds"]),
        "native_nonpow_prove": float(native["prove_excluding_pow_seconds"]),
        "native_pow": float(pow_seconds),
        "runtime_other": float(native["runtime_other_seconds"]),
        "prover_process_residual": float(process_residual),
        "external_verifier": float(report["verify_seconds"]),
    }
    if (any(value < 0 or not math.isfinite(value) for value in stages.values()) or
            not math.isclose(sum(stages.values()),
                             report["prove_seconds"] + report["verify_seconds"],
                             abs_tol=1e-5)):
        raise ValueError("stage decomposition does not reconstruct whole process wall")
    return stages


def extract(geometry_root: Path, mix_root: Path) -> dict:
    geom_plan, geom_report = load(GEOMETRY / "plan.json"), load(GEOMETRY / "heldout-report.json")
    mix_plan, mix_report = load(MIX / "plan.json"), load(MIX / "heldout-report.json")
    if (geom_plan["identity"]["compiler_sha256"] != mix_plan["identity"]["compiler_sha256"] or
            geom_plan["identity"]["engine_commit"] != mix_plan["identity"]["engine_commit"] or
            geom_plan["identity"]["host"] != mix_plan["identity"]["host"]):
        raise ValueError("historical studies used different compiler, engine, or host")
    cohorts = [
        ("fit", "alternating", count, geometry_root / "heldout" / f"gates-{count}",
         geom_plan["sources"][str(count)], geom_report["cases"][str(count)])
        for count in (96, 256, 448)
    ] + [
        ("fit" if op == "add" else "interval_calibration", op, count,
         mix_root / "heldout" / f"{op}-{count}",
         mix_plan["sources"][f"{op}-{count}"], mix_report["cases"][f"{op}-{count}"])
        for op in ("add", "mul") for count in (96, 256, 448)
    ]
    programs = []
    for split, family, count, directory, planned, saved in cohorts:
        source_name = (f"geometry_transfer_{count}.s31" if family == "alternating"
                       else f"operation_mix_{family}_{count}.s31")
        if (sha(directory / source_name) != planned["source_sha256"] or
                sha(directory / "package" / "manifest.json") != saved["package_manifest_sha256"]):
            raise ValueError("historical source or package manifest changed")
        trials = []
        for sample in range(12):
            trial_dir = directory / "trials" / f"{sample:03}"
            report_path = trial_dir / "trial-report.json"
            assignment_path = directory / "assignments" / f"{sample:03}.json"
            report = load(report_path)
            if (sha(report_path) != saved["trial_report_sha256"][sample] or
                    sha(trial_dir / "proof.bin") != report["proof_sha256"] or
                    assignment_sha(assignment_path) != planned["assignment_sha256"][sample] or
                    report["padded"]["qm31_ops"] != planned["expected_padded_qm31_rows"]):
                raise ValueError("historical trial, proof, assignment, or AIR size changed")
            trials.append({
                "sample": sample,
                "assignment_sha256": planned["assignment_sha256"][sample],
                "trial_report_sha256": sha(report_path),
                "proof_sha256": report["proof_sha256"],
                "stages_seconds": components(report),
                "first_verified_wall_seconds": report["prove_seconds"] + report["verify_seconds"],
                "proof_bytes": report["proof_bytes"],
                "prover_peak_rss_bytes": report["prover_peak_rss_bytes"],
            })
        programs.append({
            "split": split, "family": family, "gates": count,
            "source_sha256": planned["source_sha256"],
            "raw_qm31_rows": saved["raw_qm31_rows"],
            "padded_qm31_rows": saved["padded_qm31_rows"],
            "trials": trials,
        })
    return {
        "schema": "s31-stage-resolved-history-v1",
        "status": "post-hoc-extraction-before-new-prospective-phase",
        "compiler_sha256": geom_plan["identity"]["compiler_sha256"],
        "engine_commit": geom_plan["identity"]["engine_commit"],
        "host": geom_plan["identity"]["host"],
        "geometry_plan_sha256": sha(GEOMETRY / "plan.json"),
        "geometry_audit_sha256": sha(GEOMETRY / "audit.json"),
        "operation_plan_sha256": sha(MIX / "plan.json"),
        "operation_audit_sha256": sha(MIX / "audit.json"),
        "fit_programs": 6, "fit_trials": 72,
        "interval_calibration_programs": 3, "interval_calibration_trials": 36,
        "programs": programs,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--geometry-root", type=Path,
                        default=ROOT / "zig-out/s31-geometry-transfer-v1")
    parser.add_argument("--operation-root", type=Path,
                        default=ROOT / "zig-out/s31-operation-mix-transfer-v1")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise FileExistsError("historical stage ledger is write-once")
    ledger = extract(args.geometry_root.resolve(), args.operation_root.resolve())
    args.out.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
