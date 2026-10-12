#!/usr/bin/env python3
"""Second-source score of saved lagged-topology proofs against a frozen model."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
COUNTS = (96, 256, 448)
TARGETS = ("first_verified_wall_seconds", "after_reported_pow_seconds",
           "proof_bytes", "prover_peak_rss_bytes")
SCHEMA = "s31-stage-resolved-prospective-v1"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assignment_sha(path: Path) -> str:
    value = json.loads(path.read_bytes())
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def q90(values: list[float]) -> float:
    ordered = sorted(values)
    rank = .9 * (len(ordered) - 1)
    index = int(rank)
    return ordered[index] + (ordered[min(index + 1, len(ordered) - 1)] -
                             ordered[index]) * (rank - index)


def close(a: float, b: float) -> bool:
    return math.isclose(a, b, rel_tol=1e-10, abs_tol=1e-10)


def measures(report: dict) -> dict:
    native = report["prover_stages"]
    pow_time = native["fri_pow_seconds"] + native["interaction_pow_seconds"]
    native_sum = (native["witness_seconds"] + native["setup_seconds"] +
                  native["prove_seconds"] + native["runtime_other_seconds"])
    if (report.get("native_verifier_accepted") is not True or
            not report.get("changed_public_statement_rejected") or
            report.get("independent_value_oracle", {}).get("status") != "passed" or
            not math.isclose(native["prove_seconds"],
                             native["prove_excluding_pow_seconds"] + pow_time,
                             abs_tol=1e-5) or
            not math.isclose(native_sum, native["total_through_verification_seconds"],
                             abs_tol=1e-5)):
        raise ValueError("native stages or proof/value controls invalid")
    wall = report["prove_seconds"] + report["verify_seconds"]
    residual = report["prove_seconds"] - native["total_through_verification_seconds"]
    if residual < 0 or not math.isclose(wall,
            native["witness_seconds"] + native["setup_seconds"] +
            native["prove_excluding_pow_seconds"] + pow_time +
            native["runtime_other_seconds"] + residual + report["verify_seconds"],
            abs_tol=1e-5):
        raise ValueError("stage decomposition differs from measured process wall")
    return {"first_verified_wall_seconds": wall,
            "after_reported_pow_seconds": wall - pow_time,
            "proof_bytes": report["proof_bytes"],
            "prover_peak_rss_bytes": report["prover_peak_rss_bytes"],
            "prover_process_residual": residual}


def check(root: Path) -> dict:
    plan = json.loads((root / "plan.json").read_bytes())
    report = json.loads((root / "heldout-report.json").read_bytes())
    saved = json.loads((root / "heldout-score.json").read_bytes())
    model = json.loads((HERE / "calibration.json").read_bytes())
    if (plan.get("schema") != SCHEMA or plan.get("counts") != list(COUNTS) or
            plan.get("samples_per_program") != 12 or
            plan.get("historical_stage_ledger_sha256") !=
                sha(HERE / "historical-stage-ledger.json") or
            plan.get("calibration_sha256") != sha(HERE / "calibration.json") or
            plan["identity"]["independent_scorer_sha256"] != sha(Path(__file__)) or
            plan["identity"]["model_sha256"] != sha(HERE / "model.py") or
            model["model_source_sha256"] != sha(HERE / "model.py") or
            model["historical_stage_ledger_sha256"] != sha(HERE / "historical-stage-ledger.json") or
            report.get("plan_sha256") != sha(root / "plan.json") or
            saved.get("plan_sha256") != sha(root / "plan.json") or
            saved.get("calibration_sha256") != sha(HERE / "calibration.json") or
            saved.get("heldout_report_sha256") != sha(root / "heldout-report.json")):
        raise ValueError("plan, model, scorer, or report content pin differs")
    evaluation = saved["evaluation"]
    observed = {}
    covered = {phase: {name: 0 for name in TARGETS}
               for phase in ("first", "later")}
    for count in COUNTS:
        directory = root / "heldout" / f"gates-{count}"
        case_report = report["cases"][str(count)]
        case_saved = evaluation["cases"][str(count)]
        if (sha(directory / f"lagged_alternating_{count}.s31") !=
                plan["sources"][str(count)]["source_sha256"] or
                sha(directory / "package" / "manifest.json") !=
                case_report["package_manifest_sha256"] or
                case_report["padded_qm31_rows"] !=
                plan["sources"][str(count)]["expected_padded_qm31_rows"]):
            raise ValueError("saved source, package, or geometry differs")
        trials = []
        for sample in range(12):
            trial_dir = directory / "trials" / f"{sample:03}"
            path = trial_dir / "trial-report.json"
            trial = json.loads(path.read_bytes())
            if (sha(path) != case_report["trial_report_sha256"][sample] or
                    sha(trial_dir / "proof.bin") != trial["proof_sha256"] or
                    assignment_sha(directory / "assignments" / f"{sample:03}.json") !=
                    plan["sources"][str(count)]["assignment_sha256"][sample] or
                    trial.get("independent_value_oracle_provenance") !=
                    plan["identity"]["independent_oracle_provenance"] or
                    trial["padded"]["qm31_ops"] != case_report["padded_qm31_rows"]):
                raise ValueError("saved trial, proof, assignment, oracle, or AIR size differs")
            trials.append(measures(trial))
        residual_saved = case_saved["prover_process_residual"]
        residual_model = model["cases"][str(count)]["stage_centers_seconds"][
            "prover_process_residual"]
        if (not close(residual_saved["predicted_first_seconds"],
                      residual_model["first_center"]) or
                not close(residual_saved["observed_first_seconds"],
                          trials[0]["prover_process_residual"]) or
                not close(residual_saved["predicted_later_seconds"],
                          residual_model["later_center"]) or
                not close(residual_saved["observed_later_median_seconds"],
                          statistics.median(t["prover_process_residual"]
                                            for t in trials[1:]))):
            raise ValueError("first-use/later process residual differs")
        for phase, chosen in (("first", trials[:1]), ("later", trials[1:])):
            for name in TARGETS:
                values = [trial[name] for trial in chosen]
                center = model["cases"][str(count)]["target_centers_by_phase"][phase][name]
                band = model["whole_target_ratio_bands_by_phase"][phase][name]
                low = center * band["lower_ratio"]
                high = center * band["upper_ratio"]
                median = statistics.median(values)
                hits = sum(low <= value <= high for value in values)
                covered[phase][name] += hits
                expected = case_saved["metrics_by_phase"][phase][name]
                if (not close(expected["observed_median"], median) or
                        not close(expected["observed_p90"], q90(values)) or
                        not close(expected["predicted"]["center"], center) or
                        not close(expected["predicted"]["lower"], low) or
                        not close(expected["predicted"]["upper"], high) or
                        not close(expected["median_relative_error"],
                                  abs(center - median) / median) or
                        expected["covered_trials"] != hits or
                        expected["trials"] != len(chosen)):
                    raise ValueError("saved held-out median, band, or coverage differs")
    for phase, denom in (("first", 3), ("later", 33)):
        for name in TARGETS:
            key = f"{phase}_{name}_trial_coverage"
            observed[key] = covered[phase][name] / denom
            if not close(evaluation["diagnostic_observed"][key], observed[key]):
                raise ValueError("saved aggregate interval coverage differs")
    for name in ("first_verified_wall_seconds", "after_reported_pow_seconds"):
        key = f"later_{name}_upper_to_center"
        observed[key] = model["whole_target_ratio_bands_by_phase"]["later"][name]["upper_ratio"]
    for name in ("after_reported_pow_seconds", "proof_bytes", "prover_peak_rss_bytes"):
        key = f"later_{name}_program_median_error"
        observed[key] = max(evaluation["cases"][str(count)]["metrics_by_phase"]["later"][name][
            "median_relative_error"] for count in COUNTS)
    for key, value in observed.items():
        if not close(evaluation["diagnostic_observed"][key], value):
            raise ValueError("saved diagnostic observation differs")
    gates = {}
    for key, limit in plan["diagnostic_limits"].items():
        name = key.removesuffix("_min").removesuffix("_max")
        gates[key] = observed[name] >= limit if key.endswith("_min") else observed[name] <= limit
    if gates != evaluation["diagnostic_gates"] or all(gates.values()) != evaluation[
            "all_diagnostic_gates_pass"]:
        raise ValueError("saved diagnostic gates differ")
    return {"schema": SCHEMA, "phase": "independent-stage-score-check",
            "trial_count": 36, "case_count": 3,
            "diagnostic_gates": gates,
            "all_diagnostic_gates_pass": all(gates.values())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.out.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
