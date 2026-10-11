"""Training-only stage decomposition and empirical whole-target intervals.

Fit uses alternating + all-add source medians. All-multiply is reserved for
interval calibration. The future lagged-alternating family is never read here.
"""

from __future__ import annotations

import hashlib
import json
import math
import statistics
from pathlib import Path

STAGES = ("witness", "setup", "native_nonpow_prove", "native_pow",
          "runtime_other", "prover_process_residual", "external_verifier")
TARGETS = ("first_verified_wall_seconds", "after_reported_pow_seconds",
           "proof_bytes", "prover_peak_rss_bytes")
COUNTS = (96, 256, 448)
LIMITS = {
    "later_first_verified_wall_seconds_trial_coverage_min": 0.75,
    "later_after_reported_pow_seconds_trial_coverage_min": 0.80,
    "later_proof_bytes_trial_coverage_min": 0.80,
    "later_prover_peak_rss_bytes_trial_coverage_min": 0.80,
    "first_first_verified_wall_seconds_trial_coverage_min": 2 / 3,
    "later_first_verified_wall_seconds_upper_to_center_max": 8.0,
    "later_after_reported_pow_seconds_upper_to_center_max": 1.5,
    "later_after_reported_pow_seconds_program_median_error_max": 0.15,
    "later_proof_bytes_program_median_error_max": 0.10,
    "later_prover_peak_rss_bytes_program_median_error_max": 0.10,
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def quantile(values: list[float], fraction: float) -> float:
    if not values or not 0 <= fraction <= 1 or any(not math.isfinite(x) for x in values):
        raise ValueError("quantile needs finite values and a fraction in [0,1]")
    ordered = sorted(values)
    rank = fraction * (len(ordered) - 1)
    i = int(rank)
    return ordered[i] + (ordered[min(i + 1, len(ordered) - 1)] - ordered[i]) * (rank - i)


def target(trial: dict, name: str) -> float:
    if name == "after_reported_pow_seconds":
        value = (trial["first_verified_wall_seconds"] -
                 trial["stages_seconds"]["native_pow"])
    else:
        value = trial[name]
    if type(value) not in (float, int) or not math.isfinite(value) or value <= 0:
        raise ValueError(f"invalid {name}")
    return float(value)


def validate(ledger: dict) -> None:
    if (ledger.get("schema") != "s31-stage-resolved-history-v1" or
            ledger.get("fit_programs") != 6 or ledger.get("fit_trials") != 72 or
            ledger.get("interval_calibration_programs") != 3 or
            ledger.get("interval_calibration_trials") != 36):
        raise ValueError("historical stage ledger has wrong declared split")
    programs = ledger["programs"]
    roster = {(p["split"], p["family"], p["gates"]) for p in programs}
    expected = {("fit", family, count)
                for family in ("alternating", "add") for count in COUNTS} | \
               {("interval_calibration", "mul", count) for count in COUNTS}
    if roster != expected or len(programs) != 9:
        raise ValueError("historical fit/calibration source roster changed")
    for program in programs:
        if len(program["trials"]) != 12 or len({t["assignment_sha256"]
                                                 for t in program["trials"]}) != 12:
            raise ValueError("historical source lacks 12 distinct trial assignments")
        for trial in program["trials"]:
            stages = trial.get("stages_seconds")
            if (type(stages) is not dict or set(stages) != set(STAGES) or
                    any(type(v) not in (int, float) or not math.isfinite(v) or v < 0
                        for v in stages.values()) or
                    not math.isclose(sum(stages.values()),
                                     trial["first_verified_wall_seconds"], abs_tol=1e-5)):
                raise ValueError("historical stage sum differs from whole process wall")
            for name in TARGETS:
                target(trial, name)


def fit(ledger: dict, ledger_sha256: str, model_source_sha256: str) -> dict:
    validate(ledger)
    fit_rows = [p for p in ledger["programs"] if p["split"] == "fit"]
    calibrators = [p for p in ledger["programs"] if p["split"] == "interval_calibration"]
    cases = {}
    for count in COUNTS:
        sources = [p for p in fit_rows if p["gates"] == count]
        if {p["family"] for p in sources} != {"alternating", "add"}:
            raise ValueError("fit needs one alternating and one add source per count")
        components = {}
        for name in STAGES:
            if name == "prover_process_residual":
                first = {p["family"]: p["trials"][0]["stages_seconds"][name]
                         for p in sources}
                later = {p["family"]: statistics.median(
                    t["stages_seconds"][name] for t in p["trials"][1:])
                         for p in sources}
                components[name] = {
                    "first_center": statistics.median(first.values()),
                    "later_center": statistics.median(later.values()),
                    "first_fit_program_values": first,
                    "later_fit_program_medians": later,
                }
                continue
            medians = {p["family"]: statistics.median(
                t["stages_seconds"][name] for t in p["trials"]) for p in sources}
            components[name] = {"center": statistics.median(medians.values()),
                                "fit_program_medians": medians}
        shared = sum(components[name]["center"] for name in STAGES
                     if name != "prover_process_residual")
        centers = {}
        for name in ("proof_bytes", "prover_peak_rss_bytes"):
            value = statistics.median(
                statistics.median(target(t, name) for t in p["trials"])
                for p in sources)
            centers[name] = value
        by_phase = {}
        for phase in ("first", "later"):
            wall = shared + components["prover_process_residual"][f"{phase}_center"]
            by_phase[phase] = {
                "first_verified_wall_seconds": wall,
                "after_reported_pow_seconds": wall - components["native_pow"]["center"],
                "proof_bytes": centers["proof_bytes"],
                "prover_peak_rss_bytes": centers["prover_peak_rss_bytes"],
            }
        cases[str(count)] = {"stage_centers_seconds": components,
                             "target_centers_by_phase": by_phase,
                             "fit_source_sha256": sorted(p["source_sha256"] for p in sources)}
    ratios = {phase: {name: [] for name in TARGETS} for phase in ("first", "later")}
    calibrator_hashes = []
    for program in calibrators:
        count = program["gates"]
        calibrator_hashes.append(program["source_sha256"])
        for trial in program["trials"]:
            phase = "first" if trial["sample"] == 0 else "later"
            for name in TARGETS:
                ratios[phase][name].append(target(trial, name) /
                    cases[str(count)]["target_centers_by_phase"][phase][name])
    bands = {}
    for phase in ("first", "later"):
        bands[phase] = {}
        for name, values in ratios[phase].items():
            if phase == "first":
                # Only one first-use trial per calibration source: use a wide
                # envelope, never call three observations a confidence band.
                lower, upper = min(values) * .5, max(values) * 2.0
                method = "three source-level first-use ratios: min/2 to max*2"
            else:
                lower, upper = quantile(values, .025), quantile(values, .975)
                method = "33 later-trial ratios: empirical 2.5th/97.5th percentiles"
            bands[phase][name] = {
                "lower_ratio": min(1.0, lower),
                "upper_ratio": max(1.0, upper),
                "calibration_trial_count": len(values),
                "method": method,
            }
    return {
        "schema": "s31-stage-resolved-cost-v1-calibration",
        "status": "fit-and-intervals-sealed-before-new-family-native-build",
        "historical_stage_ledger_sha256": ledger_sha256,
        "model_source_sha256": model_source_sha256,
        "compiler_sha256": ledger["compiler_sha256"],
        "engine_commit": ledger["engine_commit"],
        "host": ledger["host"],
        "fit_source_sha256": sorted(p["source_sha256"] for p in fit_rows),
        "interval_calibration_source_sha256": sorted(calibrator_hashes),
        "stage_names": list(STAGES), "target_names": list(TARGETS),
        "cases": cases, "whole_target_ratio_bands_by_phase": bands,
        "diagnostic_limits": LIMITS,
        "prediction_scope": "one host/compiler/engine direct-gate family at 96/256/448 gates; split historical fit/calibration by entire source; no chip or cross-host transfer",
        "interval_interpretation": "first-use and later-process empirical historical ratio bands; only 3 first-use calibrators; not confidence intervals or finite-sample tail guarantees",
        "automatic_lowering_selection_enabled": False,
    }


def predict(model: dict, count: int, sample: int) -> dict:
    if model.get("schema") != "s31-stage-resolved-cost-v1-calibration" or count not in COUNTS:
        raise ValueError("unsupported model or gate count")
    if not 0 <= sample < 12:
        raise ValueError("sample must be within the predeclared 12-trial roster")
    phase = "first" if sample == 0 else "later"
    centers = model["cases"][str(count)]["target_centers_by_phase"][phase]
    bands = model["whole_target_ratio_bands_by_phase"][phase]
    return {name: {"center": centers[name],
                   "lower": centers[name] * bands[name]["lower_ratio"],
                   "upper": centers[name] * bands[name]["upper_ratio"]}
            for name in TARGETS}


def evaluate(model: dict, heldout: list[dict]) -> dict:
    if (sorted(p.get("gates") for p in heldout) != list(COUNTS) or
            len({p.get("source_sha256") for p in heldout}) != 3 or
            set(model["fit_source_sha256"] + model["interval_calibration_source_sha256"]) &
            {p["source_sha256"] for p in heldout}):
        raise ValueError("new held-out program roster or disjointness changed")
    rows = {}
    coverage = {phase: {name: 0 for name in TARGETS}
                for phase in ("first", "later")}
    totals = {"first": 0, "later": 0}
    for program in heldout:
        count = program["gates"]
        trials = program["trials"]
        if len(trials) != 12:
            raise ValueError("new source needs 12 trials")
        if [t.get("sample") for t in trials] != list(range(12)):
            raise ValueError("held-out trials must preserve first-use sample order")
        stats = {}
        for phase, chosen in (("first", trials[:1]), ("later", trials[1:])):
            bands = predict(model, count, 0 if phase == "first" else 1)
            stats[phase] = {}
            totals[phase] += len(chosen)
            for name in TARGETS:
                observed = [target(t, name) for t in chosen]
                median = statistics.median(observed)
                band = bands[name]
                covered = sum(band["lower"] <= value <= band["upper"]
                              for value in observed)
                coverage[phase][name] += covered
                stats[phase][name] = {
                    "observed_median": median, "observed_p90": quantile(observed, .9),
                    "predicted": band,
                    "median_relative_error": abs(band["center"] - median) / median,
                    "covered_trials": covered, "trials": len(observed),
                }
        residual = model["cases"][str(count)]["stage_centers_seconds"][
            "prover_process_residual"]
        rows[str(count)] = {"source_sha256": program["source_sha256"],
                            "padded_qm31_rows": program["padded_qm31_rows"],
                            "metrics_by_phase": stats,
                            "prover_process_residual": {
                                "predicted_first_seconds": residual["first_center"],
                                "observed_first_seconds": trials[0]["stages_seconds"]["prover_process_residual"],
                                "predicted_later_seconds": residual["later_center"],
                                "observed_later_median_seconds": statistics.median(
                                    t["stages_seconds"]["prover_process_residual"]
                                    for t in trials[1:]),
                            }}
    observed = {}
    for phase in ("first", "later"):
        for name in TARGETS:
            observed[f"{phase}_{name}_trial_coverage"] = coverage[phase][name] / totals[phase]
    for name in ("first_verified_wall_seconds", "after_reported_pow_seconds"):
        observed[f"later_{name}_upper_to_center"] = model[
            "whole_target_ratio_bands_by_phase"]["later"][name]["upper_ratio"]
    for name in ("after_reported_pow_seconds", "proof_bytes", "prover_peak_rss_bytes"):
        observed[f"later_{name}_program_median_error"] = max(
            rows[str(count)]["metrics_by_phase"]["later"][name]["median_relative_error"]
            for count in COUNTS)
    gates = {}
    for name, bound in LIMITS.items():
        key = name.removesuffix("_min").removesuffix("_max")
        gates[name] = observed[key] >= bound if name.endswith("_min") else observed[key] <= bound
    return {"schema": "s31-stage-resolved-cost-v1-heldout-score",
            "cases": rows, "diagnostic_observed": observed,
            "diagnostic_limits": LIMITS, "diagnostic_gates": gates,
            "all_diagnostic_gates_pass": all(gates.values()),
            "automatic_lowering_selection_enabled": False}
