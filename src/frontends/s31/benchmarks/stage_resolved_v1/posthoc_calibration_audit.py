#!/usr/bin/env python3
"""Post hoc, second-source replay of the presealed historical calibration.

This script was written after the prospective plan was sealed. It audits a
frozen artifact; it is not part of the prospectively pinned scoring software.
"""

from __future__ import annotations

import hashlib
import json
import math
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
COUNTS = (96, 256, 448)
STAGES = ("witness", "setup", "native_nonpow_prove", "native_pow",
          "runtime_other", "prover_process_residual", "external_verifier")
TARGETS = ("first_verified_wall_seconds", "after_reported_pow_seconds",
           "proof_bytes", "prover_peak_rss_bytes")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def percentile(xs: list[float], p: float) -> float:
    ys = sorted(xs)
    position = (len(ys) - 1) * p
    lo = math.floor(position)
    hi = math.ceil(position)
    return ys[lo] * (hi - position) + ys[hi] * (position - lo) if hi != lo else ys[lo]


def observation(trial: dict, target: str) -> float:
    if target == "after_reported_pow_seconds":
        return trial["first_verified_wall_seconds"] - trial["stages_seconds"]["native_pow"]
    return trial[target]


def same(actual: object, expected: object, path: str = "calibration") -> None:
    if isinstance(expected, dict):
        if not isinstance(actual, dict) or actual.keys() != expected.keys():
            raise ValueError(f"{path}: object keys differ")
        for key in expected:
            same(actual[key], expected[key], f"{path}.{key}")
    elif isinstance(expected, list):
        if not isinstance(actual, list) or len(actual) != len(expected):
            raise ValueError(f"{path}: list differs")
        for index, (left, right) in enumerate(zip(actual, expected)):
            same(left, right, f"{path}[{index}]")
    elif isinstance(expected, (float, int)) and not isinstance(expected, bool):
        if not isinstance(actual, (float, int)) or not math.isclose(
                actual, expected, rel_tol=1e-12, abs_tol=1e-12):
            raise ValueError(f"{path}: numeric value differs: {actual} vs {expected}")
    elif actual != expected:
        raise ValueError(f"{path}: value differs: {actual} vs {expected}")


def replay() -> dict:
    ledger_file = HERE / "historical-stage-ledger.json"
    calibration_file = HERE / "calibration.json"
    ledger = json.loads(ledger_file.read_bytes())
    calibration = json.loads(calibration_file.read_bytes())
    if calibration["historical_stage_ledger_sha256"] != digest(ledger_file):
        raise ValueError("historical ledger hash changed")
    if calibration["model_source_sha256"] != digest(HERE / "model.py"):
        raise ValueError("frozen model source hash changed")
    if (calibration["compiler_sha256"] != ledger["compiler_sha256"] or
            calibration["engine_commit"] != ledger["engine_commit"] or
            calibration["host"] != ledger["host"]):
        raise ValueError("historical compiler, engine, or host identity changed")
    programs = ledger["programs"]
    if (len(programs) != 9 or
            sorted((p["split"], p["family"], p["gates"]) for p in programs) !=
            sorted([("fit", family, count) for family in ("alternating", "add")
                    for count in COUNTS] +
                   [("interval_calibration", "mul", count) for count in COUNTS])):
        raise ValueError("historical source split changed")
    for program in programs:
        if ([t["sample"] for t in program["trials"]] != list(range(12)) or
                len({t["assignment_sha256"] for t in program["trials"]}) != 12):
            raise ValueError("historical source trial sequence changed")
        for trial in program["trials"]:
            if not math.isclose(sum(trial["stages_seconds"].values()),
                                trial["first_verified_wall_seconds"], abs_tol=1e-5):
                raise ValueError("historical stage accounting changed")

    centers = {}
    for count in COUNTS:
        fit = [p for p in programs if p["split"] == "fit" and p["gates"] == count]
        if {p["family"] for p in fit} != {"alternating", "add"}:
            raise ValueError("incomplete fit source roster")
        stage_records = {}
        for stage in STAGES:
            if stage == "prover_process_residual":
                first = {p["family"]: p["trials"][0]["stages_seconds"][stage]
                         for p in fit}
                later = {p["family"]: statistics.median(
                    t["stages_seconds"][stage] for t in p["trials"][1:]) for p in fit}
                stage_records[stage] = {
                    "first_center": statistics.median(first.values()),
                    "later_center": statistics.median(later.values()),
                    "first_fit_program_values": first,
                    "later_fit_program_medians": later,
                }
            else:
                medians = {p["family"]: statistics.median(
                    t["stages_seconds"][stage] for t in p["trials"]) for p in fit}
                stage_records[stage] = {"center": statistics.median(medians.values()),
                                        "fit_program_medians": medians}
        same(calibration["cases"][str(count)]["stage_centers_seconds"],
             stage_records, f"cases.{count}.stages")
        shared = sum(stage_records[stage]["center"] for stage in STAGES
                     if stage != "prover_process_residual")
        size_centers = {target: statistics.median(
            statistics.median(observation(t, target) for t in p["trials"])
            for p in fit) for target in ("proof_bytes", "prover_peak_rss_bytes")}
        by_phase = {}
        for phase in ("first", "later"):
            wall = shared + stage_records["prover_process_residual"][f"{phase}_center"]
            by_phase[phase] = {
                "first_verified_wall_seconds": wall,
                "after_reported_pow_seconds": wall - stage_records["native_pow"]["center"],
                **size_centers,
            }
        same(calibration["cases"][str(count)]["target_centers_by_phase"],
             by_phase, f"cases.{count}.targets")
        same(calibration["cases"][str(count)]["fit_source_sha256"],
             sorted(p["source_sha256"] for p in fit), f"cases.{count}.sources")
        centers[count] = by_phase

    ratios = {phase: {target: [] for target in TARGETS}
              for phase in ("first", "later")}
    for program in programs:
        if program["split"] != "interval_calibration":
            continue
        for trial in program["trials"]:
            phase = "first" if trial["sample"] == 0 else "later"
            for target in TARGETS:
                ratios[phase][target].append(
                    observation(trial, target) / centers[program["gates"]][phase][target])
    bands = {}
    for phase in ("first", "later"):
        bands[phase] = {}
        for target in TARGETS:
            values = ratios[phase][target]
            if phase == "first":
                low, high = min(values) / 2, max(values) * 2
                method = "three source-level first-use ratios: min/2 to max*2"
            else:
                low, high = percentile(values, .025), percentile(values, .975)
                method = "33 later-trial ratios: empirical 2.5th/97.5th percentiles"
            bands[phase][target] = {
                "lower_ratio": min(1.0, low),
                "upper_ratio": max(1.0, high),
                "calibration_trial_count": len(values),
                "method": method,
            }
    same(calibration["whole_target_ratio_bands_by_phase"], bands, "bands")
    same(calibration["fit_source_sha256"], sorted(p["source_sha256"] for p in programs
                                                if p["split"] == "fit"), "fit sources")
    same(calibration["interval_calibration_source_sha256"], sorted(
        p["source_sha256"] for p in programs if p["split"] == "interval_calibration"),
        "interval sources")
    return {
        "phase": "post-hoc-second-source-historical-calibration-audit",
        "historical_stage_ledger_sha256": digest(ledger_file),
        "calibration_sha256": digest(calibration_file),
        "fit_programs": 6, "fit_trials": 72,
        "interval_calibration_programs": 3, "interval_calibration_trials": 36,
        "stage_centers_replayed": len(COUNTS) * len(STAGES),
        "target_centers_replayed": len(COUNTS) * 2 * len(TARGETS),
        "ratio_bands_replayed": 2 * len(TARGETS),
        "exact_replay_passed": True,
        "prospectively_pinned": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, sort_keys=True))
