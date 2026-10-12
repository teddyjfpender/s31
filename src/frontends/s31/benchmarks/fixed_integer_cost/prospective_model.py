"""Small, deliberately local prospective fixed-integer cost model.

Only training-program medians fit point estimates. A disjoint calibration
width supplies empirical residual envelopes. The holdout is never read here.
"""

from __future__ import annotations

import math
import statistics

OPS = ("add", "mul")
LOWERINGS = ("direct-gate", "sparse-wide-gate")
FIT_WIDTHS = (16, 32)
CALIBRATION_WIDTH = 64
HOLDOUT_WIDTH = 128
STAGES = ("witness", "setup", "prove_non_pow", "interaction_pow", "fri_pow",
          "runtime_other", "process_residual", "verify")
TARGETS = ("build", "whole", "after_pow", "proof_bytes", "prover_rss")
GATES = {
    "whole_program_median_p90_error_max": 0.30,
    "after_pow_program_median_p90_error_max": 0.25,
    "proof_bytes_program_median_p90_error_max": 0.15,
    "prover_rss_program_median_p90_error_max": 0.20,
    "build_program_median_p90_error_max": 0.50,
    "whole_trial_interval_coverage_min": 0.75,
    "after_pow_trial_interval_coverage_min": 0.75,
    "whole_interval_upper_to_center_max": 8.0,
    "after_pow_interval_upper_to_center_max": 2.0,
}
EXTRAPOLATION_FLOOR = {
    "build": (0.5, 2.0), "whole": (0.5, 2.0),
    "after_pow": (0.7, 1.5), "proof_bytes": (0.8, 1.25),
    "prover_rss": (0.8, 1.25),
}


def positive(value: object) -> float:
    if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
        raise ValueError("expected a finite positive measurement")
    return float(value)


def quantile(values: list[float], q: float) -> float:
    if not values or not 0 <= q <= 1:
        raise ValueError("quantile requires observations and 0 <= q <= 1")
    ordered = sorted(positive(value) for value in values)
    index = q * (len(ordered) - 1)
    lo = int(index)
    return ordered[lo] + (ordered[min(lo + 1, len(ordered) - 1)] - ordered[lo]) * (index - lo)


def features(program: dict) -> dict:
    """Pre-build width and post-build AIR geometry are kept distinct."""
    geometry = program["geometry"]
    raw = geometry["raw"]["qm31_ops"]
    padded = geometry["padded"]["qm31_ops"]
    cells = geometry["preprocessed_cells"]
    if (type(program["width"]) is not int or type(raw) is not int or
            type(padded) is not int or type(cells) is not int or
            raw <= 0 or padded < raw or cells <= 0):
        raise ValueError("invalid fixed-integer AIR geometry")
    fri = geometry["visible_fri"]
    if type(fri["pow_bits"]) is not int or fri["pow_bits"] < 0:
        raise ValueError("invalid proof-of-work policy")
    return {
        "width": float(program["width"]),
        "raw_rows": float(raw),
        "padded_rows": float(padded),
        "preprocessed_cells": float(cells),
        "padded_n_log_n": padded * math.log2(padded),
        "pow_search_space": float(2 ** fri["pow_bits"]),
    }


FEATURE_BY_STAGE = {
    "build": "width",  # Available before package compilation.
    "witness": "raw_rows", "setup": "preprocessed_cells",
    "prove_non_pow": "padded_n_log_n", "interaction_pow": "pow_search_space",
    "fri_pow": "pow_search_space", "runtime_other": None,
    "process_residual": None, "verify": "padded_n_log_n",
    "proof_bytes": "padded_rows", "prover_rss": "preprocessed_cells",
}


def stage_trial(trial: dict) -> dict:
    stages = trial["stages"]
    if set(stages) != set(STAGES):
        raise ValueError("missing native stage or process residual")
    values = {}
    for name in STAGES:
        value = stages[name]
        if type(value) not in (int, float) or not math.isfinite(value):
            raise ValueError("invalid native stage timer")
        if value < 0 and (name != "process_residual" or value < -0.003):
            raise ValueError("invalid negative native stage timer")
        values[name] = float(value)
    whole = sum(values.values())
    if not math.isclose(whole, positive(trial["whole"]), abs_tol=1e-5):
        raise ValueError("native stages do not account for prover and verifier wall")
    return {
        "whole": whole,
        "after_pow": whole - values["interaction_pow"] - values["fri_pow"],
        "proof_bytes": positive(trial["proof_bytes"]),
        "prover_rss": positive(trial["prover_rss"]),
    }


def program_values(program: dict) -> dict:
    if not program["trials"]:
        raise ValueError("program needs verified native trials")
    rows = [stage_trial(trial) for trial in program["trials"]]
    return {
        **{name: statistics.median(trial["stages"][name]
                                   for trial in program["trials"])
           for name in STAGES},
        **{name: statistics.median(row[name] for row in rows)
           for name in ("proof_bytes", "prover_rss")},
        "build": positive(program["build_seconds"]),
    }


def affine_fit(low: tuple[float, float], high: tuple[float, float]) -> dict:
    x0, y0 = low
    x1, y1 = high
    if x1 < x0 or y0 < 0 or y1 < 0:
        raise ValueError("training feature order or stage measurement invalid")
    if x1 == x0 or y1 <= y0:
        return {"intercept": statistics.median((y0, y1)),
                "slope": 0.0, "feature": None}
    slope = max(0.0, (y1 - y0) / (x1 - x0))
    # A negative intercept would predict impossible negative small workloads.
    intercept = max(0.0, y1 - slope * x1)
    return {"intercept": intercept, "slope": slope, "feature": None}


def predict_one(fit: dict, feature_values: dict) -> float:
    x = 0.0 if fit["feature"] is None else feature_values[fit["feature"]]
    return max(1e-9, fit["intercept"] + fit["slope"] * x)


def predict_group(group: dict, program: dict) -> dict:
    f = features(program)
    stage = {name: predict_one(group["fits"][name], f) for name in STAGES}
    whole = sum(stage.values())
    return {"build": predict_one(group["fits"]["build"], f),
            "whole": whole,
            "after_pow": whole - stage["interaction_pow"] - stage["fri_pow"],
            "proof_bytes": predict_one(group["fits"]["proof_bytes"], f),
            "prover_rss": predict_one(group["fits"]["prover_rss"], f),
            "stage_centers": stage}


def fit(programs: list[dict]) -> dict:
    index = {(p["operation"], p["lowering"], p["width"]): p for p in programs}
    expected = {(op, lowering, width)
                for op in OPS for lowering in LOWERINGS
                for width in (*FIT_WIDTHS, CALIBRATION_WIDTH)}
    if set(index) != expected or len(programs) != len(expected):
        raise ValueError("fit requires exact, disjoint training/calibration roster")
    if len({p["source_sha256"] for p in programs}) != len(OPS) * 3:
        raise ValueError("source split has duplicate or missing source identities")
    groups = {}
    calibration_ratios = {name: [] for name in TARGETS}
    for op in OPS:
        for lowering in LOWERINGS:
            fit_rows = [index[op, lowering, width] for width in FIT_WIDTHS]
            values = [program_values(p) for p in fit_rows]
            geometry = [features(p) for p in fit_rows]
            fits = {}
            for name, feature in FEATURE_BY_STAGE.items():
                if feature is None:
                    fitted = {"intercept": statistics.median(row[name] for row in values),
                              "slope": 0.0, "feature": None}
                else:
                    fitted = affine_fit((geometry[0][feature], values[0][name]),
                                        (geometry[1][feature], values[1][name]))
                    fitted["feature"] = feature
                fits[name] = fitted
            group = {"operation": op, "lowering": lowering, "fits": fits,
                     "fit_source_sha256": [p["source_sha256"] for p in fit_rows]}
            calibrator = index[op, lowering, CALIBRATION_WIDTH]
            center = predict_group(group, calibrator)
            for trial in calibrator["trials"]:
                targets = stage_trial(trial)
                for name in TARGETS:
                    observed = (calibrator["build_seconds"] if name == "build" else
                                targets[name])
                    calibration_ratios[name].append(positive(observed) /
                                                    positive(center[name]))
            groups[f"{op}/{lowering}"] = group
    bands = {}
    for name, ratios in calibration_ratios.items():
        # Build contributes only one independent observation per calibrator.
        if name == "build":
            ratios = ratios[::len(index["add", "direct-gate", CALIBRATION_WIDTH]["trials"])]
            lower, upper = min(ratios) / 2, max(ratios) * 2
        else:
            lower, upper = quantile(ratios, .05), quantile(ratios, .95)
        floor_lo, floor_hi = EXTRAPOLATION_FLOOR[name]
        bands[name] = {"lower_ratio": min(floor_lo, 1.0, lower),
                       "upper_ratio": max(floor_hi, 1.0, upper),
                       "calibration_observations": len(ratios),
                       "method": "four-source doubled build envelope" if name == "build"
                                 else "pooled disjoint-width empirical p05/p95 ratio",
                       "predeclared_extrapolation_floor": [floor_lo, floor_hi]}
    return {"schema": "s31-fixed-integer-prospective-model-v1",
            "fit_widths": list(FIT_WIDTHS),
            "calibration_width": CALIBRATION_WIDTH,
            "holdout_width": HOLDOUT_WIDTH,
            "groups": groups, "bands": bands, "gates": GATES,
            "automatic_lowering_selection_enabled": False,
            "limits": "One compiler and host; two-width affine stage fits, u64 residual calibration, u128 unseen program holdout. PoW is stochastic and fixed policy is only a search-space feature. Empirical bands have predeclared extrapolation floors and are not confidence intervals."}


def score(model: dict, programs: list[dict]) -> dict:
    expected = {(op, lowering, HOLDOUT_WIDTH) for op in OPS for lowering in LOWERINGS}
    index = {(p["operation"], p["lowering"], p["width"]): p for p in programs}
    if set(index) != expected or len(programs) != len(expected):
        raise ValueError("score requires exact u128 holdout roster")
    cases = {}
    coverage = {name: [0, 0] for name in TARGETS}
    errors = {name: [] for name in TARGETS}
    for key in sorted(index):
        op, lowering, _ = key
        program = index[key]
        group = model["groups"][f"{op}/{lowering}"]
        if program["source_sha256"] in group["fit_source_sha256"]:
            raise ValueError("held-out source also appears in training")
        prediction = predict_group(group, program)
        actual_rows = [stage_trial(row) for row in program["trials"]]
        measured = {name: (positive(program["build_seconds"]) if name == "build"
                           else statistics.median(row[name] for row in actual_rows))
                    for name in TARGETS}
        outcome = {}
        for name in TARGETS:
            band = model["bands"][name]
            lo = prediction[name] * band["lower_ratio"]
            hi = prediction[name] * band["upper_ratio"]
            observations = ([measured[name]] if name == "build" else
                            [row[name] for row in actual_rows])
            covered = sum(lo <= value <= hi for value in observations)
            coverage[name][0] += covered
            coverage[name][1] += len(observations)
            error = abs(prediction[name] - measured[name]) / measured[name]
            errors[name].append(error)
            outcome[name] = {"predicted_center": prediction[name],
                             "interval": [lo, hi], "measured_median": measured[name],
                             "relative_error": error, "covered": covered,
                             "observations": len(observations)}
        cases[f"{op}/{lowering}"] = {"source_sha256": program["source_sha256"],
                                     "geometry": program["geometry"],
                                     "predicted_stages": prediction["stage_centers"],
                                     "targets": outcome}
    observed = {}
    for name in TARGETS:
        observed[f"{name}_program_median_p90_error"] = quantile(
            [max(e, 1e-12) for e in errors[name]], .9)
        observed[f"{name}_trial_interval_coverage"] = coverage[name][0] / coverage[name][1]
        observed[f"{name}_interval_upper_to_center"] = model["bands"][name]["upper_ratio"]
    gates = {}
    for name, limit in GATES.items():
        key = name.removesuffix("_min").removesuffix("_max")
        gates[name] = (observed[key] >= limit if name.endswith("_min")
                       else observed[key] <= limit)
    return {"schema": "s31-fixed-integer-prospective-score-v1",
            "cases": cases, "observed": observed, "gates": gates,
            "local_diagnostic_gate_pass": all(gates.values()),
            "scope": "u128 checked add and multiply, direct and sparse, one pinned host/compiler; not a universal cost predictor"}
