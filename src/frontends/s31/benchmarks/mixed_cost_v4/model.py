"""Predeclared v4 warm-wall distribution and proof-size interval arithmetic.

This module uses training and calibration rows only. Realized heldout PoW
durations are never predictor features.
"""

from __future__ import annotations

import math
import statistics

PROGRAMS = {"relay_n3": 3, "relay_n7": 7, "twist_n3": 3, "twist_n7": 7}
FIT_ROWS_PER_PROGRAM = 40
CAL_ROWS_PER_PROGRAM = 39
TARGET_QUANTILES = (0.05, 0.50, 0.95)
PROOF_COVERAGE_QUANTILE = 0.90


def _checked(rows: list[dict], expected: int) -> None:
    if len(rows) != len(PROGRAMS) * expected:
        raise ValueError("wrong frozen row count")
    for name, count in PROGRAMS.items():
        selected = [row for row in rows if row.get("program") == name]
        if len(selected) != expected:
            raise ValueError("wrong frozen program count")
        for row in selected:
            if row.get("call_count") != count or any(
                type(row.get(key)) is not int or row[key] <= 0
                for key in ("wall_ns", "fri_pow_ns", "interaction_pow_ns", "proof_bytes")
            ) or row["fri_pow_ns"] + row["interaction_pow_ns"] >= row["wall_ns"]:
                raise ValueError("invalid or nested row duration")


def _ols(xs: list[int], ys: list[float]) -> tuple[float, float]:
    mean_x, mean_y = statistics.mean(xs), statistics.mean(ys)
    denominator = sum((x - mean_x) ** 2 for x in xs)
    if denominator <= 0:
        raise ValueError("no call-count variation")
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys)) / denominator
    return mean_y - slope * mean_x, slope


def fit(fit_rows: list[dict], calibration_rows: list[dict]) -> dict:
    """Fit once on claim indices 1..40; calibrate on indices 41..79."""
    _checked(fit_rows, FIT_ROWS_PER_PROGRAM)
    _checked(calibration_rows, CAL_ROWS_PER_PROGRAM)
    counts = list(PROGRAMS.values())
    nonpow_medians = []
    proof_medians = []
    for name in PROGRAMS:
        selected = [row for row in fit_rows if row["program"] == name]
        nonpow_medians.append(statistics.median(
            row["wall_ns"] - row["fri_pow_ns"] - row["interaction_pow_ns"]
            for row in selected))
        proof_medians.append(statistics.median(row["proof_bytes"] for row in selected))
    base_intercept, base_slope = _ols(counts, nonpow_medians)
    if base_intercept <= 0 or base_slope < 0:
        base_intercept, base_slope = statistics.median(nonpow_medians), 0.0
    proof_intercept, proof_slope = _ols(counts, proof_medians)
    if proof_intercept <= 0 or proof_slope <= 0:
        raise ValueError("predeclared proof-size fit is nonpositive")
    # A geometric hash search approaches an exponential clock when p is small.
    # The scale is inferred only from fit rows at the fixed PoW difficulties.
    fri_scale = statistics.median(row["fri_pow_ns"] for row in fit_rows) / math.log(2)
    interaction_scale = statistics.median(
        row["interaction_pow_ns"] for row in fit_rows) / math.log(2)
    if fri_scale <= 0 or interaction_scale <= 0:
        raise ValueError("invalid PoW scale")
    residuals = sorted(
        row["wall_ns"] - row["fri_pow_ns"] - row["interaction_pow_ns"] -
        (base_intercept + base_slope * row["call_count"])
        for row in calibration_rows)
    proof_ratios = sorted(
        abs(row["proof_bytes"] /
            (proof_intercept + proof_slope * row["call_count"]) - 1)
        for row in calibration_rows)
    # Split-conformal rank for nominal 90% two-sided coverage.
    rank = math.ceil((len(proof_ratios) + 1) * PROOF_COVERAGE_QUANTILE) - 1
    width = proof_ratios[rank]
    return {"schema": "s31-mixed-cost-v4-distribution-model",
            "base_intercept_ns": base_intercept,
            "base_slope_ns_per_call": base_slope,
            "fri_exponential_scale_ns": fri_scale,
            "interaction_exponential_scale_ns": interaction_scale,
            "calibration_nonpow_residuals_ns": residuals,
            "proof_intercept_bytes": proof_intercept,
            "proof_slope_bytes_per_call": proof_slope,
            "proof_relative_half_width": width,
            "proof_calibration_rank_1_based": rank + 1,
            "fit_rows": len(fit_rows), "calibration_rows": len(calibration_rows)}


def _pow_sum_cdf(value: float, first_scale: float, second_scale: float) -> float:
    if value <= 0:
        return 0.0
    if abs(first_scale - second_scale) <= 1e-10 * max(first_scale, second_scale):
        x = value / first_scale
        return max(0.0, min(1.0, 1 - math.exp(-x) * (1 + x)))
    survivor = (first_scale * math.exp(-value / first_scale) -
                second_scale * math.exp(-value / second_scale)) / (
                    first_scale - second_scale)
    return max(0.0, min(1.0, 1 - survivor))


def wall_cdf(model: dict, count: int, wall_ns: float) -> float:
    if count <= 0:
        raise ValueError("positive call count required")
    residuals = model["calibration_nonpow_residuals_ns"]
    if len(residuals) != len(PROGRAMS) * CAL_ROWS_PER_PROGRAM:
        raise ValueError("wrong frozen calibration count")
    base = model["base_intercept_ns"] + model["base_slope_ns_per_call"] * count
    a, b = model["fri_exponential_scale_ns"], model["interaction_exponential_scale_ns"]
    if min(base, a, b) <= 0:
        raise ValueError("invalid model scale")
    return statistics.mean(
        _pow_sum_cdf(wall_ns - base - residual, a, b)
        for residual in residuals)


def wall_quantile(model: dict, count: int, probability: float) -> float:
    if not 0 < probability < 1:
        raise ValueError("open-interval probability required")
    base = model["base_intercept_ns"] + model["base_slope_ns_per_call"] * count
    residuals = model["calibration_nonpow_residuals_ns"]
    low = min(base + residual for residual in residuals)
    high = max(base + residual for residual in residuals) + 20 * (
        model["fri_exponential_scale_ns"] + model["interaction_exponential_scale_ns"])
    while wall_cdf(model, count, high) < probability:
        high += high - low
    for _ in range(80):
        middle = (low + high) / 2
        if wall_cdf(model, count, middle) < probability:
            low = middle
        else:
            high = middle
    return high


def prediction(model: dict, count: int) -> dict:
    proof = model["proof_intercept_bytes"] + model["proof_slope_bytes_per_call"] * count
    width = model["proof_relative_half_width"]
    if proof <= 0 or not 0 <= width < 1:
        raise ValueError("invalid proof prediction")
    return {"warm_wall_quantile_ns": {str(q): wall_quantile(model, count, q)
                                      for q in TARGET_QUANTILES},
            "proof_bytes_center": proof,
            "proof_bytes_interval": [proof * (1 - width), proof * (1 + width)]}
