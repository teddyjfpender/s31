#!/usr/bin/env python3
"""Evaluate a deliberately small S31 cost predictor on held-out programs.

The evaluator never splits trials from the same source program across train
and test.  It does not enable automatic lowering selection.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path


METRICS = {
    "paired_prove_and_verify_wall_seconds": "padded_rows",
    "proof_bytes": "padded_rows",
    "prover_peak_rss_bytes": "padded_rows",
}
LEGACY_FAMILIES = {
    "arithmetic_record": "arithmetic",
    "blake2s_merkle": "hash",
    "signed_i32_division": "fixed_width",
}


def _positive(value: object, label: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (float, int)) or not math.isfinite(value) or value <= 0:
        raise ValueError(f"{label} must be a positive finite number")
    return float(value)


def _features(case: dict) -> dict[str, float]:
    padded = case["padded"]
    if not isinstance(padded, dict) or not padded:
        raise ValueError("case needs padded component rows")
    rows = sum(_positive(value, "padded row count") for value in padded.values() if value != 0)
    return {
        "padded_rows": _positive(rows, "total padded rows"),
        "preprocessed_cells": _positive(case["preprocessed_cells"], "preprocessed cells"),
    }


def _observed(case: dict, metric: str) -> float | None:
    model = case["observed_cost_model"]
    if model["verified_trials"] < 3:
        return None
    item = model["metrics"].get(metric)
    if item is None or item["observations"] < 3:
        return None
    return _positive(item["median"], metric)


def _fit_log_line(points: list[tuple[float, float]]) -> tuple[float, float] | None:
    if len(points) < 2:
        return None
    xs = [math.log(_positive(x, "scale feature")) for x, _ in points]
    ys = [math.log(_positive(y, "measured cost")) for _, y in points]
    mean_x, mean_y = statistics.mean(xs), statistics.mean(ys)
    denominator = sum((x - mean_x) ** 2 for x in xs)
    if denominator < 1e-12:
        return None
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys)) / denominator
    return mean_y - slope * mean_x, slope


def _predict(fit: tuple[float, float], scale: float) -> float:
    predicted = math.exp(fit[0] + fit[1] * math.log(scale))
    return _positive(predicted, "predicted cost")


def _training_envelope(points: list[tuple[float, float]]) -> float | None:
    """Largest leave-one-program-out log error within the training set."""
    if len(points) < 3:
        return None
    residuals = []
    for index, (scale, measured) in enumerate(points):
        fit = _fit_log_line(points[:index] + points[index + 1:])
        if fit is None:
            return None
        residuals.append(abs(math.log(_predict(fit, scale) / measured)))
    return max(1e-12, max(residuals))


def _p90(values: list[float]) -> float:
    ordered = sorted(values)
    rank = 0.9 * (len(ordered) - 1)
    lo = int(rank)
    return ordered[lo] + (ordered[min(lo + 1, len(ordered) - 1)] - ordered[lo]) * (rank - lo)


def evaluate(report: dict) -> dict:
    """Leave one source program out; fit only other programs in its family."""
    cases = report.get("cases")
    if not isinstance(cases, dict) or not cases:
        raise ValueError("cost corpus needs a nonempty cases object")
    records = []
    seen_sources = set()
    for name, case in sorted(cases.items()):
        source = case["source_sha256"]
        if not isinstance(source, str) or len(source) != 64:
            raise ValueError(f"{name}: invalid source digest")
        if source in seen_sources:
            raise ValueError("duplicate source digest would leak a program across train/test")
        seen_sources.add(source)
        family = case.get("family", LEGACY_FAMILIES.get(name))
        if not isinstance(family, str) or not family:
            raise ValueError(f"{name}: missing workload family")
        assignment_hashes = case.get("assignment_sha256")
        if assignment_hashes is not None and (
                not isinstance(assignment_hashes, list) or
                len(assignment_hashes) != case["observed_cost_model"]["verified_trials"] or
                len(set(assignment_hashes)) != len(assignment_hashes)):
            raise ValueError(f"{name}: assignments must be distinct and match verified trial count")
        records.append({"name": name, "source_sha256": source, "family": family,
                        "features": _features(case), "case": case})
    for family in {item["family"] for item in records}:
        members = [item for item in records if item["family"] == family]
        for field in ("compiler_sha256", "lowering", "profile", "visible_fri"):
            values = {json.dumps(item["case"].get(field), sort_keys=True) for item in members}
            if len(values) != 1:
                raise ValueError(f"{family}: mixed {field} values invalidate a family fit")
    predictions = []
    gaps = []
    for held_out in records:
        same_family = [item for item in records if item["family"] == held_out["family"]
                       and item["source_sha256"] != held_out["source_sha256"]]
        for metric, feature in METRICS.items():
            actual = _observed(held_out["case"], metric)
            train = [(item["features"][feature], observed)
                     for item in same_family
                     if (observed := _observed(item["case"], metric)) is not None]
            fit = _fit_log_line(train)
            if actual is None or fit is None:
                gaps.append({"program": held_out["name"], "family": held_out["family"],
                             "metric": metric, "reason": "missing measured metric or two distinct training scales"})
                continue
            estimate = _predict(fit, held_out["features"][feature])
            envelope = _training_envelope(train)
            observed_metric = held_out["case"]["observed_cost_model"]["metrics"][metric]
            measured_mad = observed_metric.get("median_absolute_deviation")
            predictions.append({
                "program": held_out["name"], "family": held_out["family"], "metric": metric,
                "held_out_source_sha256": held_out["source_sha256"],
                "training_programs": len(train), "scale_feature": feature,
                "training_source_sha256": sorted(
                    item["source_sha256"] for item in same_family
                    if _observed(item["case"], metric) is not None),
                "log_fit": {"intercept": fit[0], "slope": fit[1]},
                "scale_value": held_out["features"][feature],
                "measured": actual, "predicted": estimate,
                "measured_median_absolute_deviation": measured_mad,
                "measured_relative_mad": measured_mad / actual if measured_mad is not None else None,
                "measured_p90": observed_metric.get("p90_interpolated"),
                "absolute_error": abs(estimate - actual),
                "relative_error": abs(estimate - actual) / actual,
                "training_loo_log_error_envelope": envelope,
                "empirical_interval": (
                    {"lower": estimate * math.exp(-envelope),
                     "upper": estimate * math.exp(envelope)} if envelope is not None else None),
            })
    accuracy = {}
    for metric in METRICS:
        metric_predictions = [item for item in predictions if item["metric"] == metric]
        values = [item["relative_error"] for item in metric_predictions]
        absolute = [item["absolute_error"] for item in metric_predictions]
        intervals = [item for item in metric_predictions if item["empirical_interval"] is not None]
        coverage = (sum(item["empirical_interval"]["lower"] <= item["measured"] <=
                        item["empirical_interval"]["upper"] for item in intervals) / len(intervals)
                    if intervals else None)
        accuracy[metric] = ({"held_out_programs": len(values),
                             "median_absolute_error": statistics.median(absolute),
                             "p90_absolute_error": _p90(absolute),
                             "median_relative_error": statistics.median(values),
                             "p90_relative_error": _p90(values), "max_relative_error": max(values),
                             "intervals_available": len(intervals),
                             "empirical_interval_coverage": coverage}
                            if values else {"held_out_programs": 0,
                                            "median_absolute_error": None, "p90_absolute_error": None,
                                            "median_relative_error": None, "p90_relative_error": None,
                                            "max_relative_error": None, "intervals_available": 0,
                                            "empirical_interval_coverage": None})
    families = {item["family"] for item in records}
    accuracy_gate = (len(families) >= 3 and all(
        sum(item["family"] == family for item in records) >= 4 for family in families) and all(
        accuracy[metric]["held_out_programs"] >= 3 and
        accuracy[metric]["p90_relative_error"] <= 0.20 and
        accuracy[metric]["max_relative_error"] <= 0.35 and
        accuracy[metric]["intervals_available"] == accuracy[metric]["held_out_programs"] and
        accuracy[metric]["empirical_interval_coverage"] >= 0.80
        for metric in METRICS))
    reasons = []
    if not accuracy_gate:
        reasons.append("held-out coverage or accuracy gate failed: require three families with four programs each; per metric, p90 relative error <=20%, max <=35%, and empirical interval coverage >=80%")
    reasons.append("automatic profile selection also needs profile soundness equivalence and validation on additional hosts and scales")
    return {
        "schema": "s31-whole-prover-held-out-evaluation-v1",
        "split": "leave one full source program out; no assignment from that program enters training",
        "fit": "per-family ordinary least squares on log(median cost) versus log(static scale feature)",
        "programs": len(records), "families": sorted(families),
        "predictions": predictions, "unpredicted": gaps, "accuracy": accuracy,
        "uncertainty": "empirical interval uses maximum training leave-one-program-out log error; with fewer than three training programs it is unavailable; this is not a calibrated confidence interval",
        "cost_accuracy_gate_pass": accuracy_gate,
        "automatic_lowering_selection_enabled": False,
        "selection_reasons": reasons,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    source = args.corpus.read_bytes()
    result = evaluate(json.loads(source))
    result["corpus_sha256"] = hashlib.sha256(source).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
