#!/usr/bin/env python3
"""Frozen online repeat forecast; first proof PoW is observed before its repeat."""

from __future__ import annotations

import statistics


def score(record: dict, forecast: dict, gates: dict) -> dict:
    trials = record["trials"]
    if len(trials) != 42:
        raise ValueError("V24 requires 21 adjacent claim pairs")
    indices = []
    predicted, observed, residuals, errors = [], [], [], []
    center = forecast["repeat_nonpow_center_ns"]
    for first, repeat in zip(trials[::2], trials[1::2], strict=True):
        index = first["claim_index"]
        indices.append(index)
        if (first["repeat"] != 0 or repeat["repeat"] != 1 or
                repeat["claim_index"] != index or
                first["assignment_sha256"] != repeat["assignment_sha256"] or
                first["statement_sha256"] != repeat["statement_sha256"] or
                first["proof_sha256"] != repeat["proof_sha256"]):
            raise ValueError("same-claim proof pair identity or order differs")
        first_pow = first["native_phases_ns"]["fri_pow_ns"] + first[
            "native_phases_ns"]["interaction_pow_ns"]
        repeat_pow = repeat["native_phases_ns"]["fri_pow_ns"] + repeat[
            "native_phases_ns"]["interaction_pow_ns"]
        wall = repeat["first_verified_process_wall_ns"]
        if (first_pow <= 0 or first_pow >= first["first_verified_process_wall_ns"] or
                repeat_pow <= 0 or wall <= repeat_pow):
            raise ValueError("nonpositive paired timing or repeat non-PoW residual")
        pred = center + first_pow
        predicted.append(pred)
        observed.append(wall)
        residuals.append(wall - repeat_pow)
        errors.append(abs(wall - pred) / wall)
    if indices[0] != 0 or sorted(indices[1:]) != list(range(1, 21)):
        raise ValueError("V24 unique fresh-claim roster differs")
    first = trials[0]["first_verified_process_wall_ns"]
    build = record["build_wall_ns"]
    durations = [row["first_verified_process_wall_ns"] for row in trials]
    if build <= 0 or any(value <= 0 for value in durations):
        raise ValueError("nonpositive lifecycle duration")
    whole = build + sum(durations)
    nonpow_median = statistics.median(residuals)
    paired_median_error = statistics.median(errors)
    paired_hits = sum(value <= 0.35 for value in errors)
    errors_global = {
        "build_wall_ns": abs(build - forecast["build_wall_ns"]) / build,
        "first_post_build_verified_wall_ns": abs(
            first - forecast["first_post_build_verified_wall_ns"]) / first,
        "build_plus_42_verified_proofs_sum_ns": abs(
            whole - forecast["build_plus_42_verified_proofs_sum_ns"]) / whole,
        "repeat_nonpow_median_ns": abs(nonpow_median - center) / nonpow_median,
    }
    passed = {
        "build_wall_ns": errors_global["build_wall_ns"] <= gates["build_wall_relative_error_max"],
        "first_post_build_verified_wall_ns": errors_global[
            "first_post_build_verified_wall_ns"] <= gates["first_post_build_verified_relative_error_max"],
        "build_plus_42_verified_proofs_sum_ns": errors_global[
            "build_plus_42_verified_proofs_sum_ns"] <= gates["build_plus_42_proofs_relative_error_max"],
        "paired_repeat_median_relative_error": paired_median_error <= gates[
            "paired_repeat_median_relative_error_max"],
        "paired_repeat_35pct_hits": paired_hits >= gates[
            "paired_repeat_relative_error_within_35pct_min"],
        "repeat_nonpow_median_ns": errors_global["repeat_nonpow_median_ns"] <= gates[
            "repeat_nonpow_median_relative_error_max"],
    }
    return {
        "schema": "s31-mixed-cost-v24-conditional-repeat-score-v1",
        "measurement": "sum of separately measured process durations; excludes idle gaps",
        "forecast_rule": "frozen N8 non-PoW center plus first same-claim measured FRI and interaction PoW",
        "paired_claim_indices": indices,
        "repeat_predicted_wall_ns": predicted,
        "repeat_observed_wall_ns": observed,
        "repeat_observed_nonpow_ns": residuals,
        "repeat_observed_relative_errors": errors,
        "paired_repeat_median_relative_error": paired_median_error,
        "paired_repeat_35pct_hits": paired_hits,
        "repeat_observed_nonpow_median_ns": nonpow_median,
        "observed": {"build_wall_ns": build,
                     "first_post_build_verified_wall_ns": first,
                     "build_plus_42_verified_proofs_sum_ns": whole},
        "forecast": {key: forecast[key] for key in (
            "build_wall_ns", "first_post_build_verified_wall_ns",
            "build_plus_42_verified_proofs_sum_ns", "repeat_nonpow_center_ns")},
        "observed_relative_error": errors_global,
        "gates": passed,
        "all_gates_pass": all(passed.values()),
    }
