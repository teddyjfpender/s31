#!/usr/bin/env python3
"""Prospective local lifecycle scoring for the frozen V20 workload."""

from __future__ import annotations

import statistics


def score(record: dict, forecast: dict, gates: dict) -> dict:
    trials = record["trials"]
    if (len(trials) != 22 or
            [(row["claim_index"], row["repeat"]) for row in trials[:2]] !=
            [(0, 0), (0, 1)]):
        raise ValueError("V20 lifecycle roster differs")
    durations = [row["first_verified_process_wall_ns"] for row in trials]
    build = record["build_wall_ns"]
    if build <= 0 or any(value <= 0 for value in durations):
        raise ValueError("nonpositive lifecycle duration")
    observed = {
        "build_wall_ns": build,
        "first_post_build_verified_wall_ns": durations[0],
        "same_claim_immediate_repeat_wall_ns": durations[1],
        "warm_verified_wall_median_ns": statistics.median(durations[2:]),
        "build_plus_22_verified_proofs_sum_ns": build + sum(durations),
    }
    limits = {
        "build_wall_ns": "build_wall_relative_error_max",
        "first_post_build_verified_wall_ns": "first_post_build_verified_relative_error_max",
        "same_claim_immediate_repeat_wall_ns": "immediate_repeat_relative_error_max",
        "build_plus_22_verified_proofs_sum_ns": "build_plus_22_proofs_relative_error_max",
    }
    errors = {key: abs(observed[key] - forecast[key]) / observed[key]
              for key in limits}
    passed = {key: errors[key] <= gates[limit]
              for key, limit in limits.items()}
    return {
        "schema": "s31-mixed-cost-v20-lifecycle-score-v1",
        "measurement": "sum of separately measured process durations; excludes idle gaps",
        "observed": observed,
        "forecast": {key: forecast[key] for key in limits},
        "observed_relative_error": errors,
        "gates": passed,
        "all_gates_pass": all(passed.values()),
    }
