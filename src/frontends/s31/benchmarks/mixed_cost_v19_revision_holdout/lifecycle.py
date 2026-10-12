#!/usr/bin/env python3
"""Report measured package-build and proof costs without fitting cold gates."""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path

import freeze as f


def summarize(result: dict) -> dict:
    record = result["record"]
    trials = record["trials"]
    if len(trials) != f.CLAIMS + 2 or [row["claim_index"] for row in trials[:2]] != [0, 0]:
        raise ValueError("unexpected build/cold/warm lifecycle roster")
    build = record["build_wall_ns"]
    first = trials[0]["first_verified_process_wall_ns"]
    immediate_repeat = trials[1]["first_verified_process_wall_ns"]
    warm = [row["first_verified_process_wall_ns"] for row in trials[2:]]
    if build <= 0 or first <= 0 or immediate_repeat <= 0 or any(value <= 0 for value in warm):
        raise ValueError("nonpositive lifecycle duration")
    warm_median = statistics.median(warm)
    actual_proofs = first + immediate_repeat + sum(warm)
    return {
        "schema": "s31-mixed-cost-lifecycle-accounting-v1",
        "measurement": "sum of separately measured process durations; excludes idle gaps between invocations",
        "proof_count": len(trials),
        "scored_warm_proof_count": len(warm),
        "build_wall_ns": build,
        "first_post_build_verified_wall_ns": first,
        "same_claim_immediate_repeat_wall_ns": immediate_repeat,
        "warm_20_median_verified_wall_ns": warm_median,
        "all_proofs_process_wall_sum_ns": actual_proofs,
        "build_plus_all_proofs_process_wall_sum_ns": build + actual_proofs,
        "observed_amortized_wall_per_proof_ns": (build + actual_proofs) / len(trials),
        "build_fraction_of_measured_lifecycle": build / (build + actual_proofs),
        "build_to_warm_median_ratio": build / warm_median,
        "first_to_warm_median_ratio": first / warm_median,
        "immediate_repeat_to_warm_median_ratio": immediate_repeat / warm_median,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    raw = args.result.read_bytes()
    result = f.v18.v2.parse(raw)
    if raw != f.canonical(result):
        raise ValueError("result is not canonical JSON")
    print(json.dumps(summarize(result), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
