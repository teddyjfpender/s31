#!/usr/bin/env python3
"""Post-hoc simulation under the unchanged v4 model; never changes v5 score."""

from __future__ import annotations

import json
import math
import random
import statistics

import protocol as p

SEED = 202610116
REPLICATIONS = 100_000


def simulate() -> dict:
    model = p.v2.parse(p.MODEL.read_bytes())
    score = p.v2.parse((p.LANGUAGE / "mixed-cost-v5-transfer-score.json").read_bytes())
    rng = random.Random(SEED)
    outcomes = {}
    for name, count in p.NAMES.items():
        observed = score["sources"][name]["observed_warm_wall_median_ns"]
        predicted = score["sources"][name]["predicted_warm_wall_median_ns"]
        base = model["base_intercept_ns"] + count * model["base_slope_ns_per_call"]
        residuals = model["calibration_nonpow_residuals_ns"]
        fri = model["fri_exponential_scale_ns"]
        interaction = model["interaction_exponential_scale_ns"]
        at_or_below = below_gate = above_gate = 0
        for _ in range(REPLICATIONS):
            sample = sorted(base + rng.choice(residuals) +
                            rng.expovariate(1 / fri) +
                            rng.expovariate(1 / interaction)
                            for _ in range(p.CLAIMS))
            median = statistics.median(sample)
            at_or_below += median <= observed
            below_gate += median < predicted / (1 + p.GATES[
                "wall_median_relative_error_per_source_max"])
            above_gate += median > predicted / (1 - p.GATES[
                "wall_median_relative_error_per_source_max"])
        outcomes[name] = {
            "observed_median_ns": observed,
            "model_fri_median_ns": fri * math.log(2),
            "model_nonpow_center_ns": base + statistics.median(residuals),
            "simulated_probability_median_at_or_below_observed":
                at_or_below / REPLICATIONS,
            "simulated_probability_below_gate": below_gate / REPLICATIONS,
            "simulated_probability_above_gate": above_gate / REPLICATIONS,
            "simulated_probability_either_gate_miss":
                (below_gate + above_gate) / REPLICATIONS,
        }
    return {"schema": "s31-mixed-cost-v5-posthoc-sampling-diagnostic",
            "v4_model_sha256": p.sha(p.MODEL.read_bytes()),
            "v5_score_sha256": p.sha((p.LANGUAGE /
                                     "mixed-cost-v5-transfer-score.json").read_bytes()),
            "seed": SEED, "replications": REPLICATIONS,
            "iid_model_draws_per_replication": p.CLAIMS,
            "sources": outcomes}


if __name__ == "__main__":
    print(json.dumps(simulate(), sort_keys=True, indent=2))
