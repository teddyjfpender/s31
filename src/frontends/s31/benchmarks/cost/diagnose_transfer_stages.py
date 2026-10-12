#!/usr/bin/env python3
"""Describe V6 stage residuals in the saved same-host transfer corpora.

Run replay_transfer_v1.py first to authenticate the local saved artifacts.
This script only diagnoses a failed transfer; it never fits or changes V6.
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

S31_DIR = Path(__file__).resolve().parents[2]
ROOT = S31_DIR.parents[2]
sys.path.insert(0, str(S31_DIR / "benchmarks"))

from stage_aware_predictor_v1 import estimate, stage_value

MODEL = ROOT / "design/s31/measurements/language/whole-prover-cost-v6-audit.json"
STAGES = (
    "native_verify_process_wall_seconds",
    "prover_process_unattributed_seconds",
    "runtime_fri_pow_seconds",
    "runtime_interaction_pow_seconds",
    "runtime_prove_seconds_when_pow_opaque",
)


def analyze(corpus: dict, model: dict) -> dict:
    rows = []
    for name, case in sorted(corpus["cases"].items()):
        policy = model["families"][case["family"]]
        residuals = {}
        for stage in STAGES:
            specification = policy["wall_stages"].get(stage)
            if specification is None:
                continue
            feature = case["features"][specification["feature"]]
            predicted = estimate(specification["fit"], feature)
            observed = statistics.mean(stage_value(trial, stage)
                                       for trial in case["trials"])
            residuals[stage] = {"predicted_seconds": predicted,
                                "observed_seconds": observed,
                                "observed_minus_predicted_seconds": observed - predicted}
        rows.append({"program": name, "family": case["family"],
                     "trial_count": len(case["trials"]), "stages": residuals})
    summary = {}
    for stage in STAGES:
        values = [row["stages"][stage]["observed_minus_predicted_seconds"]
                  for row in rows if stage in row["stages"]]
        if values:
            summary[stage] = {"programs": len(values),
                              "minimum_seconds": min(values),
                              "median_seconds": statistics.median(values),
                              "maximum_seconds": max(values)}
    return {"schema": "s31-v6-transfer-stage-diagnostic-v1",
            "corpus_schema": corpus["schema"], "programs": rows,
            "stage_residual_summary": summary,
            "interpretation": "Descriptive residuals only; do not fit V6 to these observations."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", type=Path)
    args = parser.parse_args()
    model = json.loads(MODEL.read_text())["model"]
    corpus = json.loads(args.corpus.read_text())
    if corpus.get("schema") != "s31-whole-prover-v6-transfer-corpus-v1":
        raise ValueError("expected a V6 transfer corpus")
    print(json.dumps(analyze(corpus, model), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
