"""Frozen V10-coefficient extrapolation to one *unseen* trace-log step.

This is a falsification target, not a calibrated model at log 11 or two calls.
V10 scored holdouts and the paired-lowering study are never fit inputs.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
INPUT = LANGUAGE / "mixed-cost-v10-geometry-model.json"
FROZEN = LANGUAGE / "mixed-cost-v11-unseen-model.json"

_spec = importlib.util.spec_from_file_location(
    "s31_v10_for_v11", HERE.parent / "mixed_cost_v10_geometry_model/model.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("V10 model code unavailable")
v10 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(v10)
canonical = v10.canonical
sha = v10.sha


def fit() -> dict:
    raw = INPUT.read_bytes()
    prior = json.loads(raw)
    if raw != v10.canonical(v10.fit()) or prior["schema"] != "s31-mixed-cost-v10-geometry-model":
        raise ValueError("V10 clean fit or frozen model changed")
    return {
        "schema": "s31-mixed-cost-v11-unseen-extrapolation",
        "status": "unvalidated-falsification-target",
        "v10_fit_sha256": v10.sha(raw),
        "training_artifacts": list(v10.INPUTS),
        "excluded_from_training": ["mixed-cost-v10-geometry-transfer-result.json",
                                   "paired-mixed-vs-direct-v1-result.json"],
        "allowed_log_pairs_and_calls": [[1, 11, 4], [1, 9, 11],
                                        [1, 11, 11], [2, 9, 11]],
        "extrapolation": "V4 call intercept+slope; each max log beyond 9 adds the V9-fitted first-step max-log contrast; each circuit log beyond 9 adds the V9-fitted circuit contrast; wall non-PoW adds the same fitted per-axis shifts; V10 PoW/residual mixture and proof width are unchanged",
        "fit": prior,
    }


def prediction(model: dict, calls: int, logs: tuple[int, int]) -> dict:
    if [calls, *logs] not in model["allowed_log_pairs_and_calls"]:
        raise ValueError("outside prespecified unseen geometry")
    fit = model["fit"]
    max_step = max(logs) - 9
    circuit_step = logs[0] - 9
    center = (fit["proof_intercept_bytes"] + fit["proof_slope_bytes_per_call"] * calls +
              fit["proof_max_log_jump_bytes"] * max_step +
              fit["proof_circuit_log_jump_bytes"] * circuit_step)
    # The first chip contrast is the entire 4->10 jump. Reusing that
    # contrast once more for 10->11 is a deliberately brittle extrapolation.
    shift = (fit["nonpow_circuit_log_jump_ns"] * circuit_step +
             fit["nonpow_chip_log_jump_ns"] * max(0, logs[1] - 9))
    wall_model = {**fit, "base_intercept_ns": fit["base_intercept_ns"] + shift}
    scales = fit["fri_source_exponential_scales_ns"]
    width = fit["proof_relative_half_width"]
    return {"warm_wall_quantile_ns": {str(q): v10.v8.wall_quantile(wall_model, calls, q)
                                      for q in (0.05, 0.5, 0.95)},
            "source_rate_p50_envelope_ns":
                [v10.v8.wall_quantile(wall_model, calls, 0.5, [min(scales)]),
                 v10.v8.wall_quantile(wall_model, calls, 0.5, [max(scales)])],
            "proof_bytes_center": center,
            "proof_bytes_interval": [center * (1 - width), center * (1 + width)]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = v10.canonical(fit())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("frozen V11 extrapolation differs")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": v10.sha(raw), "predictions": {
        f"{n}/{c}/{h}": prediction(model, n, (c, h))
        for n, c, h in model["allowed_log_pairs_and_calls"]}}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
