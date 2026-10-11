"""Frozen-domain geometry-aware cost fit for one-call mixed proofs.

Uses clean V4/V5/V7/V8/V9 evidence only. V6 has no performance input.
Prediction is restricted to circuit/chip trace logs 9/4, 10/4, 9/10, 10/10.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
FROZEN = LANGUAGE / "mixed-cost-v10-geometry-model.json"
INPUTS = {
    "v4_model": LANGUAGE / "mixed-cost-v4-model.json",
    "v4_train": LANGUAGE / "mixed-cost-v4-train.json",
    "v5_result": LANGUAGE / "mixed-cost-v5-transfer-result.json",
    "v7_result": LANGUAGE / "mixed-cost-v7-transfer-result.json",
    "v8_result": LANGUAGE / "mixed-cost-v8-calibrated-result.json",
    "v9_result": LANGUAGE / "mixed-cost-v9-geometry-transfer-result.json",
}
EXPECTED = {
    "v4_train": {"relay_n3": (3, 39), "relay_n7": (7, 39),
                 "twist_n3": (3, 39), "twist_n7": (7, 39)},
    "v5_result": {"scaled_seed_n1": (1, 20), "weighted_scan_n8": (8, 20)},
    "v7_result": {"affine_seed_n1": (1, 80), "switchback_n8": (8, 80)},
    "v8_result": {"folded_seed_n1": (1, 80), "braided_scan_n8": (8, 80)},
    "v9_result": {"chip_sweep_n1": (1, 80), "gate_ladder_n1": (1, 80),
                  "joint_ladder_n1": (1, 80)},
}

_spec = importlib.util.spec_from_file_location(
    "s31_v8_cost_model_for_v10", HERE.parent / "mixed_cost_v8_calibrated/model.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("frozen V8 distribution helper unavailable")
v8 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(v8)


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def selected(record: dict, group: str, count: int, length: int) -> list[dict]:
    if record["call_count"] != count:
        raise ValueError("training call count differs")
    rows = [row for row in record["trials"] if
            (41 <= row["claim_index"] <= 79 if group == "v4_train"
             else 1 <= row["claim_index"] <= length)]
    if len(rows) != length or len({row["claim_index"] for row in rows}) != length:
        raise ValueError("training claim roster differs")
    if any(not row["changed_result_rejected_at_interaction_nonce"] or
           row["native_phases_ns"]["fri_pow_ns"] <= 0 or
           row["native_phases_ns"]["interaction_pow_ns"] <= 0 or
           row["proof_bytes"] <= 0 for row in rows):
        raise ValueError("training proof or metric differs")
    return rows


def geometry(record: dict) -> tuple[int, int]:
    manifest = record["native_manifest"]
    slots = manifest["slots"]
    if manifest["call_count"] != record["call_count"] or len(slots) != 1 + 2 * record["call_count"]:
        raise ValueError("training manifest roster differs")
    return slots[0]["trace_log_size"], slots[1]["trace_log_size"]


def center_bytes(model: dict, count: int, logs: tuple[int, int]) -> float:
    center = model["proof_intercept_bytes"] + model["proof_slope_bytes_per_call"] * count
    if count == 1:
        if logs not in ((9, 4), (10, 4), (9, 10), (10, 10)):
            raise ValueError("outside measured one-call log-pair domain")
        if max(logs) == 10:
            center += model["proof_max_log_jump_bytes"]
        if logs[0] == 10:
            center += model["proof_circuit_log_jump_bytes"]
    elif logs != (9, 4):
        raise ValueError("larger-call geometry is baseline only")
    return center


def nonpow_ns(rows: list[dict]) -> float:
    return statistics.median(
        row["first_verified_process_wall_ns"] -
        row["native_phases_ns"]["fri_pow_ns"] -
        row["native_phases_ns"]["interaction_pow_ns"] for row in rows)


def fit() -> dict:
    raw = {name: path.read_bytes() for name, path in INPUTS.items()}
    data = {name: json.loads(value) for name, value in raw.items()}
    v4 = data["v4_model"]
    if v4["schema"] != "s31-mixed-cost-v4-distribution-model" or len(
            v4["calibration_nonpow_residuals_ns"]) != 156:
        raise ValueError("wrong V4 baseline")
    blocks = []
    block_rows = {}
    for group, roster in EXPECTED.items():
        artifact = data[group]
        if len(artifact["records"]) != len(roster):
            raise ValueError("training artifact roster differs")
        seen = set()
        for record in artifact["records"]:
            name = record["name"]
            if name not in roster or name in seen:
                raise ValueError("training source differs")
            seen.add(name)
            count, length = roster[name]
            rows = selected(record, group, count, length)
            logs = geometry(record)
            if (group != "v9_result" and logs != (9, 4)) or (
                    group == "v9_result" and logs != {
                        "chip_sweep_n1": (9, 10),
                        "gate_ladder_n1": (10, 4),
                        "joint_ladder_n1": (10, 10)}[name]):
                raise ValueError("training geometry differs")
            block_rows[(group, name)] = rows
            blocks.append({"artifact": group, "name": name,
                           "call_count": count, "calibration_rows": length,
                           "source_sha256": record["source_sha256"],
                           "circuit_trace_log": logs[0], "chip_trace_log": logs[1],
                           "proof_median_bytes": statistics.median(row["proof_bytes"] for row in rows),
                           "nonpow_median_ns": nonpow_ns(rows),
                           "fri_pow_median_ns": statistics.median(
                               row["native_phases_ns"]["fri_pow_ns"] for row in rows)})
        if seen != set(roster):
            raise ValueError("incomplete training roster")
    block = {(row["artifact"], row["name"]): row for row in blocks}
    baseline = v4["proof_intercept_bytes"] + v4["proof_slope_bytes_per_call"]
    chip = block[("v9_result", "chip_sweep_n1")]["proof_median_bytes"]
    gate = block[("v9_result", "gate_ladder_n1")]["proof_median_bytes"]
    joint = block[("v9_result", "joint_ladder_n1")]["proof_median_bytes"]
    # Two-parameter fit: the common max-log jump, then the average of the
    # gate-only and combined contrasts. A fully additive gate+chip model
    # would double-count the global log-10 commitment/FRI cost.
    max_jump = chip - baseline
    gate_jump = statistics.mean((gate, joint)) - chip
    if max_jump <= 0 or gate_jump <= 0:
        raise ValueError("geometry proof-size contrasts differ")
    base_nonpow = block[("v8_result", "folded_seed_n1")]["nonpow_median_ns"]
    c_nonpow = block[("v9_result", "chip_sweep_n1")]["nonpow_median_ns"]
    g_nonpow = block[("v9_result", "gate_ladder_n1")]["nonpow_median_ns"]
    j_nonpow = block[("v9_result", "joint_ladder_n1")]["nonpow_median_ns"]
    gate_shift = ((g_nonpow - base_nonpow) + (j_nonpow - c_nonpow)) / 2
    chip_shift = ((c_nonpow - base_nonpow) + (j_nonpow - g_nonpow)) / 2
    model = {"schema": "s31-mixed-cost-v10-geometry-model",
             "fit_input_sha256": {name: sha(value) for name, value in raw.items()},
             "fit_blocks": blocks,
             "domain_one_call_circuit_chip_trace_logs": [[9, 4], [10, 4], [9, 10], [10, 10]],
             "base_intercept_ns": v4["base_intercept_ns"],
             "base_slope_ns_per_call": v4["base_slope_ns_per_call"],
             "calibration_nonpow_residuals_ns": v4["calibration_nonpow_residuals_ns"],
             "interaction_exponential_scale_ns": v4["interaction_exponential_scale_ns"],
             "fri_source_exponential_scales_ns": [
                 row["fri_pow_median_ns"] / math.log(2) for row in blocks
                 if row["artifact"] in ("v5_result", "v7_result", "v8_result", "v9_result")],
             "fri_source_weight": "equal per nine clean V5/V7/V8/V9 source blocks",
             "proof_intercept_bytes": v4["proof_intercept_bytes"],
             "proof_slope_bytes_per_call": v4["proof_slope_bytes_per_call"],
             "proof_max_log_jump_bytes": max_jump,
             "proof_circuit_log_jump_bytes": gate_jump,
             "nonpow_circuit_log_jump_ns": gate_shift,
             "nonpow_chip_log_jump_ns": chip_shift}
    worst_p95 = 0.0
    for row in blocks:
        rows = block_rows[(row["artifact"], row["name"])]
        ctr = center_bytes(model, row["call_count"],
                           (row["circuit_trace_log"], row["chip_trace_log"]))
        errors = sorted(abs(trial["proof_bytes"] / ctr - 1) for trial in rows)
        rank = min(len(errors), math.ceil((len(errors) + 1) * 0.95))
        row["proof_relative_p95_rank_1_based"] = rank
        row["proof_relative_p95"] = errors[rank - 1]
        worst_p95 = max(worst_p95, errors[rank - 1])
    n1_baseline_medians = [block[(group, name)]["proof_median_bytes"]
                           for group, name in (("v5_result", "scaled_seed_n1"),
                                               ("v7_result", "affine_seed_n1"),
                                               ("v8_result", "folded_seed_n1"))]
    source_bias = max(abs(value / baseline - 1) for value in n1_baseline_medians)
    model["proof_worst_source_p95_relative"] = worst_p95
    model["proof_same_geometry_n1_source_bias_allowance"] = source_bias
    model["proof_relative_half_width"] = worst_p95 + source_bias
    if len(model["fri_source_exponential_scales_ns"]) != 9 or not 0 < model[
            "proof_relative_half_width"] < 1:
        raise ValueError("incomplete geometry fit")
    return model


def prediction(model: dict, logs: tuple[int, int]) -> dict:
    center = center_bytes(model, 1, logs)
    shift = ((model["nonpow_circuit_log_jump_ns"] if logs[0] == 10 else 0) +
             (model["nonpow_chip_log_jump_ns"] if logs[1] == 10 else 0))
    wall_model = {**model, "base_intercept_ns": model["base_intercept_ns"] + shift}
    scales = model["fri_source_exponential_scales_ns"]
    width = model["proof_relative_half_width"]
    return {"warm_wall_quantile_ns": {str(q): v8.wall_quantile(wall_model, 1, q)
                                      for q in (0.05, 0.5, 0.95)},
            "source_rate_p50_envelope_ns":
                [v8.wall_quantile(wall_model, 1, 0.5, [min(scales)]),
                 v8.wall_quantile(wall_model, 1, 0.5, [max(scales)])],
            "proof_bytes_center": center,
            "proof_bytes_interval": [center * (1 - width), center * (1 + width)]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = canonical(fit())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("model already exists")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("frozen V10 model differs from clean fit inputs or code")
    value = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "proof_width": value["proof_relative_half_width"],
                      "predictions": {f"{a}/{b}": prediction(value, (a, b))
                                      for a, b in ((10, 4), (9, 10), (10, 10))}},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
