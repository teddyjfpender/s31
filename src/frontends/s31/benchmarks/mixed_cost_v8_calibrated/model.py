"""Native-free V8 fit: source-varying PoW and profile-specific proof widths.

The fit reads only the committed V4 training/calibration, V5 transfer, and V7
transfer artifacts. V6 is an integrity-failed run and is never opened here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
INPUTS = {
    "v4_model": LANGUAGE / "mixed-cost-v4-model.json",
    "v4_train": LANGUAGE / "mixed-cost-v4-train.json",
    "v5_result": LANGUAGE / "mixed-cost-v5-transfer-result.json",
    "v7_result": LANGUAGE / "mixed-cost-v7-transfer-result.json",
}
FROZEN = LANGUAGE / "mixed-cost-v8-calibrated-model.json"
EXPECTED = {"v4_train": {"relay_n3": (3, 39), "relay_n7": (7, 39),
                         "twist_n3": (3, 39), "twist_n7": (7, 39)},
            "v5_result": {"scaled_seed_n1": (1, 20),
                          "weighted_scan_n8": (8, 20)},
            "v7_result": {"affine_seed_n1": (1, 80),
                          "switchback_n8": (8, 80)}}


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def profile(count: int) -> str:
    if count in (1, 3):
        return "small"
    if count in (7, 8):
        return "large"
    raise ValueError("V8 model is calibrated only for 1/3/7/8-call profiles")


def selected(record: dict, group: str, expected: tuple[int, int]) -> list[dict]:
    count, length = expected
    if record["call_count"] != count:
        raise ValueError("training count differs")
    rows = [row for row in record["trials"] if
            (41 <= row["claim_index"] <= 79 if group == "v4_train"
             else 1 <= row["claim_index"] <= length)]
    if len(rows) != length or len({row["claim_index"] for row in rows}) != length:
        raise ValueError("training claim roster differs")
    if any(not row["changed_result_rejected_at_interaction_nonce"] or
           row["native_phases_ns"]["fri_pow_ns"] <= 0 or
           row["proof_bytes"] <= 0 for row in rows):
        raise ValueError("training proof acceptance or metric differs")
    return rows


def fit() -> dict:
    raw = {name: path.read_bytes() for name, path in INPUTS.items()}
    data = {name: json.loads(value) for name, value in raw.items()}
    v4 = data["v4_model"]
    if v4["schema"] != "s31-mixed-cost-v4-distribution-model" or len(
            v4["calibration_nonpow_residuals_ns"]) != 156:
        raise ValueError("wrong frozen V4 model")
    blocks = []
    widths: dict[str, list[float]] = {"small": [], "large": []}
    pow_scales = []
    for group, roster in EXPECTED.items():
        artifact = data[group]
        if (len(artifact["records"]) != len(roster) or
                artifact["verified_proofs" if group != "v4_train"
                         else "native_verified_proofs"] < sum(n for _, n in roster.values())):
            raise ValueError("training artifact or proof count differs")
        seen = set()
        for record in artifact["records"]:
            name = record["name"]
            if name not in roster or name in seen:
                raise ValueError("training source roster differs")
            seen.add(name)
            count, length = roster[name]
            rows = selected(record, group, (count, length))
            center = v4["proof_intercept_bytes"] + v4["proof_slope_bytes_per_call"] * count
            errors = sorted(abs(row["proof_bytes"] / center - 1) for row in rows)
            rank = min(length, math.ceil((length + 1) * 0.95))
            width = errors[rank - 1]
            widths[profile(count)].append(width)
            median_pow = statistics.median(row["native_phases_ns"]["fri_pow_ns"]
                                           for row in rows)
            if group != "v4_train":
                pow_scales.append(median_pow / math.log(2))
            blocks.append({"artifact": group, "name": name, "call_count": count,
                           "source_sha256": record["source_sha256"],
                           "calibration_rows": length,
                           "fri_pow_median_ns": median_pow,
                           "proof_relative_p95_rank_1_based": rank,
                           "proof_relative_p95": width})
        if seen != set(roster):
            raise ValueError("incomplete training source roster")
    if len(pow_scales) != 4 or any(scale <= 0 for scale in pow_scales):
        raise ValueError("wrong recent PoW source roster")
    return {"schema": "s31-mixed-cost-v8-calibrated-model",
            "fit_input_sha256": {name: sha(value) for name, value in raw.items()},
            "fit_blocks": blocks, "fri_source_exponential_scales_ns": pow_scales,
            "fri_source_weight": "equal per V5/V7 source block",
            "interaction_exponential_scale_ns": v4["interaction_exponential_scale_ns"],
            "base_intercept_ns": v4["base_intercept_ns"],
            "base_slope_ns_per_call": v4["base_slope_ns_per_call"],
            "calibration_nonpow_residuals_ns": v4["calibration_nonpow_residuals_ns"],
            "proof_intercept_bytes": v4["proof_intercept_bytes"],
            "proof_slope_bytes_per_call": v4["proof_slope_bytes_per_call"],
            "proof_relative_half_width_by_profile":
                {name: max(values) for name, values in widths.items()},
            "out_of_scope": "No source-independent guarantee from four recent PoW blocks"}


def pow_sum_cdf(value: float, first: float, second: float) -> float:
    if value <= 0:
        return 0.0
    if abs(first - second) <= 1e-10 * max(first, second):
        x = value / first
        return max(0.0, min(1.0, 1 - math.exp(-x) * (1 + x)))
    survivor = (first * math.exp(-value / first) -
                second * math.exp(-value / second)) / (first - second)
    return max(0.0, min(1.0, 1 - survivor))


def wall_cdf(model: dict, count: int, wall_ns: float,
             scales: list[float] | None = None) -> float:
    base = model["base_intercept_ns"] + model["base_slope_ns_per_call"] * count
    scales = scales or model["fri_source_exponential_scales_ns"]
    second = model["interaction_exponential_scale_ns"]
    return statistics.mean(
        pow_sum_cdf(wall_ns - base - residual, first, second)
        for residual in model["calibration_nonpow_residuals_ns"]
        for first in scales)


def wall_quantile(model: dict, count: int, probability: float,
                  scales: list[float] | None = None) -> float:
    if not 0 < probability < 1:
        raise ValueError("probability must be interior")
    scales = scales or model["fri_source_exponential_scales_ns"]
    base = model["base_intercept_ns"] + model["base_slope_ns_per_call"] * count
    low = min(base + x for x in model["calibration_nonpow_residuals_ns"])
    high = max(base + x for x in model["calibration_nonpow_residuals_ns"]) + 20 * (
        max(scales) + model["interaction_exponential_scale_ns"])
    for _ in range(80):
        mid = (low + high) / 2
        if wall_cdf(model, count, mid, scales) < probability:
            low = mid
        else:
            high = mid
    return high


def prediction(model: dict, count: int) -> dict:
    width = model["proof_relative_half_width_by_profile"][profile(count)]
    center = model["proof_intercept_bytes"] + model["proof_slope_bytes_per_call"] * count
    scales = model["fri_source_exponential_scales_ns"]
    return {"warm_wall_quantile_ns": {str(q): wall_quantile(model, count, q)
                                      for q in (0.05, 0.5, 0.95)},
            "source_rate_p50_envelope_ns":
                [wall_quantile(model, count, 0.5, [min(scales)]),
                 wall_quantile(model, count, 0.5, [max(scales)])],
            "proof_bytes_center": center,
            "proof_bytes_interval": [center * (1 - width), center * (1 + width)]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    computed = canonical(fit())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("model already exists")
        FROZEN.write_bytes(computed)
    if args.action == "check" and FROZEN.read_bytes() != computed:
        raise ValueError("frozen V8 model differs from clean inputs or fit code")
    print(json.dumps({"model_sha256": sha(computed),
                      "widths": json.loads(computed)["proof_relative_half_width_by_profile"],
                      "predictions": {str(n): prediction(json.loads(computed), n)
                                      for n in (1, 8)}}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
