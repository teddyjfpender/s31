"""V12 frozen decomposed whole-prover forecast from V11 same-method rows.

Wall = measured V11 whole-process non-PoW residual + stochastic interaction
PoW + stochastic FRI PoW. Proof bytes and process RSS are separate forecasts.
V11's failed prospective score is a declared fit input, never hidden holdout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
INPUTS = {
    "v10_result_proof_bytes_only": LANGUAGE / "mixed-cost-v10-geometry-transfer-result.json",
    "v10_model_proof_width_only": LANGUAGE / "mixed-cost-v10-geometry-model.json",
    "v11_result_same_wall_method": LANGUAGE / "mixed-cost-v11-unseen-result.json",
    "v11_score_failed_declared_training": LANGUAGE / "mixed-cost-v11-unseen-score.json",
    "v11_protocol": LANGUAGE / "mixed-cost-v11-unseen-protocol.json",
}
FROZEN = LANGUAGE / "mixed-cost-v12-decomposed-model.json"
V11_TO_V10 = {
    "chip_surge_n1": "chip_twirl_n1",
    "gate_surge_n1": "gate_weave_n1",
    "joint_surge_n1": "joint_weave_n1",
}
V11_NAMES = (*V11_TO_V10, "serial_surge_n2")
SHAPES = {
    "circuit_cascade_n1": ("gate_surge_n1", "gate"),
    "chip_spiral_n1": ("chip_surge_n1", "chip"),
    "joint_cascade_n1": ("joint_surge_n1", "joint"),
    "serial_spiral_n2": ("serial_surge_n2", "serial"),
}
SIMULATION_SEED = 202610122121
ONE_DRAW_SAMPLES = 100_000
SAMPLE_MEDIAN_REPLICATES = 10_000
SAMPLE_SIZE = 20


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def quantile(values: list[float], q: float) -> float:
    if not 0 <= q <= 1 or not values:
        raise ValueError("invalid empirical quantile")
    ordered = sorted(values)
    position = (len(ordered) - 1) * q
    low = math.floor(position)
    high = math.ceil(position)
    return ordered[low] + (ordered[high] - ordered[low]) * (position - low)


def quantiles(values: list[float]) -> dict[str, float]:
    return {str(q): quantile(values, q) for q in (0.05, 0.5, 0.95)}


def selected(record: dict, length: int) -> list[dict]:
    rows = [row for row in record["trials"] if 1 <= row["claim_index"] <= length]
    if len(rows) != length or sorted(row["claim_index"] for row in rows) != list(range(1, length + 1)):
        raise ValueError("fit claim roster differs")
    if any(not row["changed_result_rejected_at_interaction_nonce"] or
           row["proof_bytes"] <= 0 for row in rows):
        raise ValueError("fit proof control differs")
    return rows


def simulation(blocks: list[dict], deviations: list[float]) -> dict:
    """Source-level rate mixture with Gamma posterior uncertainty.

    Jeffreys/scale-invariant 1/rate prior for an exponential clock gives
    rate | n durations ~ Gamma(shape=n, scale=1/sum(durations)). For one draw
    choose one observed source block uniformly. For a future 20-claim source,
    choose a block/rate ONCE for the sample, preserving source-level rate
    correlation across its 20 nonce searches. These are modeling assumptions,
    not proof-system or host guarantees.
    """
    rng = random.Random(SIMULATION_SEED)
    interaction_n = sum(row["scored_trials"] for row in blocks)
    interaction_sum = sum(row["interaction_pow_sum_ns"] for row in blocks)
    if interaction_n != 80 or len(deviations) != 80:
        raise ValueError("incomplete V11 PoW/residual fit")

    def rates() -> tuple[float, float]:
        block = blocks[rng.randrange(len(blocks))]
        fri_rate = rng.gammavariate(block["scored_trials"],
                                    1 / block["fri_pow_sum_ns"])
        interaction_rate = rng.gammavariate(interaction_n, 1 / interaction_sum)
        return fri_rate, interaction_rate

    wall_noise: list[float] = []
    fri_values: list[float] = []
    interaction_values: list[float] = []
    for _ in range(ONE_DRAW_SAMPLES):
        fri_rate, interaction_rate = rates()
        fri = rng.expovariate(fri_rate)
        interaction = rng.expovariate(interaction_rate)
        fri_values.append(fri)
        interaction_values.append(interaction)
        wall_noise.append(deviations[rng.randrange(len(deviations))] + fri + interaction)

    median_wall_noise: list[float] = []
    median_fri: list[float] = []
    median_interaction: list[float] = []
    for _ in range(SAMPLE_MEDIAN_REPLICATES):
        fri_rate, interaction_rate = rates()
        fri_rows: list[float] = []
        interaction_rows: list[float] = []
        wall_rows: list[float] = []
        for _ in range(SAMPLE_SIZE):
            fri = rng.expovariate(fri_rate)
            interaction = rng.expovariate(interaction_rate)
            fri_rows.append(fri)
            interaction_rows.append(interaction)
            wall_rows.append(deviations[rng.randrange(len(deviations))] + fri + interaction)
        median_wall_noise.append(statistics.median(wall_rows))
        median_fri.append(statistics.median(fri_rows))
        median_interaction.append(statistics.median(interaction_rows))
    return {
        "seed": SIMULATION_SEED,
        "rng": "Python random.Random Mersenne Twister; gammavariate and expovariate",
        "quantile_rule": "sort; linear interpolation at (n-1)*q",
        "one_draw_samples": ONE_DRAW_SAMPLES,
        "sample_median_replicates": SAMPLE_MEDIAN_REPLICATES,
        "sample_size": SAMPLE_SIZE,
        "source_rate_prior": "improper scale-invariant 1/rate; four V11 source blocks chosen uniformly",
        "one_draw_wall_noise_quantile_ns": quantiles(wall_noise),
        "sample20_median_wall_noise_quantile_ns": quantiles(median_wall_noise),
        "one_draw_fri_pow_quantile_ns": quantiles(fri_values),
        "sample20_median_fri_pow_quantile_ns": quantiles(median_fri),
        "one_draw_interaction_pow_quantile_ns": quantiles(interaction_values),
        "sample20_median_interaction_pow_quantile_ns": quantiles(median_interaction),
    }


def fit() -> dict:
    raw = {name: path.read_bytes() for name, path in INPUTS.items()}
    data = {name: json.loads(value) for name, value in raw.items()}
    v11 = data["v11_result_same_wall_method"]
    v11_score = data["v11_score_failed_declared_training"]
    v11_protocol = data["v11_protocol"]
    v10 = data["v10_result_proof_bytes_only"]
    v10_model = data["v10_model_proof_width_only"]
    if (v11["schema"] != "s31-mixed-cost-v11-unseen-result" or
            v11_score["schema"] != "s31-mixed-cost-v11-unseen-score" or
            v11_score["all_gates_pass"] is not False or
            v11_score["result_sha256"] != sha(raw["v11_result_same_wall_method"]) or
            v11["protocol_sha256"] != sha(raw["v11_protocol"]) or
            v11_protocol["schema"] != "s31-mixed-cost-v11-unseen-protocol" or
            v11["verified_proofs"] != 88 or
            v11["changed_claim_proof_rejections"] != 88 or
            v10["schema"] != "s31-mixed-cost-v10-geometry-transfer-result" or
            v10["verified_proofs"] != 246 or
            v10["changed_claim_proof_rejections"] != 246 or
            v10_model["schema"] != "s31-mixed-cost-v10-geometry-model"):
        raise ValueError("V10/V11 fit identity or proof controls differ")
    v11_records = {row["name"]: row for row in v11["records"]}
    v10_records = {row["name"]: row for row in v10["records"]}
    if set(v11_records) != set(V11_NAMES) or set(v10_records) != set(V11_TO_V10.values()):
        raise ValueError("V10/V11 fit source roster differs")
    blocks = []
    deviations = []
    for name in V11_NAMES:
        record = v11_records[name]
        rows = selected(record, 20)
        logs = [slot["trace_log_size"] for slot in record["native_manifest"]["slots"]]
        expected = {"chip_surge_n1": [9, 11, 4],
                    "gate_surge_n1": [11, 4, 4],
                    "joint_surge_n1": [11, 11, 4],
                    "serial_surge_n2": [9, 11, 4, 4, 4]}[name]
        if logs != expected or record["source_sha256"] != v11_protocol["source_roster"][name]["source_sha256"]:
            raise ValueError("V11 fit geometry/source differs")
        for row in rows:
            phase = row["native_phases_ns"]
            if (phase["fri_pow_ns"] <= 0 or phase["interaction_pow_ns"] <= 0 or
                    row["prover_process_monotonic_ns"]["peak_rss_bytes"] <= 0 or
                    row["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] <= 0):
                raise ValueError("V11 native phase/RSS missing")
        nonpow = [row["first_verified_process_wall_ns"] -
                  row["native_phases_ns"]["fri_pow_ns"] -
                  row["native_phases_ns"]["interaction_pow_ns"] for row in rows]
        center = statistics.median(nonpow)
        deviations.extend(value - center for value in nonpow)
        blocks.append({"name": name, "source_sha256": record["source_sha256"],
                       "call_count": record["call_count"], "slot_trace_logs": logs,
                       "scored_trials": len(rows),
                       "nonpow_whole_process_median_ns": center,
                       "fri_pow_sum_ns": sum(row["native_phases_ns"]["fri_pow_ns"] for row in rows),
                       "interaction_pow_sum_ns": sum(row["native_phases_ns"]["interaction_pow_ns"] for row in rows),
                       "proof_median_bytes": statistics.median(row["proof_bytes"] for row in rows),
                       "prover_rss_median_bytes": statistics.median(
                           row["prover_process_monotonic_ns"]["peak_rss_bytes"] for row in rows),
                       "verifier_rss_median_bytes": statistics.median(
                           row["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] for row in rows)})
    by_name = {block["name"]: block for block in blocks}
    chip = by_name["chip_surge_n1"]
    gate = by_name["gate_surge_n1"]
    joint = by_name["joint_surge_n1"]
    serial = by_name["serial_surge_n2"]
    c_slope = max(0.0, (joint["nonpow_whole_process_median_ns"] -
                        chip["nonpow_whole_process_median_ns"]) / 2)
    h_slope = max(0.0, joint["nonpow_whole_process_median_ns"] -
                  gate["nonpow_whole_process_median_ns"])
    proof_steps = {}
    for name, old_name in V11_TO_V10.items():
        previous = v10_records[old_name]
        old_rows = selected(previous, 80)
        old_log = [slot["trace_log_size"] for slot in previous["native_manifest"]["slots"]]
        expected_old = {"chip_surge_n1": [9, 10, 4],
                        "gate_surge_n1": [10, 4, 4],
                        "joint_surge_n1": [10, 10, 4]}[name]
        if old_log != expected_old:
            raise ValueError("V10 proof-step geometry differs")
        proof_steps[name] = by_name[name]["proof_median_bytes"] - statistics.median(
            row["proof_bytes"] for row in old_rows)
        if proof_steps[name] <= 0:
            raise ValueError("V10->V11 proof increment is not positive")
    def rss_step(role: str) -> dict[str, float]:
        key = f"{role}_rss_median_bytes"
        return {"circuit_per_log": max(0.0, (joint[key] - chip[key]) / 2),
                "chip_extra_log": max(0.0, joint[key] - gate[key])}
    model = {
        "schema": "s31-mixed-cost-v12-decomposed-model",
        "status": "unvalidated-log12-falsification-target",
        "fit_input_sha256": {name: sha(value) for name, value in raw.items()},
        "wall_fit_source": "V11 /usr/bin/time process rows only; V11 score failed 14/16 and is declared training",
        "proof_fit_source": "V10->V11 proof-byte median increments only; timing/RSS from V10 excluded",
        "fit_blocks": blocks,
        "nonpow_whole_process_deviations_ns": deviations,
        "nonpow_circuit_per_log_ns": c_slope,
        "nonpow_extra_chip_log_ns": h_slope,
        "nonpow_extrapolation": "source-shape V11 median plus V11 joint-minus-chip contrast divided by two for one circuit-log step; positive part of joint-minus-gate contrast for one chip-log step; serial remains its V11 two-call anchor",
        "proof_step_bytes_by_shape": proof_steps,
        "proof_relative_half_width": v10_model["proof_relative_half_width"],
        "prover_rss_step_bytes": rss_step("prover"),
        "verifier_rss_step_bytes": rss_step("verifier"),
        "rss_extrapolation": "V11 median plus positive one-log circuit/chip contrasts; descriptive fragile forecast, separate from wall and proof",
        "pow_predictive": simulation(blocks, deviations),
    }
    if not 0 < model["proof_relative_half_width"] < 0.2:
        raise ValueError("proof interval width differs")
    return model


def prediction(model: dict, name: str) -> dict:
    if name not in SHAPES:
        raise ValueError("outside V12 source roster")
    anchor, shape = SHAPES[name]
    block = {row["name"]: row for row in model["fit_blocks"]}[anchor]
    circuit_step = 1 if shape in ("gate", "joint") else 0
    chip_step = 1 if shape in ("chip", "joint", "serial") else 0
    center = (block["nonpow_whole_process_median_ns"] +
              circuit_step * model["nonpow_circuit_per_log_ns"] +
              chip_step * model["nonpow_extra_chip_log_ns"])
    if shape == "serial":
        proof_step = model["proof_step_bytes_by_shape"]["chip_surge_n1"]
    else:
        proof_step = model["proof_step_bytes_by_shape"][anchor]
    proof_center = block["proof_median_bytes"] + proof_step
    width = model["proof_relative_half_width"]
    def rss(role: str) -> float:
        step = model[f"{role}_rss_step_bytes"]
        return (block[f"{role}_rss_median_bytes"] +
                circuit_step * step["circuit_per_log"] +
                chip_step * step["chip_extra_log"])
    pow_prediction = model["pow_predictive"]
    return {
        "nonpow_whole_process_center_ns": center,
        "warm_wall_one_draw_quantile_ns": {
            q: center + value for q, value in pow_prediction[
                "one_draw_wall_noise_quantile_ns"].items()},
        "warm_wall_sample20_median_quantile_ns": {
            q: center + value for q, value in pow_prediction[
                "sample20_median_wall_noise_quantile_ns"].items()},
        "fri_pow_one_draw_quantile_ns": pow_prediction["one_draw_fri_pow_quantile_ns"],
        "fri_pow_sample20_median_quantile_ns": pow_prediction[
            "sample20_median_fri_pow_quantile_ns"],
        "interaction_pow_one_draw_quantile_ns": pow_prediction[
            "one_draw_interaction_pow_quantile_ns"],
        "interaction_pow_sample20_median_quantile_ns": pow_prediction[
            "sample20_median_interaction_pow_quantile_ns"],
        "proof_bytes_center": proof_center,
        "proof_bytes_interval": [proof_center * (1 - width), proof_center * (1 + width)],
        "prover_peak_rss_median_bytes": rss("prover"),
        "verifier_peak_rss_median_bytes": rss("verifier"),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = canonical(fit())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("V12 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V12 model differs from declared V10/V11 fit")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SHAPES}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
