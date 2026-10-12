#!/usr/bin/env python3
"""Frozen V14 long-call/log13 forecast from declared V11–V13 training rows."""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
INPUTS = {
    "v11_protocol": LANGUAGE / "mixed-cost-v11-unseen-protocol.json",
    "v11_result": LANGUAGE / "mixed-cost-v11-unseen-result.json",
    "v11_failed_score": LANGUAGE / "mixed-cost-v11-unseen-score.json",
    "v12_protocol": LANGUAGE / "mixed-cost-v12-decomposed-protocol.json",
    "v12_model": LANGUAGE / "mixed-cost-v12-decomposed-model.json",
    "v12_result": LANGUAGE / "mixed-cost-v12-decomposed-result.json",
    "v12_passed_score": LANGUAGE / "mixed-cost-v12-decomposed-score.json",
    "v13_protocol": LANGUAGE / "mixed-cost-v13-topology-calls-protocol.json",
    "v13_result": LANGUAGE / "mixed-cost-v13-topology-calls-result.json",
    "v13_passed_score": LANGUAGE / "mixed-cost-v13-topology-calls-score.json",
}
FROZEN = LANGUAGE / "mixed-cost-v14-long-calls-model.json"
SPECS = {
    "long_fork_n2": {"rounds": (4096, 4096), "extra_calls": 1, "chip_log_extra": 0},
    "long_fork_n3": {"rounds": (4096, 4096, 4096), "extra_calls": 2,
                     "chip_log_extra": 0},
    "long_fork_log13_n2": {"rounds": (8192, 4096), "extra_calls": 1,
                           "chip_log_extra": 1},
}


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def selected(result: dict, name: str, protocol: dict) -> list[dict]:
    record = next((r for r in result["records"] if r["name"] == name), None)
    if record is None or record["source_sha256"] != protocol["source_roster"][name]["source_sha256"]:
        raise ValueError(f"declared training source absent or changed: {name}")
    rows = [t for t in record["trials"] if t["claim_index"] > 0]
    if (len(rows) != 20 or sorted(t["claim_index"] for t in rows) != list(range(1, 21)) or
            any(not t["changed_result_rejected_at_interaction_nonce"] for t in rows)):
        raise ValueError(f"declared training controls incomplete: {name}")
    return rows


def metrics(rows: list[dict]) -> dict[str, float]:
    return {
        "nonpow_wall_median_ns": statistics.median(
            t["first_verified_process_wall_ns"] - t["native_phases_ns"]["fri_pow_ns"] -
            t["native_phases_ns"]["interaction_pow_ns"] for t in rows),
        "proof_median_bytes": statistics.median(t["proof_bytes"] for t in rows),
        "prover_rss_median_bytes": statistics.median(
            t["prover_process_monotonic_ns"]["peak_rss_bytes"] for t in rows),
        "verifier_rss_median_bytes": statistics.median(
            t["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] for t in rows),
    }


def derive() -> dict:
    raw = {key: path.read_bytes() for key, path in INPUTS.items()}
    data = {key: json.loads(value) for key, value in raw.items()}
    for version in (11, 12, 13):
        p = data[f"v{version}_protocol"]
        r = data[f"v{version}_result"]
        score_key = {11: "v11_failed_score", 12: "v12_passed_score",
                     13: "v13_passed_score"}[version]
        s = data[score_key]
        if (r["protocol_sha256"] != sha(raw[f"v{version}_protocol"]) or
                s["result_sha256"] != sha(raw[f"v{version}_result"]) or
                s["all_gates_pass"] is not (version != 11) or
                r["verified_proofs"] != r["changed_claim_proof_rejections"] or
                r["verified_proofs"] != {11: 88, 12: 88, 13: 66}[version]):
            raise ValueError(f"V{version} training identity/control/score classification differs")
    if data["v12_protocol"]["v12_model_sha256"] != sha(raw["v12_model"]):
        raise ValueError("V12 PoW/proof model identity differs")
    v11 = metrics(selected(data["v11_result"], "chip_surge_n1", data["v11_protocol"]))
    v12 = metrics(selected(data["v12_result"], "chip_spiral_n1", data["v12_protocol"]))
    n1 = metrics(selected(data["v13_result"], "fork_joint_n1", data["v13_protocol"]))
    n3 = metrics(selected(data["v13_result"], "fork_joint_n3", data["v13_protocol"]))
    n4 = metrics(selected(data["v13_result"], "fork_joint_n4", data["v13_protocol"]))
    keys = tuple(n1)
    short_call_step = {key: max(0.0, statistics.median(((n3[key] - n1[key]) / 2,
                                                          (n4[key] - n1[key]) / 3)))
                       for key in keys}
    log_step = {key: max(0.0, v12[key] - v11[key]) for key in keys}
    # V12's pre-V12 proof-log slope avoids treating a single source-to-source
    # proof-size jump as an exact per-log cost. It was frozen before V12 native.
    v12_model = data["v12_model"]
    log_step["proof_median_bytes"] = v12_model["proof_step_bytes_by_shape"]["joint_surge_n1"]
    width = v12_model["proof_relative_half_width"]
    if not 0 < width < 0.2 or log_step["proof_median_bytes"] <= 0:
        raise ValueError("invalid frozen proof log slope/interval")
    return {
        "schema": "s31-mixed-cost-v14-long-calls-model",
        "status": "unvalidated-multiple-long-call-and-log13-falsification",
        "input_sha256": {key: sha(value) for key, value in raw.items()},
        "evidence_classification": "V11 failed, V12 passed, V13 passed: all declared training; V14 source/claims/native rows unseen",
        "base_source": "V13 fork_joint_n1 scored median non-PoW verified wall, proof size, prover RSS, verifier RSS",
        "base_metrics": n1,
        "short_call_step": short_call_step,
        "log_step": log_step,
        "long_call_hypothesis": "At an already-paid max trace log12, replacing each short extra call by 4096 rounds does not add more non-PoW wall/proof/RSS than V13's short-call step; first-call log12->13 adds one chip-log step",
        "chip_log_wall_and_rss_source": "positive V12 chip_spiral_n1 minus V11 chip_surge_n1 measured non-PoW/RSS medians; different source constants are a confounder",
        "proof_log_source": "V12 pre-native model joint_surge_n1 V10->V11 proof-byte step",
        "proof_relative_half_width": width,
        "pow_predictive": v12_model["pow_predictive"],
        "build_cold_prediction_status": "no defensible gate: one-shot package builds and claim0 observations confounded by compiler cache/process cold start; report separately",
    }


def prediction(rule: dict, name: str) -> dict:
    if name not in SPECS:
        raise ValueError("outside frozen V14 source roster")
    spec = SPECS[name]
    values = {key: rule["base_metrics"][key] +
              spec["extra_calls"] * rule["short_call_step"][key] +
              spec["chip_log_extra"] * rule["log_step"][key]
              for key in rule["base_metrics"]}
    pow_prediction = rule["pow_predictive"]
    center = values["nonpow_wall_median_ns"]
    proof = values["proof_median_bytes"]
    width = rule["proof_relative_half_width"]
    return {
        "nonpow_whole_process_center_ns": center,
        "warm_wall_one_draw_quantile_ns": {
            key: center + value for key, value in pow_prediction[
                "one_draw_wall_noise_quantile_ns"].items()},
        "warm_wall_sample20_median_quantile_ns": {
            key: center + value for key, value in pow_prediction[
                "sample20_median_wall_noise_quantile_ns"].items()},
        "fri_pow_one_draw_quantile_ns": pow_prediction["one_draw_fri_pow_quantile_ns"],
        "fri_pow_sample20_median_quantile_ns": pow_prediction[
            "sample20_median_fri_pow_quantile_ns"],
        "interaction_pow_one_draw_quantile_ns": pow_prediction[
            "one_draw_interaction_pow_quantile_ns"],
        "interaction_pow_sample20_median_quantile_ns": pow_prediction[
            "sample20_median_interaction_pow_quantile_ns"],
        "proof_bytes_center": proof,
        "proof_bytes_interval": [proof * (1 - width), proof * (1 + width)],
        "prover_peak_rss_median_bytes": values["prover_rss_median_bytes"],
        "verifier_peak_rss_median_bytes": values["verifier_rss_median_bytes"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = canonical(derive())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("V14 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V14 model differs from declared training evidence")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SPECS}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
