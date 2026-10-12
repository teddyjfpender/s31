#!/usr/bin/env python3
"""Frozen V13 challenge rule; reuses V12 predictions without refitting them."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LANGUAGE = ROOT / "design/s31/measurements/language"
V12_MODEL = LANGUAGE / "mixed-cost-v12-decomposed-model.json"
V12_PROTOCOL = LANGUAGE / "mixed-cost-v12-decomposed-protocol.json"
V12_RESULT = LANGUAGE / "mixed-cost-v12-decomposed-result.json"
V12_SCORE = LANGUAGE / "mixed-cost-v12-decomposed-score.json"
FROZEN = LANGUAGE / "mixed-cost-v13-topology-calls-model.json"
NAMES = ("fork_joint_n1", "fork_joint_n3", "fork_joint_n4")
CALL_COUNTS = {"fork_joint_n1": 1, "fork_joint_n3": 3, "fork_joint_n4": 4}


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def derive() -> dict:
    raw = {"v12_model": V12_MODEL.read_bytes(),
           "v12_protocol": V12_PROTOCOL.read_bytes(),
           "v12_result_excluded": V12_RESULT.read_bytes(),
           "v12_score_excluded": V12_SCORE.read_bytes()}
    base = json.loads(raw["v12_protocol"])
    result = json.loads(raw["v12_result_excluded"])
    score = json.loads(raw["v12_score_excluded"])
    if (base["schema"] != "s31-mixed-cost-v12-decomposed-protocol" or
            base["v12_model_sha256"] != sha(raw["v12_model"]) or
            result["schema"] != "s31-mixed-cost-v12-decomposed-result" or
            result["protocol_sha256"] != sha(raw["v12_protocol"]) or
            score["schema"] != "s31-mixed-cost-v12-decomposed-score" or
            score["result_sha256"] != sha(raw["v12_result_excluded"]) or
            score["all_gates_pass"] is not True):
        raise ValueError("V12 frozen identity or declared excluded score differs")
    predictions = {name: row["prediction"] for name, row in base["source_roster"].items()}
    chip = predictions["chip_spiral_n1"]
    serial = predictions["serial_spiral_n2"]
    joint = predictions["joint_cascade_n1"]
    wall_per_extra_call = max(0.0, serial["nonpow_whole_process_center_ns"] -
                              chip["nonpow_whole_process_center_ns"])
    proof_per_extra_call = max(0.0, serial["proof_bytes_center"] -
                               chip["proof_bytes_center"])
    prover_rss_per_extra_call = max(0.0, serial["prover_peak_rss_median_bytes"] -
                                    chip["prover_peak_rss_median_bytes"])
    verifier_rss_per_extra_call = max(0.0, serial["verifier_peak_rss_median_bytes"] -
                                      chip["verifier_peak_rss_median_bytes"])
    width = (joint["proof_bytes_interval"][1] - joint["proof_bytes_center"]) / joint[
        "proof_bytes_center"]
    rule = {
        "schema": "s31-mixed-cost-v13-topology-calls-model",
        "status": "unvalidated-topology-and-call-count-falsification",
        "input_sha256": {name: sha(value) for name, value in raw.items()},
        "V12_result_and_score_training_status": "excluded; hashes and pass classification checked only; no observed V12 measurement enters V13 prediction",
        "base_prediction_source": "frozen V12 joint_cascade_n1 prediction for each forked source; V12 predictor itself unchanged",
        "topology_premium_ns": 0,
        "topology_hypothesis": "two live 1024-mul branches joining once cost the same as one live 2048-mul chain at identical trace log and chip calls",
        "extra_call_rule": "for N calls, add (N-1) times the positive part of frozen V12 serial_spiral_n2 minus chip_spiral_n1 prediction to non-PoW wall, proof bytes, prover RSS, verifier RSS; interaction and FRI PoW predictions unchanged",
        "wall_per_extra_call_ns": wall_per_extra_call,
        "proof_bytes_per_extra_call": proof_per_extra_call,
        "prover_rss_bytes_per_extra_call": prover_rss_per_extra_call,
        "verifier_rss_bytes_per_extra_call": verifier_rss_per_extra_call,
        "proof_relative_half_width": width,
        "v12_joint_prediction": joint,
    }
    if proof_per_extra_call <= 0 or width <= 0 or width >= 0.2:
        raise ValueError("unusable frozen call/proof transfer rule")
    return rule


def prediction(rule: dict, name: str) -> dict:
    if name not in CALL_COUNTS:
        raise ValueError("source outside V13 frozen roster")
    extra = CALL_COUNTS[name] - 1
    result = json.loads(canonical(rule["v12_joint_prediction"]))
    wall_shift = extra * rule["wall_per_extra_call_ns"]
    result["nonpow_whole_process_center_ns"] += wall_shift
    for field in ("warm_wall_one_draw_quantile_ns",
                  "warm_wall_sample20_median_quantile_ns"):
        result[field] = {key: value + wall_shift for key, value in result[field].items()}
    result["proof_bytes_center"] += extra * rule["proof_bytes_per_extra_call"]
    center = result["proof_bytes_center"]
    width = rule["proof_relative_half_width"]
    result["proof_bytes_interval"] = [center * (1 - width), center * (1 + width)]
    result["prover_peak_rss_median_bytes"] += extra * rule[
        "prover_rss_bytes_per_extra_call"]
    result["verifier_peak_rss_median_bytes"] += extra * rule[
        "verifier_rss_bytes_per_extra_call"]
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = canonical(derive())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("V13 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V13 rule differs from unchanged V12 predictor")
    rule = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(rule, name) for name in NAMES}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
