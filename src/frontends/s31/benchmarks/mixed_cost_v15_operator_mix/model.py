#!/usr/bin/env python3
"""V15 prospective structural phase/proof/RSS model for a wide mixed-op DAG."""

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
    **{f"v{v}_{kind}": LANGUAGE / f"mixed-cost-v{v}-{suffix}-{kind}.json"
       for v, suffix in ((11, "unseen"), (12, "decomposed"),
                         (13, "topology-calls"), (14, "long-calls"))
       for kind in ("protocol", "result")},
    "v11_score": LANGUAGE / "mixed-cost-v11-unseen-score.json",
    "v12_score": LANGUAGE / "mixed-cost-v12-decomposed-score.json",
    "v13_score": LANGUAGE / "mixed-cost-v13-topology-calls-score.json",
    "v14_score": LANGUAGE / "mixed-cost-v14-long-calls-score.json",
    "v12_model": LANGUAGE / "mixed-cost-v12-decomposed-model.json",
}
FROZEN = LANGUAGE / "mixed-cost-v15-operator-mix-model.json"
PHASES = ("topology_compile_ns", "witness_compile_ns", "profile_rebuild_ns",
          "semantic_evaluation_ns")
SPECS = {
    "wide_mix_n1": {"rounds": (4096,), "mul_every": 4, "extra_calls": 0},
    "wide_addheavy_n1": {"rounds": (4096,), "mul_every": 8, "extra_calls": 0},
    "wide_mix_n2": {"rounds": (4096, 4096), "mul_every": 4, "extra_calls": 1},
}


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def selected(result: dict, protocol: dict, name: str) -> list[dict]:
    record = next((r for r in result["records"] if r["name"] == name), None)
    if record is None or record["source_sha256"] != protocol["source_roster"][name]["source_sha256"]:
        raise ValueError(f"training source identity differs: {name}")
    rows = [t for t in record["trials"] if t["claim_index"] > 0]
    if (len(rows) != 20 or sorted(t["claim_index"] for t in rows) != list(range(1, 21)) or
            any(not t["changed_result_rejected_at_interaction_nonce"] for t in rows)):
        raise ValueError(f"training proof controls differ: {name}")
    return rows


def metrics(rows: list[dict]) -> dict[str, float]:
    result = {
        "nonpow_wall_ns": statistics.median(
            t["first_verified_process_wall_ns"] - t["native_phases_ns"]["fri_pow_ns"] -
            t["native_phases_ns"]["interaction_pow_ns"] for t in rows),
        "proof_bytes": statistics.median(t["proof_bytes"] for t in rows),
        "prover_rss_bytes": statistics.median(
            t["prover_process_monotonic_ns"]["peak_rss_bytes"] for t in rows),
        "verifier_rss_bytes": statistics.median(
            t["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] for t in rows),
    }
    result.update({key: statistics.median(t["package_stages_ns"][key] for t in rows)
                   for key in PHASES})
    return result


def derive() -> dict:
    raw = {key: path.read_bytes() for key, path in INPUTS.items()}
    data = {key: json.loads(value) for key, value in raw.items()}
    for version in (11, 12, 13, 14):
        protocol = data[f"v{version}_protocol"]
        result = data[f"v{version}_result"]
        score = data[f"v{version}_score"]
        if (result["protocol_sha256"] != sha(raw[f"v{version}_protocol"]) or
                score["result_sha256"] != sha(raw[f"v{version}_result"]) or
                score["all_gates_pass"] is not (version != 11) or
                result["verified_proofs"] != {11: 88, 12: 88, 13: 66, 14: 66}[version] or
                result["verified_proofs"] != result["changed_claim_proof_rejections"]):
            raise ValueError(f"V{version} declared training identity/control/status differs")
    if data["v12_protocol"]["v12_model_sha256"] != sha(raw["v12_model"]):
        raise ValueError("frozen V12 model identity differs")
    v11 = metrics(selected(data["v11_result"], data["v11_protocol"], "gate_surge_n1"))
    v12 = metrics(selected(data["v12_result"], data["v12_protocol"], "circuit_cascade_n1"))
    base = metrics(selected(data["v13_result"], data["v13_protocol"], "fork_joint_n1"))
    long_n2 = metrics(selected(data["v14_result"], data["v14_protocol"], "long_fork_n2"))
    long_n3 = metrics(selected(data["v14_result"], data["v14_protocol"], "long_fork_n3"))
    # V11 gate_surge: 1024 live mul nodes; V12 circuit_cascade: 2048.
    # Wide V15: 4096 live add/mul nodes, a further 2048 = two steps.
    structural_step = {key: max(0.0, v12[key] - v11[key]) for key in base}
    structural_step["proof_bytes"] = data["v12_model"]["proof_step_bytes_by_shape"]["gate_surge_n1"]
    long_call_step = {key: max(0.0, statistics.median((long_n2[key] - base[key],
                                                       (long_n3[key] - base[key]) / 2)))
                      for key in base}
    width = data["v12_model"]["proof_relative_half_width"]
    if not 0 < width < 0.2 or structural_step["proof_bytes"] <= 0:
        raise ValueError("invalid structural proof step/interval")
    return {
        "schema": "s31-mixed-cost-v15-operator-mix-model",
        "status": "unvalidated-wide-add-mul-operator-mix-falsification",
        "input_sha256": {key: sha(value) for key, value in raw.items()},
        "evidence_classification": "V11 failed and V12–V14 passed are declared training; V15 sources/claims/timings unseen",
        "source_counts": {"v11_gate_mul_nodes": 1024, "v12_circuit_mul_nodes": 2048,
                          "v13_base_mul_nodes": 2048, "v15_mixed_add_mul_nodes": 4096},
        "base_metrics": base,
        "structural_step_per_1024_ops": structural_step,
        "structural_steps_to_v15": 2,
        "structural_hypothesis": "each live packed add or mul node has same marginal phase/non-PoW/RSS cost as a live packed mul; 8-way fanout and 1:3 versus 1:7 mul:add mix carry no extra premium at fixed 4096-node/log13 geometry",
        "structural_step_source": "positive V12 circuit_cascade_n1 minus V11 gate_surge_n1 scored median per +1024 live mul nodes; constants and trace-log changes confounded; proof uses V12 pre-native gate proof-log coefficient",
        "long_call_step": long_call_step,
        "long_call_source": "positive median of V14 long_fork_n2 minus V13 fork_joint_n1 and half V14 long_fork_n3 minus V13 fork_joint_n1 scored medians; source constants differ",
        "proof_relative_half_width": width,
        "pow_predictive": data["v12_model"]["pow_predictive"],
        "build_cold_prediction_status": "no defensible gate: one-shot package builds and claim0 observations confounded by compiler cache and cold process state; report separately",
    }


def prediction(model: dict, name: str) -> dict:
    if name not in SPECS:
        raise ValueError("outside frozen V15 source roster")
    extra = SPECS[name]["extra_calls"]
    values = {key: model["base_metrics"][key] +
              model["structural_steps_to_v15"] * model["structural_step_per_1024_ops"][key] +
              extra * model["long_call_step"][key] for key in model["base_metrics"]}
    pow_prediction = model["pow_predictive"]
    center = values["nonpow_wall_ns"]
    proof = values["proof_bytes"]
    width = model["proof_relative_half_width"]
    return {
        "nonpow_whole_process_center_ns": center,
        "native_package_phase_center_ns": {key: values[key] for key in PHASES},
        "warm_wall_one_draw_quantile_ns": {
            q: center + v for q, v in pow_prediction["one_draw_wall_noise_quantile_ns"].items()},
        "warm_wall_sample20_median_quantile_ns": {
            q: center + v for q, v in pow_prediction[
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
        "prover_peak_rss_median_bytes": values["prover_rss_bytes"],
        "verifier_peak_rss_median_bytes": values["verifier_rss_bytes"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    raw = canonical(derive())
    if args.action == "freeze":
        if FROZEN.exists():
            raise ValueError("V15 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V15 model differs from declared V11–V14 evidence")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SPECS}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
