#!/usr/bin/env python3
"""V17 prospective mixed-length N4/N8 chip-call transfer model."""

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
    "v15_protocol": LANGUAGE / "mixed-cost-v15-operator-mix-protocol.json",
    "v15_result": LANGUAGE / "mixed-cost-v15-operator-mix-result.json",
    "v15_score": LANGUAGE / "mixed-cost-v15-operator-mix-score.json",
    "v16_protocol": LANGUAGE / "mixed-cost-v16-fanout-protocol.json",
    "v16_result": LANGUAGE / "mixed-cost-v16-fanout-result.json",
    "v16_score": LANGUAGE / "mixed-cost-v16-fanout-score.json",
    "v12_model": LANGUAGE / "mixed-cost-v12-decomposed-model.json",
}
FROZEN = LANGUAGE / "mixed-cost-v17-mixed-calls-model.json"
PHASES = ("topology_compile_ns", "witness_compile_ns", "profile_rebuild_ns",
          "semantic_evaluation_ns")
SPECS = {
    "calls4_log13": {"ops": 4096, "rounds": (4096, 1024, 256, 64), "mul_every": 5},
    "calls8_log13": {"ops": 4096, "rounds": (4096, 2048, 1024, 512, 256, 128, 64, 32), "mul_every": 5},
    "calls4_log14": {"ops": 8192, "rounds": (4096, 1024, 256, 64), "mul_every": 5},
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
    for version in (11, 12, 13, 14, 15, 16):
        protocol = data[f"v{version}_protocol"]
        result = data[f"v{version}_result"]
        score = data[f"v{version}_score"]
        if (result["protocol_sha256"] != sha(raw[f"v{version}_protocol"]) or
                score["result_sha256"] != sha(raw[f"v{version}_result"]) or
                score["all_gates_pass"] is not (version in (12, 13, 14, 16)) or
                result["verified_proofs"] != {11: 88, 12: 88, 13: 66, 14: 66, 15: 66, 16: 66}[version] or
                result["verified_proofs"] != result["changed_claim_proof_rejections"]):
            raise ValueError(f"V{version} declared training identity/control/status differs")
    if (data["v12_protocol"]["v12_model_sha256"] != sha(raw["v12_model"]) or
            set(data["v16_protocol"]["source_roster"]) !=
            {"fanout16_log13_n1", "fanout16_log13_n2", "fanout16_log14_n1"} or
            any(row["proof_interval_coverage"] != 1.0
                for row in data["v16_score"]["sources"].values())):
        raise ValueError("V12 model or V16 local pass evidence differs")
    v13_n1 = metrics(selected(data["v13_result"], data["v13_protocol"], "fork_joint_n1"))
    v13_n4 = metrics(selected(data["v13_result"], data["v13_protocol"], "fork_joint_n4"))
    v16_n1 = metrics(selected(data["v16_result"], data["v16_protocol"], "fanout16_log13_n1"))
    v16_n2 = metrics(selected(data["v16_result"], data["v16_protocol"], "fanout16_log13_n2"))
    v16_log14 = metrics(selected(data["v16_result"], data["v16_protocol"], "fanout16_log14_n1"))
    # An added component cannot have negative algorithmic work. Small negative
    # measured deltas are noise, so the frozen rule uses their positive part.
    short_step = {key: max(0.0, (v13_n4[key] - v13_n1[key]) / 3) for key in v16_n1}
    long_step = {key: max(0.0, v16_n2[key] - v16_n1[key]) for key in v16_n1}
    width = data["v16_protocol"]["source_roster"]["fanout16_log13_n1"][
        "prediction"]["proof_bytes_interval"][1] / data["v16_protocol"][
            "source_roster"]["fanout16_log13_n1"]["prediction"]["proof_bytes_center"] - 1
    if not 0.09 <= width <= 0.15 or short_step["proof_bytes"] <= 0 or long_step["proof_bytes"] <= 0:
        raise ValueError("V16 proof interval or measured chip-call steps invalid")
    return {
        "schema": "s31-mixed-cost-v17-mixed-calls-model",
        "status": "unvalidated-mixed-length-n4-n8-chip-call-transfer",
        "input_sha256": {key: sha(value) for key, value in raw.items()},
        "evidence_classification": "V11/V15 failed and V12/V13/V14/V16 passed are declared training; V17 sources/claims/timings unseen",
        "baseline_by_circuit_log": {"13": v16_n1, "14": v16_log14},
        "short_call_step": short_step,
        "short_call_source": "positive part of V13 fork_joint_n4 minus fork_joint_n1 scored median divided by three extra short calls (32,16,64 rounds)",
        "long_call_step": long_step,
        "long_call_source": "positive part of V16 fanout16_log13_n2 minus fanout16_log13_n1 scored median for one extra 4096-round call",
        "call_round_interpolation": "for each extra call, alpha=clamp((log2(rounds)-6)/6,0,1); step=(1-alpha)*positive V13 short-call step + alpha*positive V16 long-call step for every metric",
        "topology_hypothesis": "V16 16-branch baseline transfers to one-fifth multiplication mix; each extra chip call adds a length-interpolated component cost; mixed N4/N8 geometry has no additional cross-call premium",
        "proof_relative_half_width": width,
        "proof_interval_rule": "retain V16 pre-native-calibrated 9.846% relative half-width for all V17 source centers; proof median and 16/20 coverage gates remain separate",
        "pow_predictive": data["v12_model"]["pow_predictive"],
        "build_cold_prediction_status": "no defensible gate: one-shot package builds and claim0 observations confounded by compiler cache, source size and cold process state; report separately",
    }


def prediction(model: dict, name: str) -> dict:
    if name not in SPECS:
        raise ValueError("outside frozen V17 source roster")
    spec = SPECS[name]
    log = str(spec["ops"].bit_length())
    base = model["baseline_by_circuit_log"][log]
    values = dict(base)
    for rounds in spec["rounds"][1:]:
        alpha = min(1.0, max(0.0, (rounds.bit_length() - 1 - 6) / 6))
        values = {key: values[key] + (1 - alpha) * model["short_call_step"][key] +
                  alpha * model["long_call_step"][key] for key in base}
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
            raise ValueError("V17 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V17 model differs from declared V11–V14 evidence")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SPECS}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
