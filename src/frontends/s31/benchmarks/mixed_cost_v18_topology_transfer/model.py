#!/usr/bin/env python3
"""V18 prospective call-count and branch-topology transfer model."""

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
    "v17_protocol": LANGUAGE / "mixed-cost-v17-mixed-calls-protocol.json",
    "v17_result": LANGUAGE / "mixed-cost-v17-mixed-calls-result.json",
    "v17_score": LANGUAGE / "mixed-cost-v17-mixed-calls-score.json",
    "v12_model": LANGUAGE / "mixed-cost-v12-decomposed-model.json",
}
FROZEN = LANGUAGE / "mixed-cost-v18-topology-transfer-model.json"
PHASES = ("topology_compile_ns", "witness_compile_ns", "profile_rebuild_ns",
          "semantic_evaluation_ns")
SPECS = {
    "calls6_log13_b8": {"ops": 4096, "branches": 8, "rounds": (4096, 1024, 256, 64, 2048, 512), "mul_every": 3},
    "calls6_log14_b8": {"ops": 8192, "branches": 8, "rounds": (4096, 1024, 256, 64, 2048, 512), "mul_every": 3},
    "calls7_log14_b32": {"ops": 8192, "branches": 32, "rounds": (4096, 1024, 256, 64, 2048, 512, 128), "mul_every": 7},
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
    for version in (11, 12, 13, 14, 15, 16, 17):
        protocol = data[f"v{version}_protocol"]
        result = data[f"v{version}_result"]
        score = data[f"v{version}_score"]
        if (result["protocol_sha256"] != sha(raw[f"v{version}_protocol"]) or
                score["result_sha256"] != sha(raw[f"v{version}_result"]) or
                score["all_gates_pass"] is not (version in (12, 13, 14, 16)) or
                result["verified_proofs"] != {11: 88, 12: 88, 13: 66, 14: 66, 15: 66, 16: 66, 17: 66}[version] or
                result["verified_proofs"] != result["changed_claim_proof_rejections"]):
            raise ValueError(f"V{version} declared training identity/control/status differs")
    if (data["v12_protocol"]["v12_model_sha256"] != sha(raw["v12_model"]) or
            set(data["v16_protocol"]["source_roster"]) !=
            {"fanout16_log13_n1", "fanout16_log13_n2", "fanout16_log14_n1"} or
            any(row["proof_interval_coverage"] != 1.0
                for row in data["v16_score"]["sources"].values())):
        raise ValueError("V12 model or V16 local pass evidence differs")
    v17_n4 = metrics(selected(data["v17_result"], data["v17_protocol"], "calls4_log13"))
    v17_n8 = metrics(selected(data["v17_result"], data["v17_protocol"], "calls8_log13"))
    v17_log14 = metrics(selected(data["v17_result"], data["v17_protocol"], "calls4_log14"))
    # N4 and N8 share the same log-13 circuit source family. Use their observed
    # four-call difference, with negative work deltas clamped explicitly.
    extra_call_step = {key: max(0.0, (v17_n8[key] - v17_n4[key]) / 4)
                       for key in v17_n4}
    width = data["v16_protocol"]["source_roster"]["fanout16_log13_n1"][
        "prediction"]["proof_bytes_interval"][1] / data["v16_protocol"][
            "source_roster"]["fanout16_log13_n1"]["prediction"]["proof_bytes_center"] - 1
    if (not 0.09 <= width <= 0.15 or extra_call_step["proof_bytes"] <= 0 or
            data["v17_score"]["sources"]["calls8_log13"]["gates"]["wall_median_error"] is not False):
        raise ValueError("V16 proof interval or declared V17 failed call training differs")
    return {
        "schema": "s31-mixed-cost-v18-topology-transfer-model",
        "status": "unvalidated-n6-n7-branch-topology-and-call-count-transfer",
        "input_sha256": {key: sha(value) for key, value in raw.items()},
        "evidence_classification": "V11/V15/V17 failed and V12/V13/V14/V16 passed are declared training; V18 sources/claims/timings unseen",
        "baseline_by_circuit_log": {"13": v17_n4, "14": v17_log14},
        "extra_call_step": extra_call_step,
        "extra_call_source": "positive part of V17 calls8_log13 minus calls4_log13 scored non-PoW/proof/RSS/native-stage medians divided by four extra calls",
        "call_count_rule": "for N6/N7 use V17 matched log-size N4 baseline plus (N-4) times the frozen per-call step; round mix differs, so this is a falsifiable average-call approximation",
        "topology_hypothesis": "V17 16-branch baselines transfer to new eight- and 32-branch one-third/one-seventh multiplication circuits; log-13 per-call step transfers to log14",
        "proof_relative_half_width": width,
        "proof_interval_rule": "retain V16 pre-native-calibrated 9.846% relative half-width; V17 passed all proof bands, but no V18 retuning",
        "pow_predictive": data["v12_model"]["pow_predictive"],
        "sample20_median_band_scale": 1.5,
        "sample20_median_band_rule": "expand V12 sample-20 PoW median deviations from p50 by 1.5, declared after V17 N8 fell below its frozen band; retain V12 one-draw distribution unchanged",
        "build_cold_prediction_status": "no defensible gate: one-shot package builds and claim0 observations confounded by compiler cache, source size and cold process state; report separately",
    }


def prediction(model: dict, name: str) -> dict:
    if name not in SPECS:
        raise ValueError("outside frozen V18 source roster")
    spec = SPECS[name]
    log = str(spec["ops"].bit_length())
    base = model["baseline_by_circuit_log"][log]
    values = {key: base[key] + (len(spec["rounds"]) - 4) *
              model["extra_call_step"][key] for key in base}
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
            q: center + pow_prediction["one_draw_wall_noise_quantile_ns"]["0.5"] +
               model["sample20_median_band_scale"] *
               (v - pow_prediction["one_draw_wall_noise_quantile_ns"]["0.5"])
            for q, v in pow_prediction["sample20_median_wall_noise_quantile_ns"].items()},
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
            raise ValueError("V18 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V18 model differs from declared V11–V17 evidence")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SPECS}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
