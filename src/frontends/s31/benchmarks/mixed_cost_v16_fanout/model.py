#!/usr/bin/env python3
"""V16 prospective proof recalibration and 16-way/log14 structural challenge."""

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
    "v12_model": LANGUAGE / "mixed-cost-v12-decomposed-model.json",
}
FROZEN = LANGUAGE / "mixed-cost-v16-fanout-model.json"
PHASES = ("topology_compile_ns", "witness_compile_ns", "profile_rebuild_ns",
          "semantic_evaluation_ns")
SPECS = {
    "fanout16_log13_n1": {"ops": 4096, "rounds": (4096,), "mul_every": 3, "extra_calls": 0, "extra_scale": 0},
    "fanout16_log13_n2": {"ops": 4096, "rounds": (4096, 4096), "mul_every": 3, "extra_calls": 1, "extra_scale": 0},
    "fanout16_log14_n1": {"ops": 8192, "rounds": (4096,), "mul_every": 3, "extra_calls": 0, "extra_scale": 1},
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
    for version in (11, 12, 13, 14, 15):
        protocol = data[f"v{version}_protocol"]
        result = data[f"v{version}_result"]
        score = data[f"v{version}_score"]
        if (result["protocol_sha256"] != sha(raw[f"v{version}_protocol"]) or
                score["result_sha256"] != sha(raw[f"v{version}_result"]) or
                score["all_gates_pass"] is not (version in (12, 13, 14)) or
                result["verified_proofs"] != {11: 88, 12: 88, 13: 66, 14: 66, 15: 66}[version] or
                result["verified_proofs"] != result["changed_claim_proof_rejections"]):
            raise ValueError(f"V{version} declared training identity/control/status differs")
    if (data["v12_protocol"]["v12_model_sha256"] != sha(raw["v12_model"]) or
            set(data["v15_score"]["sources"]) !=
            {"wide_addheavy_n1", "wide_mix_n1", "wide_mix_n2"} or
            any([key for key, value in row["gates"].items() if not value] !=
                ["proof_interval_coverage"]
                for row in data["v15_score"]["sources"].values())):
        raise ValueError("V12 model or V15 failed proof-only gate differs")
    v13_base = metrics(selected(data["v13_result"], data["v13_protocol"], "fork_joint_n1"))
    v15_mix_rows = selected(data["v15_result"], data["v15_protocol"], "wide_mix_n1")
    v15_add_rows = selected(data["v15_result"], data["v15_protocol"], "wide_addheavy_n1")
    v15_n2_rows = selected(data["v15_result"], data["v15_protocol"], "wide_mix_n2")
    v15_mix = metrics(v15_mix_rows)
    v15_add = metrics(v15_add_rows)
    v15_n2 = metrics(v15_n2_rows)
    base = {key: (v15_mix[key] + v15_add[key]) / 2 for key in v15_mix}
    call_step = {key: v15_n2[key] - v15_mix[key] for key in base}
    # One additional circuit log doubles 4096 to 8192 live nodes. Native
    # process/phase/RSS work extrapolates per operation, proof per log step.
    scale_step = {key: max(0.0, base[key] - v13_base[key]) *
                  (1 if key == "proof_bytes" else 2) for key in base}
    previous_width = data["v12_model"]["proof_relative_half_width"]
    v15_relative_misses = [abs(data["v15_protocol"]["source_roster"][name]
                                 ["prediction"]["proof_bytes_center"] - value["proof_bytes"]) /
                           value["proof_bytes"]
                           for name, value in (("wide_mix_n1", v15_mix),
                                               ("wide_addheavy_n1", v15_add),
                                               ("wide_mix_n2", v15_n2))]
    v15_relative_spreads = [max(abs(row["proof_bytes"] - center["proof_bytes"])
                                for row in rows) / center["proof_bytes"]
                            for rows, center in ((v15_mix_rows, v15_mix),
                                                 (v15_add_rows, v15_add),
                                                 (v15_n2_rows, v15_n2))]
    proof_width = max(previous_width, 1.25 * max(v15_relative_misses),
                      1.5 * max(v15_relative_spreads))
    if not 0 < proof_width <= 0.15 or scale_step["proof_bytes"] <= 0:
        raise ValueError("V16 proof calibration exceeds predeclared 15% cap")
    return {
        "schema": "s31-mixed-cost-v16-fanout-model",
        "status": "unvalidated-16-way-fanout-and-log14-transfer",
        "input_sha256": {key: sha(value) for key, value in raw.items()},
        "evidence_classification": "V11 and V15 failed, V12–V14 passed; all declared training; V16 native source/claim/timing unseen",
        "base_source": "mean of V15 wide_mix_n1 and wide_addheavy_n1 scored medians; both log13/4096 live nodes",
        "base_metrics": base,
        "extra_call_step": call_step,
        "extra_call_source": "V15 wide_mix_n2 minus wide_mix_n1 scored median, same 4096-node circuit",
        "extra_scale_step": scale_step,
        "extra_scale_source": "V15 N1 mean minus V13 fork_joint_n1 medians; double increment for non-PoW/phase/RSS to extrapolate +4096 live operations, single increment for proof bytes to extrapolate one circuit log",
        "topology_hypothesis": "16-way branch/join and one-third multiplication share costs with eight-way V15 at matched log13; log14 process/phase/RSS scale per live operation while proof scales per log step",
        "proof_interval_rule": "max(V12 relative half-width, 1.25 times worst V15 proof-center relative miss, 1.5 times worst V15 within-source absolute proof spread relative to median), capped at 15%",
        "proof_relative_half_width": proof_width,
        "previous_v12_proof_relative_half_width": previous_width,
        "v15_proof_relative_misses": v15_relative_misses,
        "v15_proof_relative_spreads": v15_relative_spreads,
        "pow_predictive": data["v12_model"]["pow_predictive"],
        "build_cold_prediction_status": "no defensible gate: one-shot package builds and claim0 observations confounded by source size, compiler cache and cold process state; report separately",
    }


def prediction(model: dict, name: str) -> dict:
    if name not in SPECS:
        raise ValueError("outside frozen V16 source roster")
    spec = SPECS[name]
    values = {key: model["base_metrics"][key] +
              spec["extra_calls"] * model["extra_call_step"][key] +
              spec["extra_scale"] * model["extra_scale_step"][key]
              for key in model["base_metrics"]}
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
            raise ValueError("V16 model already frozen")
        FROZEN.write_bytes(raw)
    if args.action == "check" and FROZEN.read_bytes() != raw:
        raise ValueError("V16 model differs from declared V11–V14 evidence")
    model = json.loads(raw)
    print(json.dumps({"model_sha256": sha(raw),
                      "predictions": {name: prediction(model, name) for name in SPECS}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
