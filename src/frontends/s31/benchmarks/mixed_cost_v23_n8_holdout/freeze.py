#!/usr/bin/env python3
"""Freeze a quiet-host five-branch, eight-chip-call cost challenge."""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import statistics
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(HERE.parent / "mixed_cost_v18_topology_transfer"))
import protocol as v18  # noqa: E402

LANGUAGE = ROOT / "design/s31/measurements/language"
FROZEN = LANGUAGE / "mixed-cost-v23-n8-holdout-protocol.json"
SOURCE = LANGUAGE / "mixed-cost-v23-n8-holdout-source.json"
NAME = "calls8_log13_b5"
ROUNDS = (4096, 128, 1024, 256, 2048, 64, 512, 32)
OPS, BRANCHES, MUL_EVERY = 5120, 5, 5
CLAIMS, SEED, SCHEDULE_SEED = 20, 202610122301, 202610122302
P = 2**31 - 1
BASE_COMMIT = "06c8b94cc68312b5d657a9a62215878bf6054baf"
TOOLS = ("freeze.py", "study.py", "lifecycle.py", "audit.py", "test_preflight.py")


def canonical(value: object) -> bytes:
    return v18.canonical(value)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


@lru_cache(maxsize=1)
def source() -> bytes:
    template = v18.v2.parse(v18.v2.source("control", 2, v18.v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    nodes = []
    shifts, states = [], []
    for branch in range(BRANCHES):
        shifted, feeder = f"shift{branch}", f"seed{branch}"
        nodes.append({"name": shifted, "op": "add_const", "lhs": input_name,
                      "constant": 911 + branch * 37})
        nodes.append({"name": feeder, "op": "mul_const", "lhs": shifted,
                      "constant": 83 + branch * 7})
        shifts.append(shifted)
        states.append(feeder)
    for index in range(OPS // BRANCHES):
        for branch in range(BRANCHES):
            next_name = f"b{branch}_{index}"
            nodes.append({"name": next_name,
                          "op": "mul" if (index + branch) % MUL_EVERY == 0 else "add",
                          "lhs": states[branch], "rhs": shifts[branch]})
            states[branch] = next_name
    nodes.append({"name": "join01", "op": "add", "lhs": states[0], "rhs": states[1]})
    nodes.append({"name": "join23", "op": "add", "lhs": states[2], "rhs": states[3]})
    nodes.append({"name": "join0123", "op": "add", "lhs": "join01", "rhs": "join23"})
    nodes.append({"name": "join_all", "op": "add", "lhs": "join0123", "rhs": states[4]})
    previous = "join_all"
    for call_id, rounds in enumerate(ROUNDS):
        repeated = f"r{call_id}"
        nodes.append({"name": repeated, "op": "repeat", "lhs": previous,
                      "rounds": rounds,
                      "body": [{"op": "square"},
                               {"op": "add_const", "constant": 503 + call_id * 13}]})
        previous = repeated
    nodes.append({"name": "scaled_result", "op": "mul_const", "lhs": previous,
                  "constant": 61})
    nodes.append({"name": output_name, "op": "add", "lhs": "scaled_result",
                  "rhs": shifts[0]})
    relation = {**template, "name": f"mixed_cost_v23_n8_holdout_{NAME}",
                "nodes": nodes}
    v18.v2.flat(relation)
    return canonical(relation)


def output(words: list[int]) -> list[int]:
    shifts = [[(word + 911 + branch * 37) % P for word in words]
              for branch in range(BRANCHES)]
    states = [[(word * (83 + branch * 7)) % P for word in shifts[branch]]
              for branch in range(BRANCHES)]
    for index in range(OPS // BRANCHES):
        for branch in range(BRANCHES):
            states[branch] = [((a * b) if (index + branch) % MUL_EVERY == 0
                               else (a + b)) % P
                              for a, b in zip(states[branch], shifts[branch], strict=True)]
    value = [sum(lanes) % P for lanes in zip(*states, strict=True)]
    for call_id, rounds in enumerate(ROUNDS):
        for _ in range(rounds):
            value = [(word * word + 503 + call_id * 13) % P for word in value]
    return [((word * 61) + shift) % P
            for word, shift in zip(value, shifts[0], strict=True)]


def case(index: int) -> tuple[bytes, bytes, bytes]:
    if not 0 <= index <= CLAIMS:
        raise ValueError("claim outside frozen roster")
    raw = source()
    relation = v18.v2.parse(raw)
    seed = SEED + index * 103
    words = [(seed * (lane + 67) + lane * lane + 97) % P for lane in range(4)]
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output(words)}}
    if v18.v2.evaluate_relation(v18.v2.flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent source arithmetic oracle differs")
    statement = v18.v2.statement_from_assignment(relation, assignment)
    v18.v2.changed_result(raw, statement)
    return raw, canonical(assignment), statement


def prediction() -> dict:
    model_raw = v18.MODEL.read_bytes()
    model = v18.v2.parse(model_raw)
    if model_raw != canonical(v18.cost_model.derive()):
        raise ValueError("V18 model evidence differs")
    base = model["baseline_by_circuit_log"]["13"]
    step = model["extra_call_step"]
    values = {key: base[key] + 4 * step[key] for key in base}
    pow_prediction = model["pow_predictive"]
    center = values["nonpow_wall_ns"]
    proof = values["proof_bytes"]
    width = model["proof_relative_half_width"]
    return {
        "nonpow_whole_process_center_ns": center,
        "native_package_phase_center_ns": {key: values[key] for key in v18.cost_model.PHASES},
        "warm_wall_one_draw_quantile_ns": {
            q: center + value for q, value in pow_prediction["one_draw_wall_noise_quantile_ns"].items()},
        "warm_wall_sample20_median_quantile_ns": {
            q: center + pow_prediction["one_draw_wall_noise_quantile_ns"]["0.5"] +
               model["sample20_median_band_scale"] *
               (value - pow_prediction["one_draw_wall_noise_quantile_ns"]["0.5"])
            for q, value in pow_prediction["sample20_median_wall_noise_quantile_ns"].items()},
        "fri_pow_one_draw_quantile_ns": pow_prediction["one_draw_fri_pow_quantile_ns"],
        "fri_pow_sample20_median_quantile_ns": pow_prediction["sample20_median_fri_pow_quantile_ns"],
        "interaction_pow_one_draw_quantile_ns": pow_prediction["one_draw_interaction_pow_quantile_ns"],
        "interaction_pow_sample20_median_quantile_ns": pow_prediction["sample20_median_interaction_pow_quantile_ns"],
        "proof_bytes_center": proof,
        "proof_bytes_interval": [proof * (1 - width), proof * (1 + width)],
        "prover_peak_rss_median_bytes": values["prover_rss_bytes"],
        "verifier_peak_rss_median_bytes": values["verifier_rss_bytes"],
    }


def expected() -> dict:
    raw = source()
    calls = v18.source_calls(raw)
    slots = v18.slot_layout(13, list(ROUNDS))
    logs = [13] + [value for rounds in ROUNDS for value in (rounds.bit_length() - 1, 4)]
    return {"source_sha256": sha(raw), "call_count": len(ROUNDS),
            "expected_calls": calls,
            "expected_geometry": {
                "slots": len(slots), "constraints": 11 + 19 * len(ROUNDS),
                "tree_columns": [8, 12 + 17 * len(ROUNDS), 8 + 28 * len(ROUNDS), 8],
                "slot_trace_logs": logs,
                "slot_constraints": [11] + [v for _ in ROUNDS for v in (6, 13)],
                "slot_layout": slots, "max_column_log_size": 13,
                "composition_log_size": 13},
            "prediction": prediction()}


def lifecycle_forecast(warm_center: float) -> dict:
    paths = [LANGUAGE / f"mixed-cost-v{v}-{suffix}-result.json"
             for v, suffix in ((18, "topology-transfer"), (19, "revision-holdout"),
                               (20, "build-cold-holdout"))]
    raw = [path.read_bytes() for path in paths]
    prior = [v18.v2.parse(value) for value in raw]
    records = prior[0]["records"] + [prior[1]["record"], prior[2]["record"]]
    if len(records) != 5 or any(len(record["trials"]) != 22 for record in records):
        raise ValueError("prior lifecycle roster differs")
    build = statistics.median(record["build_wall_ns"] for record in records)
    first = statistics.median(record["trials"][0]["first_verified_process_wall_ns"] for record in records)
    repeat = statistics.median(record["trials"][1]["first_verified_process_wall_ns"] for record in records)
    return {"prior_result_sha256": {str(v): sha(value) for v, value in zip((18, 19, 20), raw, strict=True)},
            "fit": "componentwise median of five prior V18-V20 one-host lifecycle observations; no target observations",
            "build_wall_ns": build, "first_post_build_verified_wall_ns": first,
            "same_claim_immediate_repeat_wall_ns": repeat,
            "warm_verified_wall_ns": warm_center,
            "build_plus_22_verified_proofs_sum_ns": build + first + repeat + CLAIMS * warm_center}


def prepare(*, historical: dict | None = None) -> dict:
    rows = [case(index) for index in range(CLAIMS + 1)]
    assignments = [sha(row[1]) for row in rows]
    statements = [sha(row[2]) for row in rows]
    if len(set(assignments + statements)) != 2 * (CLAIMS + 1):
        raise ValueError("claim collision")
    old_sources, old_claims = v18.previous_claims_and_sources()
    old = v18.v2.parse(v18.PROTOCOL.read_bytes())
    old_sources.update(entry["source_sha256"] for entry in old["source_roster"].values())
    for entry in old["source_roster"].values():
        old_claims.update(entry["assignment_sha256"])
        old_claims.update(entry["statement_sha256"])
    for version, suffix in ((19, "revision-holdout"), (20, "build-cold-holdout"),
                            (21, "unseen-topology"), (22, "quiet-holdout")):
        prior = v18.v2.parse((LANGUAGE / f"mixed-cost-v{version}-{suffix}-protocol.json").read_bytes())
        old_sources.add(prior["source_sha256"])
        old_claims.update(prior["assignment_sha256"])
        old_claims.update(prior["statement_sha256"])
    if sha(source()) in old_sources or set(assignments + statements) & old_claims:
        raise ValueError("source or claim already measured")
    names = list(range(1, CLAIMS + 1))
    random.Random(SCHEDULE_SEED).shuffle(names)
    if historical is None:
        pins = v18.v3.pins()
        revision = BASE_COMMIT
        current_pin_sha256 = {path: sha((ROOT / path).read_bytes()) for path in v18.PIN_PATHS}
    else:
        pins = {key: historical[key] for key in ("engine_gitlink_commit", "compiler_sha256", "host")}
        revision = historical["current_revision"]
        current_pin_sha256 = {path: sha(v18.v2.git("show", f"{revision}:{path}"))
                              for path in v18.PIN_PATHS}
    return {"schema": "s31-mixed-cost-v23-n8-holdout-protocol",
            "status": "pre-native-frozen", "source": NAME,
            "source_sha256": sha(source()),
            "v18_model_sha256": sha(v18.MODEL.read_bytes()),
            "v18_protocol_sha256": sha(v18.PROTOCOL.read_bytes()),
            "expected": expected(),
            "lifecycle_forecast": lifecycle_forecast(expected()["prediction"]["warm_wall_one_draw_quantile_ns"]["0.5"]),
            "engine_gitlink_commit": pins["engine_gitlink_commit"],
            "compiler_sha256": pins["compiler_sha256"], "host": pins["host"],
            "current_revision": revision, "current_pin_sha256": current_pin_sha256,
            "tool_sha256": {name: sha((HERE / name).read_bytes()) for name in TOOLS},
            "claim_seed": SEED, "schedule_seed": SCHEDULE_SEED,
            "claim_order": names, "assignment_sha256": assignments,
            "statement_sha256": statements,
            "gates": {
                "manifest_exact_geometry_and_calls": True,
                "all_honest_accepted_and_changed_result_rejected": True,
                "wall_median_relative_error_max": 0.35,
                "nonpow_wall_median_relative_error_max": 0.20,
                "proof_median_relative_error_max": 0.10,
                "wall_one_draw_hits_min": 14,
                "proof_interval_hits_min": 16,
                "sample20_wall_median_in_band": True,
                "rss_and_native_stage_relative_error_max": 0.30,
                "build_wall_relative_error_max": 0.25,
                "first_post_build_verified_relative_error_max": 0.40,
                "immediate_repeat_relative_error_max": 0.50,
                "build_plus_22_proofs_relative_error_max": 0.25},
            "forecast_rule": "V18 model: V17 log13 N4 baseline plus four frozen average-call steps for N8; five-branch one-in-five arithmetic transferred without refit; V18-V20 five-record median lifecycle",
            "one_attempt_semantics": "two ps snapshots one second apart must show no Lean/lake/Zig process or other non-runner process at 25% CPU or above; preflight failure consumes no attempt; bind snapshot bytes/hash and runner PID into O_EXCL marker before native build; preserve failure and do not rerun"}


def frozen_record() -> tuple[dict, str]:
    raw = FROZEN.read_bytes()
    value = v18.v2.parse(raw)
    if (raw != canonical(value) or value != prepare(historical=value) or
            SOURCE.read_bytes() != source()):
        raise ValueError("V23 protocol or source differs from frozen record")
    for path in (FROZEN, SOURCE):
        if v18.v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != path.read_bytes():
            raise ValueError("V23 protocol/source must be committed unchanged")
    return value, sha(raw)


def frozen() -> tuple[dict, str]:
    value, digest = frozen_record()
    current = v18.v3.pins()
    if ({key: current[key] for key in ("engine_gitlink_commit", "compiler_sha256", "host")} !=
            {key: value[key] for key in ("engine_gitlink_commit", "compiler_sha256", "host")} or
            {path: sha((ROOT / path).read_bytes()) for path in v18.PIN_PATHS} !=
            value["current_pin_sha256"]):
        raise ValueError("current S31 stack differs from V23 pre-native freeze")
    return value, digest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check", "check-record"))
    action = parser.parse_args().action
    if action == "check-record":
        value, digest = frozen_record()
    else:
        value = prepare()
        digest = sha(canonical(value))
    if action == "freeze":
        with SOURCE.open("xb") as file:
            file.write(source())
        with FROZEN.open("xb") as file:
            file.write(canonical(value))
    if action == "check":
        frozen()
    print(json.dumps({"protocol_sha256": digest, "source_sha256": value["source_sha256"],
                      "current_revision": value["current_revision"]}, indent=2))


if __name__ == "__main__":
    main()
