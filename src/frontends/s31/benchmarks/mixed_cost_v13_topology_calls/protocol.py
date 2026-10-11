#!/usr/bin/env python3
"""Native-free V13 log-12 source, claim, prediction, and randomized schedule freeze."""

from __future__ import annotations

import argparse
import json
import random
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
import model as cost_model  # noqa: E402
sys.path.insert(0, str(HERE.parent / "mixed_cost_v4"))
import prospective as v4  # noqa: E402

v2, v3 = v4.v3.v2, v4.v3
LANGUAGE = ROOT / "design/s31/measurements/language"
MODEL = LANGUAGE / "mixed-cost-v13-topology-calls-model.json"
PROTOCOL = LANGUAGE / "mixed-cost-v13-topology-calls-protocol.json"
SOURCE_DIR = LANGUAGE / "mixed-cost-v13-topology-calls-sources"
PREVIOUS_PROTOCOLS = (
    LANGUAGE / "mixed-cost-v4-protocol.json",
    LANGUAGE / "mixed-cost-v5-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v6-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v7-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v8-calibrated-protocol.json",
    LANGUAGE / "mixed-cost-v9-geometry-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v10-geometry-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v11-unseen-protocol.json",
    LANGUAGE / "mixed-cost-v12-decomposed-protocol.json",
)
PROBES = LANGUAGE / "mixed-cost-v9-feasibility"
SOURCES = {
    "fork_joint_n1": {"gates": 2048, "rounds": (4096,)},
    "fork_joint_n3": {"gates": 2048, "rounds": (4096, 32, 16)},
    "fork_joint_n4": {"gates": 2048, "rounds": (4096, 32, 16, 64)},
}
NAMES = tuple(SOURCES)
CLAIMS = 20
P = 2**31 - 1
CLAIM_SEED = 202610122311
SCHEDULE_SEED = 202610122313
SOURCE_BASE_COMMIT = "7e90b5833eecb893c6db5f260e5d1cfc69cd230f"
GATES = {
    "wall_median_relative_error_per_source_max": 0.30,
    "wall_one_draw_90_coverage_per_source_min": 0.70,
    "wall_one_draw_90_coverage_pooled_min": 49 / 60,
    "wall_sample20_median_90_band_source_count_min": 2,
    "proof_median_relative_error_per_source_max": 0.10,
    "proof_90_interval_coverage_per_source_min": 0.80,
    "prover_rss_median_relative_error_per_source_max": 0.30,
    "verifier_rss_median_relative_error_per_source_max": 0.30,
}
PIN_PATHS = (
    "src/frontends/s31/build.zig",
    "src/frontends/s31/language/canonical.zig",
    "src/frontends/s31/language/relation.zig",
    "src/frontends/s31/language/relation_compiler.zig",
    "src/frontends/s31/language/bounded_call_admission.zig",
    "src/frontends/s31/language/record_abi.zig",
    "src/frontends/s31/runtime/bounded_compiled_binding.zig",
    "src/frontends/s31/entry/bounded_compiled_binding.zig",
    "src/frontends/s31/runtime/mixed_boundary/inspection.zig",
    "src/frontends/s31/runtime/mixed_boundary/lookup_budget.zig",
    "src/frontends/s31/runtime/mixed_boundary/registry_manifest.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_package.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_manifest_main.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig",
    "src/frontends/s31/python/abi/binding_v2.py",
    "src/frontends/s31/python/oracle.py",
    "src/frontends/s31/tests/acceptance/mixed_boundary/registry_manifest_digest.py",
    "src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/study.py",
    "src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/audit.py",
    "src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/test_static.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/protocol.py",
)


def canonical(value: object) -> bytes:
    return v2.canonical(value)


def sha(raw: bytes) -> str:
    return v2.sha(raw)


def schedule() -> list[dict]:
    rng = random.Random(SCHEDULE_SEED)
    indices = list(range(1, CLAIMS + 1))
    rng.shuffle(indices)
    result = []
    for index in indices:
        names = list(NAMES)
        rng.shuffle(names)
        result.extend({"name": name, "claim_index": index} for name in names)
    if len(result) != CLAIMS * len(NAMES) or len({(row["name"], row["claim_index"])
                                                   for row in result}) != len(result):
        raise ValueError("scored schedule is incomplete")
    return result


@lru_cache(maxsize=None)
def source(name: str) -> bytes:
    if name not in SOURCES:
        raise ValueError("outside V13 source roster")
    template = v2.parse(v2.source("control", 2, v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    family = NAMES.index(name)
    spec = SOURCES[name]
    nodes: list[dict] = [
        {"name": "shifted_left", "op": "add_const", "lhs": input_name,
         "constant": 401 + family * 23},
        {"name": "shifted_right", "op": "mul_const", "lhs": input_name,
         "constant": 17 + family * 2},
        {"name": "feeder_left", "op": "mul_const", "lhs": "shifted_left",
         "constant": 43 + family * 2},
        {"name": "feeder_right", "op": "add_const", "lhs": "shifted_right",
         "constant": 59 + family * 3},
    ]
    left, right = "feeder_left", "feeder_right"
    for index in range(spec["gates"] // 2):
        left_name, right_name = f"left{index}", f"right{index}"
        nodes.append({"name": left_name, "op": "mul", "lhs": left,
                      "rhs": left if index % 7 == 0 else "shifted_left"})
        nodes.append({"name": right_name, "op": "mul", "lhs": right,
                      "rhs": right if index % 11 == 0 else "shifted_right"})
        left, right = left_name, right_name
        if index % 127 == 126:
            left_offset, right_offset = f"left_offset{index}", f"right_offset{index}"
            nodes.append({"name": left_offset, "op": "add_const", "lhs": left,
                          "constant": 307 + family * 29 + index})
            nodes.append({"name": right_offset, "op": "add_const", "lhs": right,
                          "constant": 503 + family * 31 + index})
            left, right = left_offset, right_offset
    nodes.append({"name": "joined", "op": "add", "lhs": left, "rhs": right})
    previous = "joined"
    for call_id, rounds in enumerate(spec["rounds"]):
        repeated = f"r{call_id}"
        nodes.append({"name": repeated, "op": "repeat", "lhs": previous,
                      "rounds": rounds,
                      "body": [{"op": "square"},
                               {"op": "add_const", "constant": 257 + family * 31 + call_id}]})
        previous = repeated
    nodes.append({"name": "scaled_result", "op": "mul_const", "lhs": previous,
                  "constant": 41 + family * 2})
    nodes.append({"name": output_name, "op": "add", "lhs": "scaled_result",
                  "rhs": "shifted_left"})
    relation = {**template, "name": f"mixed_cost_v13_topology_calls_{name}",
                "nodes": nodes}
    v2.flat(relation)
    return canonical(relation)


def output(name: str, words: list[int]) -> list[int]:
    if name not in SOURCES or len(words) != 4:
        raise ValueError("invalid V13 source/words")
    family = NAMES.index(name)
    spec = SOURCES[name]
    shifted_left = [(word + 401 + family * 23) % P for word in words]
    shifted_right = [(word * (17 + family * 2)) % P for word in words]
    left = [(word * (43 + family * 2)) % P for word in shifted_left]
    right = [(word + 59 + family * 3) % P for word in shifted_right]
    for index in range(spec["gates"] // 2):
        left_rhs = left if index % 7 == 0 else shifted_left
        right_rhs = right if index % 11 == 0 else shifted_right
        left = [(a * b) % P for a, b in zip(left, left_rhs, strict=True)]
        right = [(a * b) % P for a, b in zip(right, right_rhs, strict=True)]
        if index % 127 == 126:
            left = [(word + 307 + family * 29 + index) % P for word in left]
            right = [(word + 503 + family * 31 + index) % P for word in right]
    previous = [(a + b) % P for a, b in zip(left, right, strict=True)]
    for call_id, rounds in enumerate(spec["rounds"]):
        for _ in range(rounds):
            previous = [(word * word + 257 + family * 31 + call_id) % P
                        for word in previous]
    previous = [(word * (41 + family * 2)) % P for word in previous]
    return [(a + b) % P for a, b in zip(previous, shifted_left, strict=True)]


def case(name: str, index: int) -> tuple[bytes, bytes, bytes]:
    if name not in SOURCES or not 0 <= index <= CLAIMS:
        raise ValueError("outside V13 source/claim roster")
    raw_source = source(name)
    relation = v2.parse(raw_source)
    family = NAMES.index(name)
    seed = CLAIM_SEED + family * 10_000_000 + index * 97
    words = [(seed * (lane + 43) + lane * lane + 61) % P for lane in range(4)]
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output(name, words)}}
    if (v2.evaluate_relation(v2.flat(relation), assignment) !=
            assignment["public_outputs"]):
        raise ValueError("independent arithmetic oracle differs from source")
    statement = v2.statement_from_assignment(relation, assignment)
    v2.changed_result(raw_source, statement)
    return raw_source, canonical(assignment), statement


def previous_claims_and_sources() -> tuple[set[str], set[str]]:
    sources = {sha((PROBES / f"{name}.s31.json").read_bytes())
               for name in ("gates256", "rounds1024")}
    claims: set[str] = set()
    for path in PREVIOUS_PROTOCOLS:
        value = v2.parse(path.read_bytes())
        roster = ([entry for group in value["split"].values() for entry in group.values()]
                  if "split" in value else list(value["source_roster"].values()))
        for entry in roster:
            sources.add(entry["source_sha256"])
            claims.update(entry["assignment_sha256"])
            claims.update(entry["statement_sha256"])
    return sources, claims


def prepare_value() -> dict:
    if any(v2.git("show", f"{SOURCE_BASE_COMMIT}:{path}") != (ROOT / path).read_bytes()
           for path in PIN_PATHS if path.endswith((".zig", ".zon"))):
        raise ValueError("production Zig bytes differ from isolated V13 source base commit")
    current_pins = v3.pins()
    v12 = v2.parse(cost_model.V12_PROTOCOL.read_bytes())
    if (current_pins["host"] != v12["host"] or
            current_pins["compiler_sha256"] != v12["compiler_sha256"] or
            current_pins["engine_gitlink_commit"] != v12["engine_gitlink_commit"]):
        raise ValueError("V13 host/compiler/engine differs from frozen V12 validation")
    model_raw = MODEL.read_bytes()
    model = v2.parse(model_raw)
    if (model["schema"] != "s31-mixed-cost-v13-topology-calls-model" or
            model_raw != cost_model.canonical(cost_model.derive())):
        raise ValueError("V13 rule differs from unchanged V12 predictions")
    previous_sources, previous_claims = previous_claims_and_sources()
    roster = {}
    new_sources: set[str] = set()
    new_claims: set[str] = set()
    for name, spec in SOURCES.items():
        rows = [case(name, index) for index in range(CLAIMS + 1)]
        digest = sha(rows[0][0])
        assignments = [sha(row[1]) for row in rows]
        statements = [sha(row[2]) for row in rows]
        all_claims = set(assignments + statements)
        if (digest in previous_sources | new_sources or
                len(all_claims) != 2 * (CLAIMS + 1) or
                all_claims & (previous_claims | new_claims) or
                any(row[0] != rows[0][0] for row in rows)):
            raise ValueError("V13 source or claim collides with prior evidence")
        new_sources.add(digest)
        new_claims.update(all_claims)
        count = len(spec["rounds"])
        slot_logs = [12 if spec["gates"] else 9] + [entry for rounds in spec["rounds"]
                                                     for entry in (rounds.bit_length() - 1, 4)]
        roster[name] = {
            "source_sha256": digest, "call_count": count,
            "chip_rounds": list(spec["rounds"]), "live_mul_nodes": spec["gates"],
            "topology": "two parallel live 1024-mul branches joined by add before chip calls",
            "source_nodes": len(v2.parse(rows[0][0])["nodes"]),
            "expected_geometry": {
                "slots": 1 + 2 * count, "constraints": 11 + 19 * count,
                "tree_columns": [8, 12 + 17 * count, 8 + 28 * count, 8],
                "slot_trace_logs": slot_logs,
                "max_column_log_size": 12, "composition_log_size": 12},
            "assignment_sha256": assignments, "statement_sha256": statements,
            "prediction": cost_model.prediction(model, name),
        }
    if len(new_sources) != 3 or len(new_claims) != 126:
        raise ValueError("V13 fresh source/claim count differs")
    return {
        "schema": "s31-mixed-cost-v13-topology-calls-protocol",
        "status": "pre-native-frozen", "source_roster": roster,
        "v13_model_sha256": sha(model_raw),
        "v12_result_excluded_sha256": model["input_sha256"]["v12_result_excluded"],
        "v12_score_excluded_sha256": model["input_sha256"]["v12_score_excluded"],
        "source_base_commit": SOURCE_BASE_COMMIT,
        "build_mode": "ReleaseFast", "lowering": "direct-mixed-general",
        "claims_per_source": CLAIMS + 1, "scored_claims_per_source": CLAIMS,
        "first_post_build_claim": 0, "claim_zero_immediate_repeat": True,
        "scored_schedule_seed": SCHEDULE_SEED,
        "scored_schedule": schedule(),
        "process_measurement": "fresh prover and external verifier subprocess wall under /usr/bin/time for OS peak RSS; same method as V11 wall fit and V12 validation",
        "reported_phase_measurement": "S31_MIXED_NATIVE_PHASE_V1 interaction and FRI PoW; residual = first verified wall minus both PoW reports",
        "proof_negative_error": "InvalidMixedInteractionNonce",
        "native_builds_before_scored_proofs": "all three packages built and manifested before any claim-0 or scored proof",
        "one_prospective_run_only": True,
        "speedup_claim_enabled": False,
        "model_claim": "unchanged V12 predictor plus frozen V12-prediction-only call rule tested on fork topology and N3/N4; no host-independent reliability claim",
        "gates": GATES,
        "transfer_tool_sha256": {path: sha((ROOT / path).read_bytes()) for path in PIN_PATHS},
        **current_pins,
    }


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    if raw != canonical(value) or value != prepare_value():
        raise ValueError("V13 protocol or pinned stack differs from pre-native freeze")
    for path in (PROTOCOL, MODEL):
        if v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != path.read_bytes():
            raise ValueError(f"V13 frozen file was not committed unchanged: {path}")
    for name in SOURCES:
        path = SOURCE_DIR / f"{name}.json"
        if (path.read_bytes() != source(name) or
                v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != source(name)):
            raise ValueError(f"V13 source was not committed unchanged: {name}")
    return value, sha(raw)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check"))
    args = parser.parse_args()
    if args.action == "check":
        value, digest = frozen()
    else:
        value = prepare_value()
        raw = canonical(value)
        digest = sha(raw)
        if args.action == "freeze":
            if PROTOCOL.exists() or SOURCE_DIR.exists():
                raise ValueError("V13 protocol or sources already frozen")
            SOURCE_DIR.mkdir()
            for name in SOURCES:
                (SOURCE_DIR / f"{name}.json").write_bytes(source(name))
            PROTOCOL.write_bytes(raw)
    print(json.dumps({"protocol_sha256": digest,
                      "source_sha256": {name: row["source_sha256"]
                                        for name, row in value["source_roster"].items()},
                      "predictions": {name: row["prediction"]
                                      for name, row in value["source_roster"].items()}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
