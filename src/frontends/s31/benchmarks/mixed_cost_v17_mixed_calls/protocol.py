#!/usr/bin/env python3
"""Native-free V17 mixed-length N4/N8 chip-call prediction freeze."""

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
MODEL = LANGUAGE / "mixed-cost-v17-mixed-calls-model.json"
PROTOCOL = LANGUAGE / "mixed-cost-v17-mixed-calls-protocol.json"
SOURCE_DIR = LANGUAGE / "mixed-cost-v17-mixed-calls-sources"
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
    LANGUAGE / "mixed-cost-v13-topology-calls-protocol.json",
    LANGUAGE / "mixed-cost-v14-long-calls-protocol.json",
    LANGUAGE / "mixed-cost-v15-operator-mix-protocol.json",
    LANGUAGE / "mixed-cost-v16-fanout-protocol.json",
)
PROBES = LANGUAGE / "mixed-cost-v9-feasibility"
SOURCES = {
    "calls4_log13": {"ops": 4096, "branches": 16, "mul_every": 5,
                     "rounds": (4096, 1024, 256, 64)},
    "calls8_log13": {"ops": 4096, "branches": 16, "mul_every": 5,
                     "rounds": (4096, 2048, 1024, 512, 256, 128, 64, 32)},
    "calls4_log14": {"ops": 8192, "branches": 16, "mul_every": 5,
                     "rounds": (4096, 1024, 256, 64)},
}
NAMES = tuple(SOURCES)
CLAIMS = 20
P = 2**31 - 1
CLAIM_SEED = 202610130171
SCHEDULE_SEED = 202610130173
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
    "nonpow_wall_median_relative_error_per_source_max": 0.20,
    "native_phase_median_relative_error_per_source_max": 0.30,
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
    "src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/study.py",
    "src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/audit.py",
    "src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/test_static.py",
    "src/frontends/s31/benchmarks/mixed_cost_v14_long_calls/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v14_long_calls/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v16_fanout/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v16_fanout/protocol.py",
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
        raise ValueError("outside V17 source roster")
    template = v2.parse(v2.source("control", 2, v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    family = NAMES.index(name)
    spec = SOURCES[name]
    nodes: list[dict] = []
    shifts, states = [], []
    for branch in range(spec["branches"]):
        shifted, feeder = f"shift{branch}", f"seed{branch}"
        nodes.append({"name": shifted, "op": "add_const", "lhs": input_name,
                      "constant": 401 + family * 37 + branch * 19})
        nodes.append({"name": feeder, "op": "mul_const", "lhs": shifted,
                      "constant": 43 + family * 5 + branch * 2})
        shifts.append(shifted)
        states.append(feeder)
    for index in range(spec["ops"] // spec["branches"]):
        for branch in range(spec["branches"]):
            next_name = f"b{branch}_{index}"
            operation = "mul" if (index + branch) % spec["mul_every"] == 0 else "add"
            nodes.append({"name": next_name, "op": operation,
                          "lhs": states[branch], "rhs": shifts[branch]})
            states[branch] = next_name
    for level in range(spec["branches"].bit_length() - 1):
        next_states = []
        for pair in range(len(states) // 2):
            name_at_level = f"join{level}_{pair}"
            nodes.append({"name": name_at_level, "op": "add",
                          "lhs": states[2 * pair], "rhs": states[2 * pair + 1]})
            next_states.append(name_at_level)
        states = next_states
    previous = states[0]
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
                  "rhs": shifts[0]})
    relation = {**template, "name": f"mixed_cost_v17_mixed_calls_{name}",
                "nodes": nodes}
    v2.flat(relation)
    return canonical(relation)


def output(name: str, words: list[int]) -> list[int]:
    if name not in SOURCES or len(words) != 4:
        raise ValueError("invalid V17 source/words")
    family = NAMES.index(name)
    spec = SOURCES[name]
    shifts = [[(word + 401 + family * 37 + branch * 19) % P for word in words]
              for branch in range(spec["branches"])]
    states = [[(word * (43 + family * 5 + branch * 2)) % P for word in shifts[branch]]
              for branch in range(spec["branches"])]
    for index in range(spec["ops"] // spec["branches"]):
        for branch in range(spec["branches"]):
            if (index + branch) % spec["mul_every"] == 0:
                states[branch] = [(a * b) % P for a, b in zip(
                    states[branch], shifts[branch], strict=True)]
            else:
                states[branch] = [(a + b) % P for a, b in zip(
                    states[branch], shifts[branch], strict=True)]
    for _ in range(spec["branches"].bit_length() - 1):
        states = [[(a + b) % P for a, b in zip(states[2 * pair],
                                               states[2 * pair + 1], strict=True)]
                  for pair in range(len(states) // 2)]
    previous = states[0]
    for call_id, rounds in enumerate(spec["rounds"]):
        for _ in range(rounds):
            previous = [(word * word + 257 + family * 31 + call_id) % P
                        for word in previous]
    previous = [(word * (41 + family * 2)) % P for word in previous]
    return [(a + b) % P for a, b in zip(previous, shifts[0], strict=True)]


def case(name: str, index: int) -> tuple[bytes, bytes, bytes]:
    if name not in SOURCES or not 0 <= index <= CLAIMS:
        raise ValueError("outside V17 source/claim roster")
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


def source_calls(raw_source: bytes) -> list[dict]:
    """Derive semantic native-call identities from the frozen source node order."""
    relation = v2.parse(raw_source)
    node_ids = {item["name"]: index for index, item in
                enumerate(relation["nodes"], start=1)}
    node_ids[relation["inputs"][0]["name"]] = 0
    calls = []
    for node in relation["nodes"]:
        if node["op"] == "repeat":
            calls.append({"call_id": len(calls),
                          "source_node_id": node_ids[node["name"]],
                          "input_node_id": node_ids[node["lhs"]],
                          "rounds": node["rounds"],
                          "constant": node["body"][1]["constant"]})
    return calls


def slot_layout(circuit_log: int, rounds: list[int]) -> list[dict]:
    """Predict every deterministic registry slot field before native admission."""
    slots = []
    main, interaction, constraint = 0, 0, 0
    for index in range(1 + 2 * len(rounds)):
        if index == 0:
            call_id, key, registry_id, role = None, "bundled_circuit", 0, "circuit"
            trace_log, evaluation_log = circuit_log, circuit_log + 1
            main_columns, interaction_columns, n_constraints = 12, 8, 11
            relations, preprocessed = [378353459], [0, 2, 3, 1, 4, 5, 6, 7]
        else:
            call_id = (index - 1) // 2
            chip = index % 2 == 1
            family = "pair" if call_id < 2 else "many"
            key = f"{family}_{'chip' if chip else 'bridge'}"
            registry_id = (1 if chip else 2) + (0 if family == "pair" else 2)
            role = "chip" if chip else "bridge"
            trace_log = rounds[call_id].bit_length() - 1 if chip else 4
            evaluation_log = trace_log + 1 if chip else 6
            main_columns, interaction_columns, n_constraints = (
                (9, 8, 6) if chip else (8, 20, 13))
            relations = [1395863811] if chip else [378353459, 1395863811]
            preprocessed = []
        slots.append({"source_kind": key, "registry_key": key,
                      "registry_id": registry_id, "registry_role": role,
                      "registry_version": 1, "call_id": call_id,
                      "proof_index": index, "claimed_sum_index": index,
                      "trace_log_size": trace_log,
                      "evaluation_log_size": evaluation_log,
                      "main_offset": main, "main_columns": main_columns,
                      "interaction_offset": interaction,
                      "interaction_columns": interaction_columns,
                      "constraint_offset": constraint,
                      "n_constraints": n_constraints,
                      "preprocessed_indices": preprocessed,
                      "relation_ids": relations})
        main += main_columns
        interaction += interaction_columns
        constraint += n_constraints
    return slots


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
        raise ValueError("production Zig bytes differ from isolated V17 source base commit")
    current_pins = v3.pins()
    v12 = v2.parse(cost_model.INPUTS["v12_protocol"].read_bytes())
    if (current_pins["host"] != v12["host"] or
            current_pins["compiler_sha256"] != v12["compiler_sha256"] or
            current_pins["engine_gitlink_commit"] != v12["engine_gitlink_commit"]):
        raise ValueError("V17 host/compiler/engine differs from frozen V12 validation")
    model_raw = MODEL.read_bytes()
    model = v2.parse(model_raw)
    if (model["schema"] != "s31-mixed-cost-v17-mixed-calls-model" or
            model_raw != cost_model.canonical(cost_model.derive())):
        raise ValueError("V17 rule differs from declared V11–V16 evidence")
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
            raise ValueError("V17 source or claim collides with prior evidence")
        new_sources.add(digest)
        new_claims.update(all_claims)
        count = len(spec["rounds"])
        expected_calls = source_calls(rows[0][0])
        if ([call["rounds"] for call in expected_calls] != list(spec["rounds"]) or
                [call["call_id"] for call in expected_calls] != list(range(count))):
            raise ValueError("source-derived call roster differs from design")
        slot_logs = [spec["ops"].bit_length()] + [entry for rounds in spec["rounds"]
                                                     for entry in (rounds.bit_length() - 1, 4)]
        expected_slots = slot_layout(spec["ops"].bit_length(), list(spec["rounds"]))
        if ([slot["trace_log_size"] for slot in expected_slots] != slot_logs or
                sum(slot["n_constraints"] for slot in expected_slots) != 11 + 19 * count):
            raise ValueError("source-derived slot layout differs from design")
        mul_count = sum((index + branch) % spec["mul_every"] == 0
                        for index in range(spec["ops"] // spec["branches"])
                        for branch in range(spec["branches"]))
        roster[name] = {
            "source_sha256": digest, "call_count": count,
            "chip_rounds": list(spec["rounds"]), "live_arithmetic_nodes": spec["ops"],
            "expected_calls": expected_calls,
            "live_mul_nodes": mul_count,
            "live_add_nodes": spec["ops"] - mul_count,
            "topology": f"sixteen live {spec['ops'] // 16}-operation branches with one-fifth multiplication, joined as a balanced binary tree before mixed-length chip calls",
            "source_nodes": len(v2.parse(rows[0][0])["nodes"]),
            "expected_geometry": {
                "slots": 1 + 2 * count, "constraints": 11 + 19 * count,
                "tree_columns": [8, 12 + 17 * count, 8 + 28 * count, 8],
                "slot_trace_logs": slot_logs,
                "slot_constraints": [11] + [value for _ in range(count)
                                            for value in (6, 13)],
                "slot_layout": expected_slots,
                "max_column_log_size": max(slot_logs),
                "composition_log_size": max(slot_logs)},
            "assignment_sha256": assignments, "statement_sha256": statements,
            "prediction": cost_model.prediction(model, name),
        }
    if len(new_sources) != 3 or len(new_claims) != 126:
        raise ValueError("V17 fresh source/claim count differs")
    return {
        "schema": "s31-mixed-cost-v17-mixed-calls-protocol",
        "status": "pre-native-frozen", "source_roster": roster,
        "v17_model_sha256": sha(model_raw),
        "declared_training_sha256": model["input_sha256"],
        "source_base_commit": SOURCE_BASE_COMMIT,
        "build_mode": "ReleaseFast", "lowering": "direct-mixed-general",
        "claims_per_source": CLAIMS + 1, "scored_claims_per_source": CLAIMS,
        "first_post_build_claim": 0, "claim_zero_immediate_repeat": True,
        "scored_schedule_seed": SCHEDULE_SEED,
        "scored_schedule": schedule(),
        "process_measurement": "fresh prover and external verifier subprocess wall under /usr/bin/time for OS peak RSS; same method as V11 wall fit and V12 validation",
        "reported_phase_measurement": "S31_MIXED_NATIVE_PHASE_V1 interaction and FRI PoW; residual = first verified wall minus both PoW reports",
        "nonpow_residual_guard": "every cold and scored trial must have positive FRI/interaction PoW durations and their sum strictly below measured verified prover-plus-external-verifier process wall; scorer and independent audit reject any nonpositive residual before division",
        "proof_negative_error": "InvalidMixedInteractionNonce",
        "native_builds_before_scored_proofs": "all three packages built and manifested before any claim-0 or scored proof",
        "native_manifest_admission": "exact source-derived ordered call IDs/source and feeder node IDs/rounds/constants; complete deterministic slot layout including per-slot constraints, registry roles, offsets, relation and preprocessed IDs; compiler-assigned numeric addresses checked for four-lane shape, fresh outputs and consecutive call-chain equality but not forecast numerically",
        "one_prospective_run_only": True,
        "fixed_attempt_marker": "design/s31/measurements/language/mixed-cost-v17-mixed-calls-attempt.jsonl",
        "attempt_semantics": "before any native build, atomically create the fixed marker with O_EXCL and fsync file/directory; reject all subsequent invocations regardless of output path; append completed or failed terminal metadata, retaining a started-only marker after hard interruption",
        "speedup_claim_enabled": False,
        "model_claim": "V11–V16-trained V17 mixed-length N4/N8 chip calls at circuit logs 13/14; V11/V15 failures declared training; PoW distribution inherited from V12; no host-independent reliability claim",
        "build_cold_prediction_status": model["build_cold_prediction_status"],
        "gates": GATES,
        "transfer_tool_sha256": {path: sha((ROOT / path).read_bytes()) for path in PIN_PATHS},
        **current_pins,
    }


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    if raw != canonical(value) or value != prepare_value():
        raise ValueError("V17 protocol or pinned stack differs from pre-native freeze")
    for path in (PROTOCOL, MODEL):
        if v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != path.read_bytes():
            raise ValueError(f"V17 frozen file was not committed unchanged: {path}")
    for name in SOURCES:
        path = SOURCE_DIR / f"{name}.json"
        if (path.read_bytes() != source(name) or
                v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != source(name)):
            raise ValueError(f"V17 source was not committed unchanged: {name}")
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
                raise ValueError("V17 protocol or sources already frozen")
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
