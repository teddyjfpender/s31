#!/usr/bin/env python3
"""Native-free V12 log-12 source, claim, prediction, and randomized schedule freeze."""

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
MODEL = LANGUAGE / "mixed-cost-v12-decomposed-model.json"
PROTOCOL = LANGUAGE / "mixed-cost-v12-decomposed-protocol.json"
SOURCE_DIR = LANGUAGE / "mixed-cost-v12-decomposed-sources"
PREVIOUS_PROTOCOLS = (
    LANGUAGE / "mixed-cost-v4-protocol.json",
    LANGUAGE / "mixed-cost-v5-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v6-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v7-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v8-calibrated-protocol.json",
    LANGUAGE / "mixed-cost-v9-geometry-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v10-geometry-transfer-protocol.json",
    LANGUAGE / "mixed-cost-v11-unseen-protocol.json",
)
PROBES = LANGUAGE / "mixed-cost-v9-feasibility"
SOURCES = {
    "circuit_cascade_n1": {"gates": 2048, "rounds": (16,)},
    "chip_spiral_n1": {"gates": 0, "rounds": (4096,)},
    "joint_cascade_n1": {"gates": 2048, "rounds": (4096,)},
    "serial_spiral_n2": {"gates": 0, "rounds": (4096, 32)},
}
NAMES = tuple(SOURCES)
CLAIMS = 20
P = 2**31 - 1
CLAIM_SEED = 202610122219
SCHEDULE_SEED = 202610122241
SOURCE_BASE_COMMIT = "7e90b5833eecb893c6db5f260e5d1cfc69cd230f"
GATES = {
    "wall_median_relative_error_per_source_max": 0.30,
    "wall_one_draw_90_coverage_per_source_min": 0.70,
    "wall_one_draw_90_coverage_pooled_min": 67 / 80,
    "wall_sample20_median_90_band_source_count_min": 3,
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
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/study.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/audit.py",
    "src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/test_static.py",
    "src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/protocol.py",
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
        raise ValueError("outside V12 source roster")
    template = v2.parse(v2.source("control", 2, v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    family = NAMES.index(name)
    spec = SOURCES[name]
    nodes: list[dict] = [
        {"name": "shifted_input", "op": "add_const", "lhs": input_name,
         "constant": 211 + family * 23},
        {"name": "feeder", "op": "mul_const", "lhs": "shifted_input",
         "constant": 31 + family * 6},
    ]
    previous = "feeder"
    for index in range(spec["gates"]):
        next_name = f"g{index}"
        rhs = previous if index % 7 == 0 else "shifted_input"
        nodes.append({"name": next_name, "op": "mul", "lhs": previous, "rhs": rhs})
        previous = next_name
        if index % 127 == 126:
            adjusted = f"offset{index}"
            nodes.append({"name": adjusted, "op": "add_const", "lhs": previous,
                          "constant": 307 + family * 29 + index})
            previous = adjusted
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
                  "rhs": "shifted_input"})
    relation = {**template, "name": f"mixed_cost_v12_decomposed_{name}",
                "nodes": nodes}
    v2.flat(relation)
    return canonical(relation)


def output(name: str, words: list[int]) -> list[int]:
    if name not in SOURCES or len(words) != 4:
        raise ValueError("invalid V12 source/words")
    family = NAMES.index(name)
    spec = SOURCES[name]
    shifted = [(word + 211 + family * 23) % P for word in words]
    previous = [(word * (31 + family * 6)) % P for word in shifted]
    for index in range(spec["gates"]):
        rhs = previous if index % 7 == 0 else shifted
        previous = [(left * right) % P for left, right in zip(previous, rhs, strict=True)]
        if index % 127 == 126:
            previous = [(word + 307 + family * 29 + index) % P for word in previous]
    for call_id, rounds in enumerate(spec["rounds"]):
        for _ in range(rounds):
            previous = [(word * word + 257 + family * 31 + call_id) % P
                        for word in previous]
    previous = [(word * (41 + family * 2)) % P for word in previous]
    return [(left + right) % P for left, right in zip(previous, shifted, strict=True)]


def case(name: str, index: int) -> tuple[bytes, bytes, bytes]:
    if name not in SOURCES or not 0 <= index <= CLAIMS:
        raise ValueError("outside V12 source/claim roster")
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
        raise ValueError("production Zig bytes differ from isolated V12 source base commit")
    model_raw = MODEL.read_bytes()
    model = v2.parse(model_raw)
    if (model["schema"] != "s31-mixed-cost-v12-decomposed-model" or
            model_raw != cost_model.canonical(cost_model.fit())):
        raise ValueError("V12 model differs from frozen V10/V11 fit")
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
            raise ValueError("V12 source or claim collides with prior evidence")
        new_sources.add(digest)
        new_claims.update(all_claims)
        count = len(spec["rounds"])
        slot_logs = [12 if spec["gates"] else 9] + [entry for rounds in spec["rounds"]
                                                     for entry in (rounds.bit_length() - 1, 4)]
        roster[name] = {
            "source_sha256": digest, "call_count": count,
            "chip_rounds": list(spec["rounds"]), "live_mul_chain": spec["gates"],
            "source_nodes": len(v2.parse(rows[0][0])["nodes"]),
            "expected_geometry": {
                "slots": 1 + 2 * count, "constraints": 11 + 19 * count,
                "tree_columns": [8, 12 + 17 * count, 8 + 28 * count, 8],
                "slot_trace_logs": slot_logs,
                "max_column_log_size": 12, "composition_log_size": 12},
            "assignment_sha256": assignments, "statement_sha256": statements,
            "prediction": cost_model.prediction(model, name),
        }
    if len(new_sources) != 4 or len(new_claims) != 168:
        raise ValueError("V12 fresh source/claim count differs")
    return {
        "schema": "s31-mixed-cost-v12-decomposed-protocol",
        "status": "pre-native-frozen", "source_roster": roster,
        "v12_model_sha256": sha(model_raw),
        "v11_result_sha256": model["fit_input_sha256"]["v11_result_same_wall_method"],
        "v11_failed_score_sha256": model["fit_input_sha256"]["v11_score_failed_declared_training"],
        "source_base_commit": SOURCE_BASE_COMMIT,
        "build_mode": "ReleaseFast", "lowering": "direct-mixed-general",
        "claims_per_source": CLAIMS + 1, "scored_claims_per_source": CLAIMS,
        "first_post_build_claim": 0, "claim_zero_immediate_repeat": True,
        "scored_schedule_seed": SCHEDULE_SEED,
        "scored_schedule": schedule(),
        "process_measurement": "fresh prover and external verifier subprocess wall under /usr/bin/time for OS peak RSS; same method as V11 wall fit",
        "reported_phase_measurement": "S31_MIXED_NATIVE_PHASE_V1 interaction and FRI PoW; residual = first verified wall minus both PoW reports",
        "proof_negative_error": "InvalidMixedInteractionNonce",
        "native_builds_before_scored_proofs": "all four packages built and manifested before any claim-0 or scored proof",
        "one_prospective_run_only": True,
        "speedup_claim_enabled": False,
        "model_claim": "V11-fitted decomposed falsification at unseen log 12; no host-independent reliability claim",
        "gates": GATES,
        "transfer_tool_sha256": {path: sha((ROOT / path).read_bytes()) for path in PIN_PATHS},
        **v3.pins(),
    }


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    if raw != canonical(value) or value != prepare_value():
        raise ValueError("V12 protocol or pinned stack differs from pre-native freeze")
    for path in (PROTOCOL, MODEL):
        if v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != path.read_bytes():
            raise ValueError(f"V12 frozen file was not committed unchanged: {path}")
    for name in SOURCES:
        path = SOURCE_DIR / f"{name}.json"
        if (path.read_bytes() != source(name) or
                v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != source(name)):
            raise ValueError(f"V12 source was not committed unchanged: {name}")
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
                raise ValueError("V12 protocol or sources already frozen")
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
