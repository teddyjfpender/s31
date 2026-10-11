#!/usr/bin/env python3
"""Native-free 80-claim N=1/N=8 transfer of the unchanged v4 predictor."""

from __future__ import annotations

import argparse
import json
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(HERE.parent / "mixed_cost_v4"))
import model as v4_model  # noqa: E402
import prospective as v4  # noqa: E402

v3, v2 = v4.v3, v4.v3.v2
LANGUAGE = ROOT / "design/s31/measurements/language"
PROTOCOL = LANGUAGE / "mixed-cost-v7-transfer-protocol.json"
SOURCE_DIR = LANGUAGE / "mixed-cost-v7-transfer-sources"
MODEL = LANGUAGE / "mixed-cost-v4-model.json"
V4_PROTOCOL = LANGUAGE / "mixed-cost-v4-protocol.json"
V5_PROTOCOL = LANGUAGE / "mixed-cost-v5-transfer-protocol.json"
V6_PROTOCOL = LANGUAGE / "mixed-cost-v6-transfer-protocol.json"
NAMES = {"affine_seed_n1": 1, "switchback_n8": 8}
CLAIMS = 80
SEED = 202610117703
P = 2**31 - 1
GATES = {
    "wall_median_relative_error_per_source_max": 0.30,
    "wall_90_interval_coverage_per_source_min": 0.80,
    "proof_median_relative_error_per_source_max": 0.10,
    "proof_90_interval_coverage_per_source_min": 0.80,
}
PIN_PATHS = (
    "src/frontends/s31/build.zig",
    "src/frontends/s31/language/relation_compiler.zig",
    "src/frontends/s31/language/bounded_call_admission.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_package.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_trace_audit_main.zig",
    "src/frontends/s31/python/abi/binding_v2.py",
    "src/frontends/s31/python/oracle.py",
    "src/frontends/s31/tests/acceptance/mixed_boundary/registry_manifest_digest.py",
    "src/frontends/s31/benchmarks/mixed_cost_v7_transfer/protocol.py",
    "src/frontends/s31/benchmarks/mixed_cost_v7_transfer/study.py",
    "src/frontends/s31/benchmarks/mixed_cost_v7_transfer/audit.py",
    "src/frontends/s31/benchmarks/mixed_cost_v7_transfer/test_static.py",
)


def canonical(value: object) -> bytes:
    return v2.canonical(value)


def sha(raw: bytes) -> str:
    return v2.sha(raw)


@lru_cache(maxsize=None)
def source(name: str) -> bytes:
    if name not in NAMES:
        raise ValueError("outside frozen transfer roster")
    template = v2.parse(v2.source("control", 2, v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    nodes: list[dict] = []
    previous = input_name
    count = NAMES[name]
    for index in range(count):
        feeder = f"feeder{index}"
        if name == "affine_seed_n1":
            nodes.append({"name": "scaled_input", "op": "mul_const",
                          "lhs": input_name, "constant": 7})
            nodes.append({"name": feeder, "op": "add_const",
                          "lhs": "scaled_input", "constant": 11})
        elif index % 2 == 0:
            nodes.append({"name": feeder, "op": "add", "lhs": previous,
                          "rhs": input_name})
        else:
            nodes.append({"name": feeder, "op": "mul_const", "lhs": previous,
                          "constant": index + 3})
        repeated = f"r{index}"
        nodes.append({"name": repeated, "op": "repeat", "lhs": feeder,
                      "rounds": 16,
                      "body": [{"op": "square"},
                               {"op": "add_const", "constant": 73 + index}]})
        if name == "switchback_n8" and index % 3 == 0 and index + 1 < count:
            merged = f"offset{index}"
            nodes.append({"name": merged, "op": "add_const", "lhs": repeated,
                          "constant": index + 23})
            previous = merged
        else:
            previous = repeated
    if name == "affine_seed_n1":
        nodes.append({"name": "offset_result", "op": "add_const",
                      "lhs": previous, "constant": 17})
        previous = "offset_result"
    nodes.append({"name": output_name, "op": "add", "lhs": previous,
                  "rhs": input_name})
    relation = {**template, "name": f"mixed_cost_v7_transfer_{name}",
                "nodes": nodes}
    v2.flat(relation)
    return canonical(relation)


def expected_output(name: str, words: list[int]) -> list[int]:
    previous = words[:]
    for index in range(NAMES[name]):
        if name == "affine_seed_n1":
            feeder = [(7 * word + 11) % P for word in words]
        elif index % 2 == 0:
            feeder = [(left + right) % P for left, right in zip(previous, words)]
        else:
            feeder = [((index + 3) * word) % P for word in previous]
        previous = feeder
        for _ in range(16):
            previous = [(word * word + 73 + index) % P for word in previous]
        if name == "switchback_n8" and index % 3 == 0 and index + 1 < NAMES[name]:
            previous = [(word + index + 23) % P for word in previous]
    if name == "affine_seed_n1":
        previous = [(word + 17) % P for word in previous]
    return [(left + right) % P for left, right in zip(previous, words)]


def case(name: str, index: int) -> tuple[bytes, bytes, bytes]:
    if name not in NAMES or not 0 <= index <= CLAIMS:
        raise ValueError("outside frozen source/claim roster")
    raw_source = source(name)
    relation = v2.parse(raw_source)
    family = tuple(NAMES).index(name)
    seed = SEED + family * 10_000_000 + NAMES[name] * 100_000 + index * 61
    words = [(seed * (lane + 37) + lane * lane + 23) % P for lane in range(4)]
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]:
                                     expected_output(name, words)}}
    if (v2.evaluate_relation(v2.flat(relation), assignment) !=
            assignment["public_outputs"]):
        raise ValueError("independent arithmetic oracle differs from source")
    statement = v2.statement_from_assignment(relation, assignment)
    v2.changed_result(raw_source, statement)
    return raw_source, canonical(assignment), statement


def prepare_value() -> dict:
    model_bytes = MODEL.read_bytes()
    model = v2.parse(model_bytes)
    if model.get("schema") != "s31-mixed-cost-v4-distribution-model":
        raise ValueError("wrong frozen v4 model")
    prior = v2.parse(V4_PROTOCOL.read_bytes())
    v5 = v2.parse(V5_PROTOCOL.read_bytes())
    v6 = v2.parse(V6_PROTOCOL.read_bytes())
    previous_rows = [entry for group in prior["split"].values()
                     for entry in group.values()]
    previous_rows += list(v5["source_roster"].values())
    previous_rows += list(v6["source_roster"].values())
    previous_sources = {entry["source_sha256"] for entry in previous_rows}
    previous_claims = {digest for entry in previous_rows
                       for key in ("assignment_sha256", "statement_sha256")
                       for digest in entry[key]}
    roster = {}
    seen_sources = set()
    seen_claims = set()
    for name, count in NAMES.items():
        rows = [case(name, index) for index in range(CLAIMS + 1)]
        source_hash = sha(rows[0][0])
        assignment_hashes = [sha(row[1]) for row in rows]
        statement_hashes = [sha(row[2]) for row in rows]
        current_claims = set(assignment_hashes + statement_hashes)
        if (source_hash in previous_sources or source_hash in seen_sources or
                len(current_claims) != 2 * (CLAIMS + 1) or
                current_claims & (previous_claims | seen_claims) or
                any(row[0] != rows[0][0] for row in rows)):
            raise ValueError("source or claim collision")
        seen_sources.add(source_hash)
        seen_claims.update(current_claims)
        roster[name] = {"call_count": count, "source_sha256": source_hash,
                        "source_nodes": len(v2.parse(rows[0][0])["nodes"]),
                        "assignment_sha256": assignment_hashes,
                        "statement_sha256": statement_hashes,
                        "prediction": v4_model.prediction(model, count)}
    pins = v3.pins()
    return {"schema": "s31-mixed-cost-v7-transfer-protocol",
            "status": "pre-native-frozen", "source_roster": roster,
            "v4_model_sha256": sha(model_bytes),
            "v4_protocol_sha256": sha(V4_PROTOCOL.read_bytes()),
            "v5_protocol_sha256": sha(V5_PROTOCOL.read_bytes()),
            "v6_protocol_sha256": sha(V6_PROTOCOL.read_bytes()),
            "source_ids_disjoint_from_v4_v5_v6": True,
            "build_mode": "ReleaseFast", "lowering": "direct-mixed-general",
            "claims_per_source": CLAIMS + 1,
            "process_order": "claim 0 first-post-build and immediate same-claim repeat; then claims 1..80 ascending",
            "scored_claim_indices": [1, CLAIMS],
            "cold_pair": "claim 0 twice, descriptive only",
            "proof_negative_error": "InvalidMixedInteractionNonce",
            "gates": GATES, "speedup_claim_enabled": False,
            "transfer_tool_sha256": {path: sha((ROOT / path).read_bytes())
                                     for path in PIN_PATHS},
            **pins}


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    if raw != canonical(value) or value != prepare_value():
        raise ValueError("protocol or pinned stack differs from pre-native freeze")
    if v2.git("show", f"HEAD:{PROTOCOL.relative_to(ROOT).as_posix()}") != raw:
        raise ValueError("protocol must be committed before native measurement")
    for name in NAMES:
        path = SOURCE_DIR / f"{name}.json"
        if (path.read_bytes() != source(name) or
                v2.git("show", f"HEAD:{path.relative_to(ROOT).as_posix()}") != source(name)):
            raise ValueError(f"source bytes must be committed unchanged: {name}")
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
                raise ValueError("transfer protocol or sources already exist")
            SOURCE_DIR.mkdir()
            for name in NAMES:
                (SOURCE_DIR / f"{name}.json").write_bytes(source(name))
            PROTOCOL.write_bytes(raw)
    print(json.dumps({"protocol_sha256": digest,
                      "sources": {name: entry["source_sha256"]
                                  for name, entry in value["source_roster"].items()},
                      "predictions": {name: entry["prediction"]
                                      for name, entry in value["source_roster"].items()}},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
