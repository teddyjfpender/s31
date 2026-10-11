#!/usr/bin/env python3
"""Native-free v4 source and claim inventory; never measures proof timings."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
_spec = importlib.util.spec_from_file_location(
    "mixed_cost_v3_for_v4", HERE.parent / "mixed_cost_v3/study.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("v3 generator unavailable")
sys.path.insert(0, str(HERE.parent / "mixed_cost_v3"))
v3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(v3)

P = (1 << 31) - 1
SEED = 202610119907
CLAIMS = 80
GATES = {
    "wall_program_p90_median_relative_error_max": 0.30,
    "wall_nominal_90_interval_coverage_min": 0.85,
    "wall_nominal_90_interval_coverage_per_source_min": 0.75,
    "proof_program_p90_median_relative_error_max": 0.10,
    "proof_nominal_90_interval_coverage_min": 0.85,
    "proof_nominal_90_interval_coverage_per_source_min": 0.75,
}
SPLITS = {
    "train": (("relay", 3), ("relay", 7), ("twist", 3), ("twist", 7)),
    "heldout": (("braid", 5), ("braid", 7), ("spoke", 5), ("spoke", 7)),
}
OUTPUT = ROOT / "design/s31/measurements/language/mixed-cost-v4-prospective-inventory.json"


def add(left: list[int], right: list[int]) -> list[int]:
    return [(a + b) % P for a, b in zip(left, right)]


def mul_const(values: list[int], constant: int) -> list[int]:
    return [(v * constant) % P for v in values]


def add_const(values: list[int], constant: int) -> list[int]:
    return [(v + constant) % P for v in values]


def repeat(values: list[int], index: int) -> list[int]:
    result = values[:]
    for _ in range(16):
        result = [(v * v + 29 + index) % P for v in result]
    return result


def repeat_node(name: str, lhs: str, index: int) -> dict:
    return {"name": name, "op": "repeat", "lhs": lhs, "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 29 + index}]}


def nodes(shape: str, count: int, input_name: str, output_name: str) -> list[dict]:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"]:
        raise ValueError("source outside v4 split")
    result = []
    previous = input_name
    for index in range(count):
        r = f"r{index}"
        if shape == "relay":
            result.append(repeat_node(r, previous, index))
            previous = r
            if index + 1 < count:
                next_name = f"relay{index}"
                result.append({"name": next_name, "op": "add",
                               "lhs": previous, "rhs": input_name})
                previous = next_name
        elif shape == "twist":
            pre = f"pre{index}"
            if index % 2 == 0:
                result.append({"name": pre, "op": "mul_const",
                               "lhs": previous, "constant": index + 2})
            else:
                result.append({"name": pre, "op": "add_const",
                               "lhs": previous, "constant": 31 + index})
            result.append(repeat_node(r, pre, index))
            previous = r
        elif shape == "braid":
            lhs = input_name if index % 2 else previous
            result.append(repeat_node(r, lhs, index))
            if index:
                summed = f"braid{index}"
                result.append({"name": summed, "op": "add",
                               "lhs": previous, "rhs": r})
                previous = summed
            else:
                previous = r
        else:  # spoke
            result.append(repeat_node(r, input_name, index))
            if index:
                scaled = f"scaled{index}"
                summed = f"spoke{index}"
                result.append({"name": scaled, "op": "mul_const",
                               "lhs": previous, "constant": index + 2})
                result.append({"name": summed, "op": "add",
                               "lhs": scaled, "rhs": r})
                previous = summed
            else:
                previous = r
    result.append({"name": output_name, "op": "add",
                   "lhs": previous, "rhs": input_name})
    return result


def output_words(shape: str, count: int, words: list[int]) -> list[int]:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"] or len(words) != 4:
        raise ValueError("invalid v4 oracle input")
    previous = words[:]
    for index in range(count):
        if shape == "relay":
            previous = repeat(previous, index)
            if index + 1 < count:
                previous = add(previous, words)
        elif shape == "twist":
            before = (mul_const(previous, index + 2) if index % 2 == 0
                      else add_const(previous, 31 + index))
            previous = repeat(before, index)
        elif shape == "braid":
            current = repeat(words if index % 2 else previous, index)
            previous = add(previous, current) if index else current
        else:
            current = repeat(words, index)
            previous = add(mul_const(previous, index + 2), current) if index else current
    return add(previous, words)


@lru_cache(maxsize=None)
def source(shape: str, count: int) -> bytes:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"]:
        raise ValueError("source outside v4 split")
    template = v3.v2.parse(v3.v2.source("control", 2, v3.v2.source_design()))
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    relation = {**template, "name": f"mixed_cost_v4_{shape}_n{count}",
                "nodes": nodes(shape, count, input_name, output_name)}
    v3.v2.flat(relation)  # reject malformed or unsupported relation shape
    return v3.v2.canonical(relation)


def case(shape: str, count: int, index: int) -> tuple[bytes, bytes, bytes]:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"] or not 0 <= index < CLAIMS:
        raise ValueError("claim outside v4 split")
    raw_source = source(shape, count)
    relation = v3.v2.parse(raw_source)
    family = [item for split in SPLITS.values() for item in split].index((shape, count))
    seed = SEED + family * 10_000_000 + count * 100_000 + index * 53
    words = [(seed * (lane + 29) + lane * lane + 17) % P for lane in range(4)]
    expected = output_words(shape, count, words)
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: expected}}
    if v3.v2.evaluate_relation(v3.v2.flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent oracle disagrees with v4 source")
    statement = v3.v2.statement_from_assignment(relation, assignment)
    v3.v2.changed_result(raw_source, statement)
    return raw_source, v3.v2.canonical(assignment), statement


def prior_hashes() -> tuple[set[str], set[str]]:
    sources = set()
    claims = v3.v2.prior_claim_hashes()
    for relative in v3.v2.PRIOR_PROTOCOLS:
        document = v3.v2.parse((ROOT / relative).read_bytes())
        if document["schema"] == "s31-mixed-phase-v1-protocol":
            rows = document["roster"].values()
        elif document["schema"] == "s31-mixed-stage-cost-transfer-v1-protocol-candidate":
            rows = document["inventory"].values()
        elif document["schema"] == "s31-mixed-stage-cost-v1-protocol":
            rows = [row for group in document["inventory"].values()
                    for row in group.values()]
        else:
            raise ValueError("unexpected prior source protocol")
        sources.update(row["source_sha256"] for row in rows)
    for protocol_path in (v3.v2.PROTOCOL, v3.PROTOCOL):
        protocol = v3.v2.parse(protocol_path.read_bytes())
        for group in protocol["split"].values():
            for row in group.values():
                sources.add(row["source_sha256"])
                claims.update(row["assignment_sha256"])
                claims.update(row["statement_sha256"])
    return sources, claims


def inventory() -> dict:
    prior_sources, prior_claims = prior_hashes()
    seen_sources, seen_claims = set(prior_sources), set(prior_claims)
    split = {}
    for split_name, programs in SPLITS.items():
        group = {}
        for shape, count in programs:
            rows = [case(shape, count, index) for index in range(CLAIMS)]
            source_hash = v3.v2.sha(rows[0][0])
            assignment_hashes = [v3.v2.sha(row[1]) for row in rows]
            statement_hashes = [v3.v2.sha(row[2]) for row in rows]
            all_claims = assignment_hashes + statement_hashes
            if (source_hash in seen_sources or len(set(all_claims)) != len(all_claims) or
                    set(all_claims) & seen_claims or any(row[0] != rows[0][0] for row in rows)):
                raise ValueError("v4 source or claim reused prior evidence")
            seen_sources.add(source_hash)
            seen_claims.update(all_claims)
            name = f"{shape}_n{count}"
            group[name] = {"shape": shape, "call_count": count,
                           "rounds_per_call": 16, "source_nodes": len(v3.v2.parse(rows[0][0])["nodes"]),
                           "source_sha256": source_hash,
                           "assignment_sha256": assignment_hashes,
                           "statement_sha256": statement_hashes}
        split[split_name] = group
    if len(seen_sources - prior_sources) != 8 or len(seen_claims - prior_claims) != 16 * CLAIMS:
        raise ValueError("v4 inventory count differs")
    return {"schema": "s31-mixed-cost-v4-prospective-inventory",
            "status": "design-only-no-native-runner",
            "source_generator_sha256": v3.v2.sha(Path(__file__).read_bytes()),
            "distribution_model_source_sha256": v3.v2.sha((HERE / "model.py").read_bytes()),
            "v3_protocol_sha256": v3.v2.sha(v3.PROTOCOL.read_bytes()),
            "v2_protocol_sha256": v3.v2.sha(v3.v2.PROTOCOL.read_bytes()),
            "source_template_sha256": v3.v2.sha(
                (ROOT / v3.v2.source_design()["source_template"]).read_bytes()),
            "assignment_seed": SEED, "claims_per_source": CLAIMS,
            "fit_claim_indices": [1, 40],
            "calibration_claim_indices": [41, 79],
            "heldout_score_claim_indices": [1, 79],
            "first_claim_processes": "index-0 first post-build and immediate same-claim repeat, both diagnostic only",
            "gates": GATES,
            "speedup_claim_enabled": False,
            "automatic_lowering_enabled": False,
            "source_and_claim_disjoint_from_v2_v3": True,
            "split": split}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "write"))
    args = parser.parse_args()
    data = inventory()
    raw = v3.v2.canonical(data)
    if args.action == "write":
        if OUTPUT.exists():
            raise ValueError("prospective inventory already exists")
        OUTPUT.write_bytes(raw)
    print(json.dumps({"schema": data["schema"], "status": data["status"],
                      "sha256": v3.v2.sha(raw), "sources": 8,
                      "unique_claims": 8 * CLAIMS}, sort_keys=True))


if __name__ == "__main__":
    main()
