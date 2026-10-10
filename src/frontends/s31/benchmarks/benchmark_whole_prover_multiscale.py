#!/usr/bin/env python3
"""Build a multi-scale, native-verified corpus for held-out S31 cost evaluation."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "python"))
sys.path.insert(0, str(HERE / "benchmarks"))

import s31
from benchmark_whole_prover import measured_package_build
from runtime.cost_model import observed_cost_model

P = (1 << 31) - 1
ARITHMETIC_ROUNDS = (16, 64, 256, 1024)
HASH_DEPTHS = (1, 2, 3, 4)
SIGNED_WIDTHS = (8, 16, 32, 64)


def arithmetic_program(rounds: int) -> dict:
    return {
        "version": 1, "name": f"arith_step_{rounds}",
        "inputs": [{"name": "x", "kind": "m31", "length": 4, "visibility": "public"}],
        "nodes": [{"name": "result", "op": "repeat", "lhs": "x", "rounds": rounds,
                   "body": [{"op": "square"}, {"op": "add_const", "constant": 7}]}],
        "assertions": [], "public_outputs": ["result"],
    }


def arithmetic_assignment(rounds: int, index: int) -> dict:
    values = [1 + 17 * index, 2 + 31 * index, 3 + 47 * index, 511 + 59 * index]
    result = values.copy()
    for _ in range(rounds):
        result = [(value * value + 7) % P for value in result]
    return {"public_inputs": {"x": values}, "private_inputs": {},
            "public_outputs": {"result": result}}


def hash_program(depth: int) -> dict:
    inputs = [{"name": "secret", "kind": "m31", "length": 8, "visibility": "private"}]
    if depth > 1:
        inputs.append({"name": "sibling", "kind": "m31", "length": 8, "visibility": "private"})
    nodes = [{"name": "h0", "op": "hash_blake2s_leaf", "lhs": "secret"}]
    for step in range(1, depth):
        nodes.append({"name": f"h{step}", "op": "hash_blake2s_pair",
                      "lhs": f"h{step - 1}", "rhs": "sibling"})
    return {"version": 1, "name": f"blake_chain_{depth}", "inputs": inputs,
            "nodes": nodes, "assertions": [], "public_outputs": [f"h{depth - 1}"]}


def _blake(words: list[int], person: bytes) -> list[int]:
    data = b"".join(struct.pack("<I", value) for value in words)
    raw = hashlib.blake2s(data, person=person).digest()
    return [value % P for value in struct.unpack("<8I", raw)]


def hash_assignment(depth: int, index: int) -> dict:
    secret = [index * 17 + offset + 1 for offset in range(8)]
    sibling = [index * 19 + offset + 101 for offset in range(8)]
    root = _blake(secret, b"S31LEAF1")
    for _ in range(1, depth):
        root = _blake(root + sibling, b"S31PAIR1")
    private = {"secret": secret}
    if depth > 1:
        private["sibling"] = sibling
    return {"public_inputs": {}, "private_inputs": private,
            "public_outputs": {f"h{depth - 1}": root}}


def workload_cases(output: Path, samples: int) -> list[dict]:
    source_dir = output / "generated-sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    workloads = []
    for rounds in ARITHMETIC_ROUNDS:
        name = f"arithmetic_{rounds}"
        source = source_dir / f"{name}.s31.json"
        s31.write_json(source, arithmetic_program(rounds))
        workloads.append({"name": name, "family": "arithmetic", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [arithmetic_assignment(rounds, index) for index in range(samples)]})
    for depth in HASH_DEPTHS:
        name = f"hash_{depth}"
        source = source_dir / f"{name}.s31.json"
        s31.write_json(source, hash_program(depth))
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, index) for index in range(samples)]})
    for width in SIGNED_WIDTHS:
        name = f"signed_division_{width}"
        source = HERE / f"examples/math/division/i{width}_div_rem.s31"
        fixture_dir = HERE / f"examples/math/division/fixtures/i{width}"
        fixtures = sorted(fixture_dir.glob("*.json"))
        if len(fixtures) < samples:
            raise ValueError(f"{name} has only {len(fixtures)} fixtures")
        workloads.append({"name": name, "family": "fixed_width", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [json.loads(path.read_text()) for path in fixtures[:samples]]})
    return workloads


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=5, help="distinct witnesses per program (3..5)")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if not 3 <= args.samples <= 5:
        parser.error("--samples must be between 3 and 5")
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    prepared = []
    for workload in workload_cases(output, args.samples):
        name = workload["name"]
        source = workload["source"]
        package, build_measurement = measured_package_build(
            source, output / name / "package", workload["lowering"])
        manifest = json.loads((package / "manifest.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
        assignment_digests = []
        for index, assignment in enumerate(workload["assignments"]):
            path = output / name / "assignments" / f"{index:02d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(path, assignment)
            assignment_digests.append(s31.assignment_digest(path))
        if len(set(assignment_digests)) != args.samples:
            raise ValueError(f"{name} did not produce distinct witnesses")
        prepared.append({"workload": workload, "package": package,
                         "build_measurement": build_measurement, "manifest": manifest,
                         "cost": cost, "assignment_digests": assignment_digests,
                         "trials": []})
        print(f"{name}: package ready", flush=True)
    proof_order = []
    for index in range(args.samples):
        rotated = prepared[index % len(prepared):] + prepared[:index % len(prepared)]
        for item in rotated:
            name = item["workload"]["name"]
            path = output / name / "assignments" / f"{index:02d}.json"
            item["trials"].append(s31.trial(
                item["package"], path, output / name / "trials" / f"{index:02d}"))
            proof_order.append({"program": name, "assignment_index": index})
        print(f"native proof round {index + 1}/{args.samples} verified for all programs", flush=True)
    results = {}
    for item in prepared:
        workload = item["workload"]
        name = workload["name"]
        source = workload["source"]
        manifest = item["manifest"]
        cost = item["cost"]
        results[name] = {
            "family": workload["family"], "source": str(source),
            "source_sha256": s31.file_hash(source),
            "compiler_sha256": manifest["compiler_sha256"],
            "lowering": workload["lowering"], "profile": cost["profile"],
            "visible_fri": s31.visible_fri(cost, workload["lowering"]),
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "package_build": item["build_measurement"],
            "assignment_sha256": item["assignment_digests"],
            "observed_cost_model": observed_cost_model(item["trials"]),
        }
    report = {
        "schema": "s31-multiscale-cost-corpus-v1",
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()},
        "samples_per_program": args.samples,
        "package_build_order": [item["workload"]["name"] for item in prepared],
        "proof_order": proof_order,
        "scope": "Fresh native prover/verifier processes, distinct valid witnesses. Zig compiler cache uncontrolled; all timing is host-local.",
        "cases": results,
    }
    s31.write_json(output / "multiscale-corpus.json", report)
    print(output / "multiscale-corpus.json")


if __name__ == "__main__":
    main()
