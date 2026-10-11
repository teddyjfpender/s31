#!/usr/bin/env python3
"""Generate the predeclared independent arithmetic RSS train/validation corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE / "python"))
sys.path.insert(0, str(HERE / "benchmarks"))

import s31
from benchmark_whole_prover import measured_package_build
from benchmark_whole_prover_stage_v1 import compact_trial
from runtime.cost_model import observed_cost_model

PROTOCOL = ROOT / "design/s31/measurements/arithmetic-rss-v2.json"
P = (1 << 31) - 1


def program(name: str, rounds: int, body: list[dict]) -> dict:
    return {
        "version": 1, "name": name,
        "inputs": [{"name": "x", "kind": "m31", "length": 4, "visibility": "public"}],
        "nodes": [{"name": "result", "op": "repeat", "lhs": "x", "rounds": rounds,
                   "body": body}],
        "assertions": [], "public_outputs": ["result"],
    }


def assignment(rounds: int, body: list[dict], index: int) -> dict:
    values = [1 + 17 * index, 2 + 31 * index, 3 + 47 * index, 511 + 59 * index]
    result = values.copy()
    for _ in range(rounds):
        for step in body:
            if step["op"] == "square":
                result = [(value * value) % P for value in result]
            elif step["op"] == "add_const":
                result = [(value + step["constant"]) % P for value in result]
            elif step["op"] == "mul_const":
                result = [(value * step["constant"]) % P for value in result]
            else:
                raise ValueError(f"unsupported benchmark step {step['op']}")
    return {"public_inputs": {"x": values}, "private_inputs": {},
            "public_outputs": {"result": result}}


def workloads(split: str, output: Path, protocol: dict) -> list[dict]:
    source_dir = output / "generated-sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    spec = protocol[split]
    entries = ([(rounds, "train", spec["body"]) for rounds in spec["rounds"]]
               if split == "train" else
               [(rounds, body_name, body)
                for body_name, body in spec["bodies"].items()
                for rounds in spec["rounds"]])
    cases = []
    for rounds, body_name, body in entries:
        name = f"arith_rss_{body_name}_{rounds}"
        source = source_dir / f"{name}.s31.json"
        s31.write_json(source, program(name, rounds, body))
        cases.append({"name": name, "source": source,
                      "assignments": [assignment(rounds, body,
                                                 spec["assignment_index_base"] + i)
                                      for i in range(protocol["samples_per_program"])]})
    return cases


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove"), required=True)
    parser.add_argument("--model", type=Path, help="frozen training model for validation")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if (args.split == "validation") != (args.model is not None):
        parser.error("--model is required exactly for validation")
    protocol_bytes = PROTOCOL.read_bytes()
    protocol = json.loads(protocol_bytes)
    if protocol["schema"] != "s31-arithmetic-rss-protocol-v2":
        raise ValueError("unrecognized arithmetic RSS protocol")
    model_bytes = args.model.read_bytes() if args.model is not None else None
    frozen_model = json.loads(model_bytes) if model_bytes is not None else None
    if frozen_model is not None:
        if frozen_model.get("schema") != "s31-arithmetic-rss-model-v2":
            raise ValueError("validation needs the frozen arithmetic RSS model")
        if frozen_model.get("protocol_sha256") != hashlib.sha256(protocol_bytes).hexdigest():
            raise ValueError("model/protocol mismatch")
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    prepared = []
    for workload in workloads(args.split, output, protocol):
        name = workload["name"]
        source = workload["source"]
        package_path = output / name / "package"
        record_path = output / name / "package-build-record.json"
        if args.phase == "build":
            package, build_measurement = measured_package_build(source, package_path, "direct-gate")
        else:
            record = json.loads(record_path.read_text())
            if record["source_sha256"] != s31.file_hash(source):
                raise ValueError(f"{name}: source changed since build")
            package = s31.build(source, package_path, "direct-gate")
            build_measurement = record["package_build"]
        manifest = json.loads((package / "manifest.json").read_text())
        if args.phase == "build":
            s31.write_json(record_path, {"source_sha256": s31.file_hash(source),
                                          "compiler_sha256": manifest["compiler_sha256"],
                                          "package_build": build_measurement})
        elif record["compiler_sha256"] != manifest["compiler_sha256"]:
            raise ValueError(f"{name}: compiler changed since build")
        cost = json.loads((package / "cost-report.json").read_text())
        assignment_digests = []
        for index, value in enumerate(workload["assignments"]):
            path = output / name / "assignments" / f"{index:02d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(path, value)
            assignment_digests.append(s31.assignment_digest(path))
        if len(set(assignment_digests)) != protocol["samples_per_program"]:
            raise ValueError(f"{name}: non-distinct assignments")
        prepared.append({"workload": workload, "package": package,
                         "manifest": manifest, "cost": cost,
                         "build_measurement": build_measurement,
                         "assignment_sha256": assignment_digests, "trials": []})
        print(f"{name}: package ready", flush=True)
    compiler_digests = {item["manifest"]["compiler_sha256"] for item in prepared}
    if len(compiler_digests) != 1:
        raise ValueError("mixed compiler fingerprints")
    compiler_sha = next(iter(compiler_digests))
    if frozen_model is not None and compiler_sha != frozen_model["compiler_sha256"]:
        raise ValueError("compiler changed since training model was frozen")
    if args.phase == "build":
        s31.write_json(output / "build-inventory.json", {
            "schema": "s31-arithmetic-rss-build-inventory-v2", "split": args.split,
            "protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
            "compiler_sha256": compiler_sha,
            "programs": {item["workload"]["name"]: item["build_measurement"]
                         for item in prepared},
        })
        print(output / "build-inventory.json")
        return
    proof_order = []
    for index in range(protocol["samples_per_program"]):
        rotated = prepared[index % len(prepared):] + prepared[:index % len(prepared)]
        for item in rotated:
            name = item["workload"]["name"]
            path = output / name / "assignments" / f"{index:02d}.json"
            trial = s31.trial(item["package"], path,
                              output / name / "trials" / f"{index:02d}")
            if trial["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}[{index}]: independent oracle unavailable")
            item["trials"].append(trial)
            proof_order.append({"program": name, "assignment_index": index})
        print(f"native proof round {index + 1}/{protocol['samples_per_program']} verified", flush=True)
    cases = {}
    for item in prepared:
        workload = item["workload"]
        name = workload["name"]
        cost = item["cost"]
        cases[name] = {
            "source": str(workload["source"]),
            "source_sha256": s31.file_hash(workload["source"]),
            "compiler_sha256": item["manifest"]["compiler_sha256"],
            "lowering": "direct-gate", "profile": cost["profile"],
            "visible_fri": s31.visible_fri(cost, "direct-gate"),
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "package_build": item["build_measurement"],
            "assignment_sha256": item["assignment_sha256"],
            "trials": [compact_trial(trial) for trial in item["trials"]],
            "observed_cost_model": observed_cost_model(item["trials"]),
        }
    s31.write_json(output / "arithmetic-rss-corpus.json", {
        "schema": "s31-arithmetic-rss-corpus-v2", "split": args.split,
        "protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
        "frozen_model_sha256": hashlib.sha256(model_bytes).hexdigest() if model_bytes is not None else None,
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()},
        "compiler_sha256": compiler_sha,
        "samples_per_program": protocol["samples_per_program"],
        "package_build_order": [item["workload"]["name"] for item in prepared],
        "proof_order": proof_order,
        "cases": cases,
    })
    print(output / "arithmetic-rss-corpus.json")


if __name__ == "__main__":
    main()
