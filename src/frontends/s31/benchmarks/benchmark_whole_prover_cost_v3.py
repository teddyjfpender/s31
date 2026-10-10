#!/usr/bin/env python3
"""Prospective four-profile whole-prover cost corpus; splits run separately.

The frozen protocol is design/s31/measurements/whole-prover-cost-v3.json. Run
the training split first, fit and save a model, then run the disjoint validation
split. This runner never fits on validation observations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import random
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE / "python"))
sys.path.insert(0, str(HERE / "benchmarks"))

import s31
from benchmark_whole_prover import measured_package_build
from benchmark_whole_prover_multiscale import (
    hash_assignment, hash_program,
)
from benchmark_arithmetic_rss_v2 import assignment as recurrence_assignment
from benchmark_arithmetic_rss_v2 import program as recurrence_program
from runtime.cost_model import observed_cost_model

PROTOCOL = ROOT / "design/s31/measurements/whole-prover-cost-v3.json"


def host_identity() -> dict:
    """Bind train/validation to one host without publishing its raw hostname."""
    node = platform.node()
    if not node:
        raise ValueError("host identity is unavailable")
    cpu = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"],
                         capture_output=True, text=True, check=False)
    model = cpu.stdout.strip() if cpu.returncode == 0 else platform.processor()
    if not model:
        raise ValueError("CPU model is unavailable")
    return {"host_id_sha256": hashlib.sha256(node.encode()).hexdigest(),
            "cpu_model": model,
            "platform": platform.platform(), "machine": platform.machine(),
            "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()}


def signed_words(value: int, width: int) -> list[int]:
    unsigned = value % (1 << width)
    return [(unsigned >> (16 * offset)) & ((1 << min(16, width)) - 1)
            for offset in range((width + 15) // 16)]


def signed_assignment(width: int, index: int, quotient_only: bool,
                      output_name: str = "result") -> dict:
    rng = random.Random(0x531C057 + width * 1_000_003 + index)
    limit = 1 << (width - 1)
    numerator = rng.randrange(-limit + 1, limit)
    divisor = rng.randrange(1, limit)
    if index & 1:
        divisor = -divisor
    quotient = abs(numerator) // abs(divisor)
    if (numerator < 0) != (divisor < 0):
        quotient = -quotient
    remainder = numerator - quotient * divisor
    expected = signed_words(quotient, width)
    if not quotient_only:
        expected += signed_words(remainder, width)
    return {
        "public_inputs": {},
        "private_inputs": {"numerator": signed_words(numerator, width),
                           "divisor": signed_words(divisor, width)},
        "public_outputs": {output_name: expected},
    }


def quotient_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_quotient_cost_v1(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    let result = std::int::limbs(quotient);\n"
            f"    result\n"
            f"}}\n")


def workload_cases(split: str, output: Path, samples: int, protocol: dict) -> list[dict]:
    spec = protocol["splits"][split]
    source_dir = output / "generated-sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    workloads = []
    seed = spec["assignment_index_base"]
    for rounds in spec["arithmetic_rounds"]:
        name = f"arithmetic_{rounds}"
        source = source_dir / f"{name}.s31.json"
        body = [{"op": "square"}, {"op": "add_const", "constant": spec["arithmetic_constant"]}]
        s31.write_json(source, recurrence_program(name, rounds, body))
        workloads.append({"name": name, "family": "arithmetic", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [recurrence_assignment(rounds, body, seed + i)
                                          for i in range(samples)]})
    for rounds in spec["chip_rounds"]:
        name = f"chip_{rounds}"
        source = source_dir / f"{name}.s31.json"
        body = [{"op": "square"}, {"op": "add_const", "constant": spec["chip_constant"]}]
        s31.write_json(source, recurrence_program(name, rounds, body))
        workloads.append({"name": name, "family": "chip", "source": source,
                          "lowering": "direct-chip",
                          "assignments": [recurrence_assignment(rounds, body, seed + 100000 + i)
                                          for i in range(samples)]})
    for depth in spec["hash_depths"]:
        name = f"hash_{depth}"
        source = source_dir / f"{name}.s31.json"
        s31.write_json(source, hash_program(depth))
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, seed + i)
                                          for i in range(samples)]})
    for width in spec["signed_widths"]:
        quotient_only = split == "validation"
        name = f"signed_{'quotient' if quotient_only else 'div_rem'}_{width}"
        if quotient_only:
            source = source_dir / f"{name}.s31"
            source.write_text(quotient_source(width))
        else:
            source = HERE / f"examples/math/division/i{width}_div_rem.s31"
        from package.context import lower_text
        relation, _, _ = lower_text(source)
        if len(relation["public_outputs"]) != 1:
            raise ValueError(f"{name}: expected one public output")
        output_name = relation["public_outputs"][0]
        workloads.append({"name": name, "family": "fixed_width", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [signed_assignment(width, seed + i, quotient_only,
                                                            output_name)
                                          for i in range(samples)]})
    return workloads


def compact_trial(trial: dict) -> dict:
    """Retain raw observations and proof binding without duplicating audit files."""
    return {key: trial[key] for key in (
        "proof_sha256", "proof_bytes", "native_verifier_accepted",
        "changed_public_statement_rejected", "independent_value_oracle",
        "prove_seconds", "prover_stages", "prover_peak_rss_bytes",
        "prover_peak_rss_method", "verify_seconds", "verifier_peak_rss_bytes",
        "verifier_peak_rss_method")}


def chip_manifest_binding(package: Path) -> dict:
    """Require the generated, sealed one-call typed component manifest."""
    component = json.loads((package / "component-manifest.json").read_text())
    key = json.loads((package / "verification-key.json").read_text())
    package_manifest = json.loads((package / "manifest.json").read_text())
    call = component.get("chip_call")
    if (component.get("schema") != "s31-component-manifest-direct-chip-v2" or
        not isinstance(call, dict) or call.get("call_id") != 0 or
        key.get("schema") != "s31-verification-key-direct-chip-manifest-v2" or
        key.get("component_manifest") != component or
        "component-manifest.json" not in package_manifest.get("artifacts", {})):
        raise ValueError("direct-chip package lacks generated sealed one-call manifest")
    geometry = [{key: item[key] for key in (
        "name", "trace_log_size", "base_trace_columns", "interaction_trace_columns")}
        for item in component["components"]]
    if ([item["name"] for item in geometry] != ["qm31_ops", "repeated_step_chip"] or
        any(type(item["trace_log_size"]) is not int or item["trace_log_size"] < 0 or
            item["trace_log_size"] > 24 or
            any(type(item[key]) is not int or item[key] <= 0
                for key in ("base_trace_columns", "interaction_trace_columns"))
            for item in geometry) or
        1 << geometry[1]["trace_log_size"] != call.get("rounds")):
        raise ValueError("direct-chip package has invalid component geometry")
    rows = [1 << item["trace_log_size"] for item in geometry]
    return {"schema": component["schema"], "chip_call": call,
            "component_geometry": geometry,
            "chip_trace_cells": sum(row * (item["base_trace_columns"] +
                                           item["interaction_trace_columns"])
                                    for row, item in zip(rows, geometry)),
            "chip_fri_domain_rows": max(rows),
            "manifest_precommitment_sha256": key["manifest_precommitment_sha256"],
            "component_manifest_sha256": s31.file_hash(package / "component-manifest.json")}


def run_corpus(args: argparse.Namespace, *, protocol_path: Path, protocol_schema: str,
               model_schema: str, corpus_schema: str, build_schema: str,
               workloads: object) -> None:
    """Shared artifact collection; each prospective study supplies its frozen protocol."""
    protocol_bytes = protocol_path.read_bytes()
    protocol = json.loads(protocol_bytes)
    if protocol["schema"] != protocol_schema:
        raise ValueError("unrecognized prospective protocol")
    if (args.split == "validation") != (args.model is not None):
        raise ValueError("--model is required exactly for the validation split")
    model_bytes = args.model.read_bytes() if args.model is not None else None
    frozen_model = json.loads(model_bytes) if model_bytes is not None else None
    if frozen_model is not None:
        if frozen_model.get("schema") != model_schema:
            raise ValueError("validation requires a fitted stage-aware model")
        if frozen_model.get("protocol_sha256") != hashlib.sha256(protocol_bytes).hexdigest():
            raise ValueError("model was fitted under another protocol")
    samples = protocol["samples_per_program"]
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    prepared = []
    for workload in workloads(args.split, output, samples, protocol):
        name = workload["name"]
        source = workload["source"]
        package_path = output / name / "package"
        build_record_path = output / name / "package-build-record.json"
        if args.phase == "prove":
            build_record = json.loads(build_record_path.read_text())
            if build_record["source_sha256"] != s31.file_hash(source):
                raise ValueError(f"{name}: source changed since package build phase")
            package = s31.build(source, package_path, workload["lowering"])
            build_measurement = build_record["package_build"]
        else:
            package, build_measurement = measured_package_build(
                source, package_path, workload["lowering"])
        manifest = json.loads((package / "manifest.json").read_text())
        if args.phase == "prove":
            if build_record["compiler_sha256"] != manifest["compiler_sha256"]:
                raise ValueError(f"{name}: compiler changed since package build phase")
        else:
            s31.write_json(build_record_path, {
                "source_sha256": s31.file_hash(source),
                "compiler_sha256": manifest["compiler_sha256"],
                "package_build": build_measurement,
            })
        cost = json.loads((package / "cost-report.json").read_text())
        chip_binding = chip_manifest_binding(package) if workload["family"] == "chip" else None
        digests = []
        for index, assignment in enumerate(workload["assignments"]):
            path = output / name / "assignments" / f"{index:02d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(path, assignment)
            digests.append(s31.assignment_digest(path))
        if len(set(digests)) != samples:
            raise ValueError(f"{name}: non-distinct assignments")
        prepared.append({"workload": workload, "package": package,
                         "manifest": manifest, "cost": cost,
                         "chip_manifest_binding": chip_binding,
                         "build_measurement": build_measurement,
                         "assignment_sha256": digests, "trials": []})
        print(f"{name}: package ready", flush=True)
    compiler_digests = {item["manifest"]["compiler_sha256"] for item in prepared}
    if len(compiler_digests) != 1:
        raise ValueError("compiler source changed during package builds")
    if frozen_model is not None and compiler_digests != {frozen_model["compiler_sha256"]}:
        raise ValueError("compiler source changed since the training model was frozen")
    if args.phase == "build":
        s31.write_json(output / "whole-prover-build-inventory.json", {
            "schema": build_schema, "split": args.split,
            "protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
            "compiler_sha256": next(iter(compiler_digests)),
            "programs": {item["workload"]["name"]: {
                "source_sha256": s31.file_hash(item["workload"]["source"]),
                "chip_manifest_binding": item["chip_manifest_binding"],
                "package_build": item["build_measurement"],
            } for item in prepared},
        })
        print(output / "whole-prover-build-inventory.json")
        return
    proof_order = []
    for index in range(samples):
        rotated = prepared[index % len(prepared):] + prepared[:index % len(prepared)]
        for item in rotated:
            name = item["workload"]["name"]
            assignment = output / name / "assignments" / f"{index:02d}.json"
            trial = s31.trial(item["package"], assignment,
                              output / name / "trials" / f"{index:02d}")
            if trial["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}[{index}]: independent value oracle unavailable")
            item["trials"].append(trial)
            proof_order.append({"program": name, "assignment_index": index})
        print(f"native proof round {index + 1}/{samples} verified for all programs", flush=True)
    cases = {}
    for item in prepared:
        workload = item["workload"]
        source = workload["source"]
        cost = item["cost"]
        cases[workload["name"]] = {
            "family": workload["family"], "source": str(source),
            "source_sha256": s31.file_hash(source),
            "compiler_sha256": item["manifest"]["compiler_sha256"],
            "lowering": workload["lowering"], "profile": cost["profile"],
            "visible_fri": s31.visible_fri(cost, workload["lowering"]),
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "package_build": item["build_measurement"],
            "chip_manifest_binding": item["chip_manifest_binding"],
            "assignment_sha256": item["assignment_sha256"],
            "trials": [compact_trial(trial) for trial in item["trials"]],
            "observed_cost_model": observed_cost_model(item["trials"]),
        }
    report = {
        "schema": corpus_schema, "split": args.split,
        "protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
        "host": host_identity(),
        "samples_per_program": samples,
        "package_build_order": [item["workload"]["name"] for item in prepared],
        "proof_order": proof_order,
        "frozen_model_sha256": hashlib.sha256(model_bytes).hexdigest() if model_bytes is not None else None,
        "scope": "Fresh process and cold native setup per proof; package-build Zig cache uncontrolled. No cached-setup measurement.",
        "cases": cases,
    }
    s31.write_json(output / "whole-prover-corpus.json", report)
    print(output / "whole-prover-corpus.json")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove", "all"), default="all")
    parser.add_argument("--model", type=Path, help="frozen training model, required for validation")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run_corpus(args, protocol_path=PROTOCOL,
               protocol_schema="s31-whole-prover-cost-protocol-v3.1",
               model_schema="s31-whole-prover-cost-model-v3.1",
               corpus_schema="s31-whole-prover-cost-corpus-v3.1",
               build_schema="s31-whole-prover-build-inventory-v3",
               workloads=workload_cases)


if __name__ == "__main__":
    main()
