#!/usr/bin/env python3
"""Prospective stage-aware cost corpus; train and validation run separately.

The frozen protocol is design/s31/measurements/stage-aware-cost-v1.json. Run
the training split first, fit and save a model, then run the disjoint validation
split. This runner never fits on validation observations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE / "python"))
sys.path.insert(0, str(HERE / "benchmarks"))

import s31
from benchmark_whole_prover import measured_package_build
from benchmark_whole_prover_multiscale import (
    arithmetic_assignment, arithmetic_program, hash_assignment, hash_program,
)
from runtime.cost_model import observed_cost_model

PROTOCOL = ROOT / "design/s31/measurements/stage-aware-cost-v1.json"
SIGNED_WIDTHS = (8, 16, 32, 64)


def signed_words(value: int, width: int) -> list[int]:
    unsigned = value % (1 << width)
    return [(unsigned >> (16 * offset)) & ((1 << min(16, width)) - 1)
            for offset in range((width + 15) // 16)]


def signed_assignment(width: int, index: int, quotient_only: bool) -> dict:
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
        "public_outputs": {"result": expected},
    }


def quotient_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_quotient_cost_v1(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    std::int::limbs(quotient)\n"
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
        s31.write_json(source, arithmetic_program(rounds))
        workloads.append({"name": name, "family": "arithmetic", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [arithmetic_assignment(rounds, seed + i)
                                          for i in range(samples)]})
    for depth in spec["hash_depths"]:
        name = f"hash_{depth}"
        source = source_dir / f"{name}.s31.json"
        s31.write_json(source, hash_program(depth))
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, seed + i)
                                          for i in range(samples)]})
    for width in SIGNED_WIDTHS:
        quotient_only = split == "validation"
        name = f"signed_{'quotient' if quotient_only else 'div_rem'}_{width}"
        if quotient_only:
            source = source_dir / f"{name}.s31"
            source.write_text(quotient_source(width))
        else:
            source = HERE / f"examples/math/division/i{width}_div_rem.s31"
        workloads.append({"name": name, "family": "fixed_width", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [signed_assignment(width, seed + i, quotient_only)
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--model", type=Path, help="frozen training model, required for validation")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    protocol_bytes = PROTOCOL.read_bytes()
    protocol = json.loads(protocol_bytes)
    if protocol["schema"] != "s31-stage-aware-cost-protocol-v1":
        raise ValueError("unrecognized prospective protocol")
    if (args.split == "validation") != (args.model is not None):
        parser.error("--model is required exactly for the validation split")
    model_bytes = args.model.read_bytes() if args.model is not None else None
    frozen_model = json.loads(model_bytes) if model_bytes is not None else None
    if frozen_model is not None:
        if frozen_model.get("schema") != "s31-stage-aware-cost-model-v1":
            raise ValueError("validation requires a fitted stage-aware model")
        if frozen_model.get("protocol_sha256") != hashlib.sha256(protocol_bytes).hexdigest():
            raise ValueError("model was fitted under another protocol")
    samples = protocol["samples_per_program"]
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    prepared = []
    for workload in workload_cases(args.split, output, samples, protocol):
        name = workload["name"]
        source = workload["source"]
        package, build_measurement = measured_package_build(
            source, output / name / "package", workload["lowering"])
        manifest = json.loads((package / "manifest.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
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
                         "build_measurement": build_measurement,
                         "assignment_sha256": digests, "trials": []})
        print(f"{name}: package ready", flush=True)
    compiler_digests = {item["manifest"]["compiler_sha256"] for item in prepared}
    if len(compiler_digests) != 1:
        raise ValueError("compiler source changed during package builds")
    if frozen_model is not None and compiler_digests != {frozen_model["compiler_sha256"]}:
        raise ValueError("compiler source changed since the training model was frozen")
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
            "assignment_sha256": item["assignment_sha256"],
            "trials": [compact_trial(trial) for trial in item["trials"]],
            "observed_cost_model": observed_cost_model(item["trials"]),
        }
    report = {
        "schema": "s31-stage-aware-cost-corpus-v1", "split": args.split,
        "protocol_sha256": hashlib.sha256(protocol_bytes).hexdigest(),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()},
        "samples_per_program": samples,
        "package_build_order": [item["workload"]["name"] for item in prepared],
        "proof_order": proof_order,
        "frozen_model_sha256": hashlib.sha256(model_bytes).hexdigest() if model_bytes is not None else None,
        "scope": "Fresh process and cold native setup per proof; package-build Zig cache uncontrolled. No cached-setup measurement.",
        "cases": cases,
    }
    s31.write_json(output / "stage-aware-corpus.json", report)
    print(output / "stage-aware-corpus.json")


if __name__ == "__main__":
    main()
