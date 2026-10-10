#!/usr/bin/env python3
"""Collect fresh v5 packages only after explicit source/tool fingerprint freeze."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

from benchmark_whole_prover_cost_v3 import (
    HERE, ROOT, hash_assignment, hash_program, measurement_tool_digest,
    quotient_source, recurrence_assignment, recurrence_program, run_corpus,
    s31, signed_assignment,
)

PROTOCOL = HERE.parents[2] / "design/s31/measurements/whole-prover-cost-v5.json"
TOOL_SOURCES = (tuple(sorted((HERE / "benchmarks").glob("*.py"))) +
                tuple(sorted((HERE / "python").rglob("*.py"))))


def div_rem_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_div_rem_cost_v5(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {2 * count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    let result = std::array::concat(std::int::limbs(quotient), "
            f"std::int::limbs(remainder));\n"
            f"    result\n"
            f"}}\n")


def remainder_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_remainder_cost_v5(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    let result = std::int::limbs(remainder);\n"
            f"    result\n"
            f"}}\n")


def remainder_assignment(width: int, index: int, output_name: str) -> dict:
    assignment = signed_assignment(width, index, False, output_name)
    count = (width + 15) // 16
    assignment["public_outputs"][output_name] = assignment["public_outputs"][output_name][count:]
    return assignment


def require_frozen_pins(protocol: dict) -> None:
    """Refuse native observation while the prospective source/tool pin is draft."""
    for key in ("source_base_commit", "engine_gitlink_commit", "compiler_sha256",
                "measurement_tool_sha256"):
        if not re.fullmatch(r"[0-9a-f]{40}" if key.endswith("commit") else
                            r"[0-9a-f]{64}", protocol.get(key) or ""):
            raise ValueError(f"v5 {key} must be pinned before a native build or trial")
    if protocol.get("status") != "frozen-before-any-v5-native-observation":
        raise ValueError("v5 protocol status must record the prospective native freeze")
    if protocol["measurement_tool_sha256"] != measurement_tool_digest(TOOL_SOURCES):
        raise ValueError("v5 pinned measurement tool digest differs from source bytes")
    if protocol["compiler_sha256"] != s31.compiler_fingerprint():
        raise ValueError("v5 pinned compiler digest differs from source bytes")
    engine = subprocess.check_output(
        ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
        text=True).strip()
    if engine != protocol["engine_gitlink_commit"]:
        raise ValueError("v5 pinned engine gitlink differs from checkout")
    source_base = subprocess.run(
        ["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
         protocol["source_base_commit"], "HEAD"], check=False)
    if source_base.returncode != 0:
        raise ValueError("v5 pinned S31 source base is not an ancestor of this checkout")


def workload_cases(split: str, output: Path, samples: int, protocol: dict) -> list[dict]:
    spec = protocol["splits"][split]
    source_dir = output / "generated-sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    seed = spec["assignment_index_base"]
    workloads = []
    for family, key, lowering, offset in (
        ("arithmetic", "arithmetic_rounds", "direct-gate", 0),
        ("chip", "chip_rounds", "direct-chip", 100000),
    ):
        for rounds in spec[key]:
            if family == "chip" and (rounds < 16 or rounds > 32768 or
                                     rounds & (rounds - 1)):
                raise ValueError("direct-chip rounds must be powers of two from 16 to 32768")
            name = f"{family}_{rounds}"
            source = source_dir / f"{name}.s31.json"
            body = [{"op": "square"}, {"op": "add_const",
                                       "constant": spec[f"{family}_constant"]}]
            s31.write_json(source, recurrence_program(name, rounds, body))
            workloads.append({"name": name, "family": family, "source": source,
                              "lowering": lowering,
                              "assignments": [recurrence_assignment(rounds, body, seed + offset + i)
                                              for i in range(samples)]})
    for depth in spec["hash_depths"]:
        name = f"hash_{depth}"
        source = source_dir / f"{name}.s31.json"
        relation = hash_program(depth)
        relation["name"] = f"blake_chain_v5_{depth}"
        s31.write_json(source, relation)
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, seed + i)
                                          for i in range(samples)]})
    for width in spec["signed_widths"]:
        kind = (spec["signed_128_output"] if width == 128 else
                "quotient" if split == "validation" else "div_rem")
        name = f"signed_{kind}_{width}"
        source = source_dir / f"{name}.s31"
        if kind == "quotient":
            source.write_text(quotient_source(width).replace("_cost_v1", "_cost_v5"))
        elif kind == "remainder":
            source.write_text(remainder_source(width))
        else:
            source.write_text(div_rem_source(width))
        from package.context import lower_text

        relation, _, _ = lower_text(source)
        if len(relation["public_outputs"]) != 1:
            raise ValueError(f"{name}: expected one public output")
        output_name = relation["public_outputs"][0]
        workloads.append({"name": name, "family": "fixed_width", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [(remainder_assignment(width, seed + i, output_name)
                                           if kind == "remainder" else
                                           signed_assignment(width, seed + i,
                                                             kind == "quotient", output_name))
                                          for i in range(samples)]})
    return workloads


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove", "all"), default="all")
    parser.add_argument("--model", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text())
    require_frozen_pins(protocol)
    if shutil.disk_usage(ROOT).free < protocol["minimum_available_disk_bytes_before_native_phase"]:
        raise ValueError("v5 native phase needs at least eight GiB of free artifact space")
    run_corpus(args, protocol_path=PROTOCOL,
               protocol_schema="s31-whole-prover-cost-protocol-v5",
               model_schema="s31-whole-prover-cost-model-v5",
               corpus_schema="s31-whole-prover-cost-corpus-v5",
               build_schema="s31-whole-prover-build-inventory-v5",
               workloads=workload_cases, tool_sources=TOOL_SOURCES)


if __name__ == "__main__":
    main()
