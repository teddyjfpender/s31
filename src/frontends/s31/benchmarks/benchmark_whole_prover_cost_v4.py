#!/usr/bin/env python3
"""Collect fresh v4 train/held-out packages and native proof trials."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmark_whole_prover_cost_v3 import (
    HERE, hash_assignment, hash_program, quotient_source, recurrence_assignment,
    recurrence_program, run_corpus, s31, signed_assignment,
)

PROTOCOL = HERE.parents[2] / "design/s31/measurements/whole-prover-cost-v4.json"
TOOL_SOURCES = (tuple(sorted((HERE / "benchmarks").glob("*.py"))) +
                tuple(sorted((HERE / "python").rglob("*.py"))))


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
        relation["name"] = f"blake_chain_v4_{depth}"
        s31.write_json(source, relation)
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, seed + i)
                                          for i in range(samples)]})
    for width in spec["signed_widths"]:
        quotient_only = split == "validation"
        name = f"signed_{'quotient' if quotient_only else 'div_rem'}_{width}"
        source = source_dir / f"{name}.s31"
        if quotient_only:
            source.write_text(quotient_source(width).replace("_cost_v1", "_cost_v4"))
        else:
            original = HERE / f"examples/math/division/i{width}_div_rem.s31"
            source.write_text(original.read_text().replace(
                f"circuit i{width}_div_rem(", f"circuit i{width}_div_rem_cost_v4("))
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove", "all"), default="all")
    parser.add_argument("--model", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    run_corpus(parser.parse_args(), protocol_path=PROTOCOL,
               protocol_schema="s31-whole-prover-cost-protocol-v4",
               model_schema="s31-whole-prover-cost-model-v4",
               corpus_schema="s31-whole-prover-cost-corpus-v4",
               build_schema="s31-whole-prover-build-inventory-v4",
               workloads=workload_cases, tool_sources=TOOL_SOURCES)


if __name__ == "__main__":
    main()
