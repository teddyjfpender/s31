#!/usr/bin/env python3
"""Pair native direct and sparse-wide checked-add proofs on the same inputs."""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks" / "fixed_integer_cost"))

import s31
from evidence import analyze
from oracle import evaluate_relation
from paired_tune import tune_interleaved
from text_frontend import compile_text
from validate import PROFILE_FIELDS, host_identity, validate


KINDS = tuple(f"{sign}{width}" for sign in ("u", "i")
              for width in (8, 16, 32, 64, 128))


def limbs(value: int, width: int) -> list[int]:
    pattern = value & ((1 << width) - 1)
    return [(pattern >> (16 * index)) & 0xffff
            for index in range(max(1, width // 16))]


def corpus(kind: str, count: int, seed: int) -> list[tuple[int, int]]:
    if count < 5:
        raise ValueError("count must include at least five distinct witnesses")
    width = int(kind[1:])
    signed = kind.startswith("i")
    lower = -(1 << (width - 1)) if signed else 0
    upper = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    initial = [(0, 0), (upper - 1, 1), (lower, 0), (1, 0)]
    if width > 16:
        initial.append(((1 << 16) - 1, 1))
    else:
        initial.append((upper // 2, 1))
    cases = list(dict.fromkeys(initial))
    rng = random.Random(seed)
    while len(cases) < count:
        a = rng.randint(lower, upper)
        b = rng.randint(lower, upper)
        if not lower <= a + b <= upper or (a, b) in cases:
            continue
        cases.append((a, b))
    return cases


def run(kind: str, count: int, seed: int, output: Path) -> dict:
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    compiler_sha256 = s31.compiler_fingerprint()
    host = host_identity()
    width = int(kind[1:])
    source = output / f"{kind}_checked_add.s31"
    source.write_text(
        f"use std@1;\ncircuit {kind}_checked_add(private a: {kind}, private b: {kind}) "
        f"-> public {kind} {{ std::int::add_checked(a, b) }}\n")
    relation, _ = compile_text(source.read_text(), str(source))
    result_name = relation["public_outputs"][0]
    assignments = []
    for index, (a, b) in enumerate(corpus(kind, count, seed)):
        value = {"public_inputs": {},
                 "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
                 "public_outputs": {result_name: limbs(a + b, width)}}
        if evaluate_relation(relation, value) != value["public_outputs"]:
            raise AssertionError(f"independent integer oracle failed at case {index}")
        path = output / "assignments" / f"{index:03d}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        s31.write_json(path, value)
        assignments.append(path)
    report = tune_interleaved(source, assignments, output / "tune",
                              ("direct-gate", "sparse-wide-gate"))
    if s31.compiler_fingerprint() != compiler_sha256 or host_identity() != host:
        raise AssertionError("compiler or host identity changed during paired measurement")
    profiles = report["profiles"]
    if (set(profiles) != {"direct-gate", "sparse-wide-gate"} or
            report["distinct_assignment_count"] != count or
            not report["distinct_assignments"] or
            report["same_visible_fri_settings"] is not True or
            not all(profile["native_verifier_accepted_all"] and
                    profile["changed_public_statement_rejected_all"] and
                    profile["independent_value_oracle_statuses"] == ["passed"] * count
                    for profile in profiles.values())):
        raise AssertionError("paired profile audit failed")
    concise = {
        "schema": "s31-fixed-addition-paired-v2",
        "kind": kind, "count": count, "seed": seed,
        "compiler_sha256": compiler_sha256,
        "host": host,
        "source_sha256": s31.file_hash(source),
        "program_sha256": report["program_sha256"],
        "canonical_ir_sha256": report["canonical_ir_sha256"],
        "assignment_sha256": report["assignment_sha256"],
        "same_visible_fri_settings": report["same_visible_fri_settings"],
        "profiles": {
            name: {field: profile[field] for field in PROFILE_FIELDS}
            for name, profile in profiles.items()
        },
        "limitations": ("One host and one program; native setup is cold in every fresh "
                        "prover process. Paired profile order alternates by assignment, "
                        "while transcript proof-of-work and external load still vary. "
                        "Equal visible FRI settings do not establish equal soundness."),
    }
    s31.write_json(output / "summary.json", concise)
    validate(output)
    analyze(output)
    return concise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=KINDS)
    parser.add_argument("--count", type=int, default=20)
    parser.add_argument("--seed", type=int, default=0x531ADD)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.kind, args.count, args.seed, args.out),
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
