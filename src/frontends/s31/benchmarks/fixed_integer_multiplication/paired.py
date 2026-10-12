#!/usr/bin/env python3
"""Pair native checked-multiply proofs on identical seeded integer witnesses."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks" / "fixed_integer_cost"))

import s31
from evidence import analyze, host_identity
from oracle import OracleError, evaluate_relation
from paired_tune import tune_interleaved
from text_frontend import compile_text


KINDS = tuple(f"{sign}{width}" for sign in ("u", "i")
              for width in (8, 16, 32, 64, 128))
LOWERINGS = ("direct-gate", "sparse-wide-gate")


def limbs(value: int, width: int) -> list[int]:
    pattern = value & ((1 << width) - 1)
    return [(pattern >> (16 * index)) & 0xffff
            for index in range(max(1, width // 16))]


def bounds(kind: str) -> tuple[int, int]:
    width = int(kind[1:])
    return ((-(1 << (width - 1)), (1 << (width - 1)) - 1) if kind.startswith("i")
            else (0, (1 << width) - 1))


def corpus(kind: str, count: int, seed: int) -> list[tuple[int, int]]:
    """Edge cases plus deterministic, distinct, in-range products."""
    if kind not in KINDS or count < 5 or count > 256:
        raise ValueError("expected a supported kind and 5..256 distinct witnesses")
    width = int(kind[1:])
    minimum, maximum = bounds(kind)
    if kind.startswith("i"):
        initial = [(0, 0), (1, 1), (minimum, 1), (maximum, 1), (-3, 7),
                   (maximum // 2, 2), (minimum // 2, 2), (-1, -1)]
    else:
        cross = ((17, 13) if width == 8 else
                 (255, 255) if width == 16 else (255, 258))
        initial = [(0, 0), (1, 1), (maximum, 1), (maximum // 2, 2), cross,
                   (0, maximum), (maximum, 0), (3, 7)]
    cases = list(dict.fromkeys(initial[:count]))
    rng = random.Random(seed)
    attempts = 0
    while len(cases) < count:
        attempts += 1
        if attempts > 100_000:
            raise RuntimeError("could not generate distinct in-range multiplication corpus")
        if rng.randrange(2):
            a = rng.randint(minimum, maximum)
            b = rng.randint(-8 if kind.startswith("i") else 0, 8)
        else:
            budget = width - 1 if kind.startswith("i") else width
            a_bits = rng.randrange(budget + 1)
            b_bits = budget - a_bits
            a, b = rng.getrandbits(a_bits), rng.getrandbits(b_bits)
            if kind.startswith("i"):
                a *= -1 if rng.randrange(2) else 1
                b *= -1 if rng.randrange(2) else 1
        if minimum <= a * b <= maximum and (a, b) not in cases:
            cases.append((a, b))
    if len(cases) != len(set(cases)) or any(
            not minimum <= a * b <= maximum for a, b in cases):
        raise AssertionError("corpus is not distinct and in range")
    return cases


def assignment(kind: str, a: int, b: int, output: str) -> dict:
    width = int(kind[1:])
    return {"public_inputs": {},
            "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
            "public_outputs": {output: limbs(a * b, width)}}


def overflow_case(kind: str) -> tuple[int, int]:
    minimum, maximum = bounds(kind)
    return ((minimum, -1) if kind.startswith("i") else (maximum, 2))


def prepare(kind: str, count: int, seed: int, output: Path) -> tuple[Path, list[Path], Path]:
    output.mkdir(parents=True, exist_ok=True)
    source = output / f"{kind}_checked_mul.s31"
    source.write_text(
        f"use std@1;\ncircuit {kind}_checked_mul(private a: {kind}, private b: {kind}) "
        f"-> public {kind} {{ std::int::mul_checked(a, b) }}\n")
    relation, _ = compile_text(source.read_text(), str(source))
    width = int(kind[1:])
    spec = width | (256 if kind.startswith("i") else 0)
    if ([node["op"] for node in relation["nodes"]] !=
            ["int_view", "int_view", "int_mul_checked"] or
            any(node.get("constant") != spec for node in relation["nodes"])):
        raise AssertionError("checked multiplication relation shape or width tag changed")
    result = relation["public_outputs"][0]
    assignments: list[Path] = []
    for index, (a, b) in enumerate(corpus(kind, count, seed)):
        claim = assignment(kind, a, b, result)
        if evaluate_relation(relation, claim) != claim["public_outputs"]:
            raise AssertionError(f"independent multiplication oracle failed at case {index}")
        path = output / "assignments" / f"{index:03d}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        s31.write_json(path, claim)
        assignments.append(path)
    overflow = assignment(kind, *overflow_case(kind), result)
    try:
        evaluate_relation(relation, overflow)
    except OracleError as exc:
        if "overflow" not in str(exc):
            raise AssertionError("overflow oracle rejected for another reason") from exc
    else:
        raise AssertionError("independent oracle accepted checked multiplication overflow")
    overflow_path = output / "overflow.json"
    s31.write_json(overflow_path, overflow)
    return source, assignments, overflow_path


def run(kind: str, count: int, seed: int, output: Path) -> dict:
    output = output.resolve()
    compiler_sha = s31.compiler_fingerprint()
    host = host_identity()
    source, assignments, overflow = prepare(kind, count, seed, output)
    report = tune_interleaved(source, assignments, output / "tune", LOWERINGS)
    profiles = report["profiles"]
    if (set(profiles) != set(LOWERINGS) or
            report["distinct_assignment_count"] != count or
            not report["distinct_assignments"] or
            len(report["assignment_sha256"]) != count or
            any(not profile["native_verifier_accepted_all"] or
                not profile["changed_public_statement_rejected_all"] or
                profile["independent_value_oracle_statuses"] != ["passed"] * count
                for profile in profiles.values())):
        raise AssertionError("paired native proof, verifier, or oracle controls failed")
    if s31.compiler_fingerprint() != compiler_sha or host_identity() != host:
        raise AssertionError("compiler or host identity changed during paired measurement")
    overflow_controls: dict[str, bool] = {}
    for lowering in LOWERINGS:
        package = Path(profiles[lowering]["package"])
        manifest = json.loads((package / "manifest.json").read_text())
        if (manifest["compiler_sha256"] != compiler_sha or
                manifest["program_sha256"] != report["program_sha256"] or
                manifest["canonical_ir_sha256"] != report["canonical_ir_sha256"]):
            raise AssertionError(f"{lowering}: package compiler or relation identity drifted")
        prover = package / "bin" / f"s31-{kind}_checked_mul-prover"
        if not prover.is_file():
            raise AssertionError(f"{lowering}: prover missing")
        proof = output / f"{lowering}-overflow.proof"
        proof.unlink(missing_ok=True)
        rejected = subprocess.run([str(prover), "prove", str(overflow), str(proof)],
                                  capture_output=True, text=True, timeout=120)
        if rejected.returncode == 0:
            raise AssertionError(f"{lowering}: native prover accepted overflowing product")
        overflow_controls[lowering] = True
    concise = {
        "schema": "s31-fixed-multiplication-paired-v2",
        "kind": kind, "count": count, "seed": seed,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "program_sha256": report["program_sha256"],
        "canonical_ir_sha256": report["canonical_ir_sha256"],
        "compiler_sha256": compiler_sha,
        "assignment_sha256": report["assignment_sha256"],
        "distinct_assignment_count": report["distinct_assignment_count"],
        "source_arithmetic_oracle_passed_all": True,
        "checked_overflow_oracle_rejected": True,
        "independent_value_oracle_provenance": report["independent_value_oracle_provenance"],
        "same_visible_fri_settings": report["same_visible_fri_settings"],
        "host": host,
        "tune_timing_note": report["timing_note"],
        "profiles": {
            name: {**{field: profile[field] for field in (
                "profile", "visible_fri", "raw", "padded", "preprocessed_cells",
                "proof_bytes_per_assignment", "median_proof_bytes",
                "wall_prove_seconds_per_assignment", "median_wall_prove_seconds",
                "median_prove_excluding_pow_seconds", "median_native_verify_seconds",
                "native_verifier_accepted_all", "changed_public_statement_rejected_all",
                "independent_value_oracle_statuses")},
                   "native_overflow_rejected": overflow_controls[name]}
            for name, profile in profiles.items()
        },
        "direct_over_sparse_median_wall_prove_ratio": round(
            profiles["direct-gate"]["median_wall_prove_seconds"] /
            profiles["sparse-wide-gate"]["median_wall_prove_seconds"], 4),
        "direct_over_sparse_median_proof_bytes_ratio": round(
            profiles["direct-gate"]["median_proof_bytes"] /
            profiles["sparse-wide-gate"]["median_proof_bytes"], 4),
        "limitations": ("One host and one source; paired profile order alternates by assignment, "
                        "with cold native setup for each distinct witness. Host load, process start, "
                        "OS cache, and proof-of-work vary. Matching visible FRI settings alone "
                        "do not establish equal soundness."),
    }
    s31.write_json(output / "summary.json", concise)
    analyze(output)
    return concise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=KINDS)
    parser.add_argument("--count", type=int, default=20)
    parser.add_argument("--seed", type=int, default=0x531A11)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--prepare-only", action="store_true",
                        help="write source and checked assignments without native proof runs")
    args = parser.parse_args()
    if args.prepare_only:
        source, assignments, overflow = prepare(args.kind, args.count, args.seed,
                                                args.out.resolve())
        print(json.dumps({"schema": "s31-fixed-multiplication-plan-v1",
                          "kind": args.kind, "count": len(assignments),
                          "source": str(source), "overflow_assignment": str(overflow)},
                         sort_keys=True, indent=2))
    else:
        print(json.dumps(run(args.kind, args.count, args.seed, args.out),
                         sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
