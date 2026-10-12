#!/usr/bin/env python3
"""Native checked-addition edge cases for every nominal integer width."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


KINDS = tuple(f"{sign}{width}" for sign in ("u", "i")
              for width in (8, 16, 32, 64, 128))


def limbs(value: int, width: int) -> list[int]:
    pattern = value & ((1 << width) - 1)
    return [(pattern >> (16 * index)) & 0xffff
            for index in range(max(1, width // 16))]


def assignment(width: int, a: int, b: int, result: int, output: str) -> dict:
    return {
        "public_inputs": {},
        "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
        "public_outputs": {output: limbs(result, width)},
    }


def rejected_by_prover(package: Path, kind: str, work: Path, value: dict) -> bool:
    case = work / f"{kind}-overflow.json"
    s31.write_json(case, value)
    native = package / "bin" / f"s31-{kind}_checked_add-native-verifier"
    prover = package / "bin" / f"s31-{kind}_checked_add-prover"
    if not native.is_file() or not prover.is_file():
        raise AssertionError(f"{kind}: generated native tools are missing")
    result = subprocess.run([str(prover), "prove", str(case),
                             str(work / f"{kind}-overflow.proof")],
                            capture_output=True, text=True, timeout=120)
    return result.returncode != 0


def run_case(work: Path, kind: str, *, source_only: bool = False,
             lowering: str = "sparse-wide-gate") -> dict:
    width = int(kind[1:])
    signed = kind.startswith("i")
    largest = (1 << (width - 1 if signed else width)) - 1
    source = (f"use std@1;\n"
              f"circuit {kind}_checked_add(private a: {kind}, private b: {kind}) "
              f"-> public {kind} {{ std::int::add_checked(a, b) }}\n")
    source_file = work / f"{kind}_checked_add.s31"
    source_file.write_text(source)
    relation, _ = compile_text(source, str(source_file))
    output_name = relation["public_outputs"][0]
    nodes = relation["nodes"]
    spec = width | (256 if signed else 0)
    if ([node["op"] for node in nodes] !=
            ["int_view", "int_view", "int_add_checked"] or
            any(node.get("constant") != spec for node in nodes)):
        raise AssertionError(f"{kind}: width/signedness or relation lowering changed")
    honest = assignment(width, largest - 1, 1, largest, output_name)
    honest_file = work / f"{kind}-honest.json"
    s31.write_json(honest_file, honest)
    if evaluate_relation(relation, honest) != honest["public_outputs"]:
        raise AssertionError(f"{kind}: independent oracle rejected the limit result")
    boundary_cases = [(0, 0, 0)]
    boundary_cases.extend(((1 << offset) - 1, 1, 1 << offset)
                          for offset in range(16, width - (1 if signed else 0), 16))
    if signed:
        boundary_cases.append((-(1 << (width - 1)), 0, -(1 << (width - 1))))
    for a, b, expected in boundary_cases:
        case = assignment(width, a, b, expected, output_name)
        if evaluate_relation(relation, case) != case["public_outputs"]:
            raise AssertionError(f"{kind}: independent oracle rejected a boundary case")
    overflow = assignment(width, largest, 1, largest + 1, output_name)
    try:
        evaluate_relation(relation, overflow)
    except OracleError as exc:
        if "overflow" not in str(exc):
            raise AssertionError(f"{kind}: overflow failed for another reason") from exc
    else:
        raise AssertionError(f"{kind}: independent oracle accepted overflow")
    if signed:
        underflow = assignment(width, -(1 << (width - 1)), -1,
                               -(1 << (width - 1)) - 1, output_name)
        try:
            evaluate_relation(relation, underflow)
        except OracleError as exc:
            if "overflow" not in str(exc):
                raise AssertionError(f"{kind}: lower overflow failed for another reason") from exc
        else:
            raise AssertionError(f"{kind}: independent oracle accepted lower overflow")
    if source_only:
        return {"kind": kind, "spec": spec, "source_and_oracle_checked": True,
                "native_not_run": True}

    package = s31.build(source_file, work / f"{kind}-package", lowering)
    cost = json.loads((package / "cost-report.json").read_text())
    expected_profile = "direct-m31-v4" if lowering == "direct-gate" else "sparse-wide-v5"
    if cost["profile"] != expected_profile or cost["constant_min_base"] != 16:
        raise AssertionError(f"{kind}: unexpected proof profile or integer constant policy")
    trial = s31.trial(package, honest_file, work / f"{kind}-trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError(f"{kind}: honest proof or changed-claim control failed")
    if not rejected_by_prover(package, kind, work, overflow):
        raise AssertionError(f"{kind}: native prover accepted overflow")
    return {
        "kind": kind, "spec": spec, "lowering": lowering,
        "canonical_ir_sha256": cost["canonical_ir_sha256"],
        "raw": cost["raw"], "padded": cost["padded"],
        "preprocessed_cells": cost["preprocessed_cells"],
        "proof_bytes": trial["proof_bytes"],
        "native_verifier_accepted": True,
        "changed_public_statement_rejected": True,
        "native_overflow_rejected": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=KINDS)
    parser.add_argument("--source-only", action="store_true",
                        help="check source, tags and independent values without building a proof")
    parser.add_argument("--lowering", choices=("sparse-wide-gate", "direct-gate"),
                        default="sparse-wide-gate")
    args = parser.parse_args()
    names = (args.case,) if args.case else KINDS
    with tempfile.TemporaryDirectory(prefix="s31-int-addition-") as temporary:
        cases = []
        for kind in names:
            if not args.source_only:
                print(f"checked addition: {kind}", file=sys.stderr, flush=True)
            cases.append(run_case(Path(temporary), kind, source_only=args.source_only,
                                  lowering=args.lowering))
    print(json.dumps({"schema": "s31-int-addition-source-v1" if args.source_only
                      else "s31-int-addition-native-v1", "lowering": args.lowering,
                      "compiler_sha256": s31.compiler_fingerprint(),
                      "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
