#!/usr/bin/env python3
"""Source and selected native checks for direct integer subtraction and order."""

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


def assignment(kind: str, a: int, b: int, result: int,
               output: str, operation: str) -> dict:
    width = int(kind[1:])
    return {
        "public_inputs": {},
        "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
        "public_outputs": {output: [result] if operation == "le" else limbs(result, width)},
    }


def source(kind: str, operation: str) -> str:
    result_type = "bit" if operation == "le" else kind
    return (f"use std@1;\ncircuit {kind}_{operation}(private a: {kind}, private b: {kind}) "
            f"-> public {result_type} {{ std::int::{operation}(a, b) }}\n")


def cases(kind: str, operation: str) -> tuple[list[tuple[int, int, int]], tuple[int, int, int] | None]:
    width = int(kind[1:])
    signed = kind.startswith("i")
    minimum = -(1 << (width - 1)) if signed else 0
    maximum = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    if operation == "sub_checked":
        honest = [(0, 0, 0), (maximum, 1, maximum - 1),
                  (minimum, 0, minimum), (1, 1, 0)]
        if width > 16:
            honest.append((1 << 16, 1, (1 << 16) - 1))
        if signed:
            honest.extend([(-1, -1, 0), (0, minimum + 1, maximum)])
            invalid = (minimum, 1, minimum - 1)
        else:
            invalid = (0, 1, maximum)
        return honest, invalid
    if operation == "le":
        honest = [(minimum, maximum, 1), (maximum, minimum, 0),
                  (0, 0, 1), (maximum, maximum, 1)]
        if signed:
            honest.extend([(-1, 0, 1), (0, -1, 0)])
        return honest, None
    raise ValueError(operation)


def run(work: Path, kind: str, operation: str, native: bool) -> dict:
    text = source(kind, operation)
    source_file = work / f"{kind}_{operation}.s31"
    source_file.write_text(text)
    relation, _ = compile_text(text, str(source_file))
    output = relation["public_outputs"][0]
    expected_op = "int_le" if operation == "le" else "int_sub_checked"
    spec = int(kind[1:]) | (256 if kind.startswith("i") else 0)
    if ([node["op"] for node in relation["nodes"]] !=
            ["int_view", "int_view", expected_op] or
            any(node.get("constant") != spec for node in relation["nodes"])):
        raise AssertionError(f"{kind} {operation}: relation shape or width tag changed")
    honest, invalid = cases(kind, operation)
    for a, b, result in honest:
        value = assignment(kind, a, b, result, output, operation)
        if evaluate_relation(relation, value) != value["public_outputs"]:
            raise AssertionError(f"{kind} {operation}: oracle disagrees at {a}, {b}")
    if invalid is not None:
        bad = assignment(kind, *invalid, output, operation)
        try:
            evaluate_relation(relation, bad)
        except OracleError as exc:
            if "overflow" not in str(exc):
                raise AssertionError(f"{kind}: rejected for another reason") from exc
        else:
            raise AssertionError(f"{kind}: checked subtraction accepted underflow")
    result = {"kind": kind, "operation": operation, "source_and_oracle_checked": True}
    if not native:
        return result
    package = s31.build(source_file, work / f"{kind}_{operation}-package", "direct-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "direct-m31-v4" or cost["raw"]["eq"] != 0 or cost["raw"]["m31_to_u32"] != 0:
        raise AssertionError(f"{kind} {operation}: direct arithmetic-only admission failed")
    a, b, expected = honest[-1]
    honest_file = work / f"{kind}_{operation}-honest.json"
    s31.write_json(honest_file, assignment(kind, a, b, expected, output, operation))
    trial = s31.trial(package, honest_file, work / f"{kind}_{operation}-trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError(f"{kind} {operation}: proof controls failed")
    if invalid is not None:
        bad_file = work / f"{kind}_{operation}-underflow.json"
        s31.write_json(bad_file, assignment(kind, *invalid, output, operation))
        prover = package / "bin" / f"s31-{kind}_{operation}-prover"
        rejected = subprocess.run([str(prover), "prove", str(bad_file),
                                   str(work / f"{kind}_{operation}-bad.proof")],
                                  capture_output=True, text=True, timeout=120)
        if rejected.returncode == 0:
            raise AssertionError(f"{kind}: native prover accepted underflow")
    result.update({"raw": cost["raw"], "padded": cost["padded"],
                   "preprocessed_cells": cost["preprocessed_cells"],
                   "proof_bytes": trial["proof_bytes"],
                   "native_verifier_accepted": True,
                   "changed_public_statement_rejected": True,
                   "native_underflow_rejected": invalid is not None})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=KINDS)
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    selected = (args.case,) if args.case else KINDS
    with tempfile.TemporaryDirectory(prefix="s31-direct-int-binary-") as directory:
        records = []
        for kind in selected:
            for operation in ("sub_checked", "le"):
                if args.native:
                    print(f"direct integer {kind} {operation}", file=sys.stderr, flush=True)
                records.append(run(Path(directory), kind, operation, args.native))
    print(json.dumps({"schema": "s31-direct-integer-binary-v1",
                      "native": args.native, "cases": records}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
