#!/usr/bin/env python3
"""Ten-width direct multiplication source, oracle, and native proof gate."""

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
    return {"public_inputs": {},
            "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
            "public_outputs": {output: limbs(result, width)}}


def checked_values(width: int, signed: bool) -> tuple[list[tuple[int, int, int]], tuple[int, int, int]]:
    minimum = -(1 << (width - 1)) if signed else 0
    maximum = (1 << (width - 1 if signed else width)) - 1
    honest = [(0, 0, 0), (1, 1, 1), (maximum, 1, maximum),
              (minimum, 1, minimum), (maximum // 2, 2, (maximum // 2) * 2)]
    if signed:
        honest.append((-3, 7, -21))
        overflow = (minimum, -1, -minimum)
    else:
        if width > 16:
            honest.append((255, 258, 255 * 258))
        overflow = (maximum, 2, maximum * 2)
    return honest, overflow


def run(work: Path, kind: str, checked: bool, native: bool) -> dict:
    width = int(kind[1:])
    signed = kind.startswith("i")
    mode = "checked" if checked else "wrapping"
    source = (f"use std@1;\ncircuit {kind}_mul_{mode}(private a: {kind}, private b: {kind}) "
              f"-> public {kind} {{ std::int::mul_{mode}(a, b) }}\n")
    source_file = work / f"{kind}_mul_{mode}.s31"
    source_file.write_text(source)
    relation, _ = compile_text(source, str(source_file))
    output = relation["public_outputs"][0]
    spec = width | (256 if signed else 0)
    expected = "int_mul_checked" if checked else "int_mul_wrapping"
    if ([node["op"] for node in relation["nodes"]] !=
            ["int_view", "int_view", expected] or
            any(node.get("constant") != spec for node in relation["nodes"])):
        raise AssertionError(f"{kind} {mode}: relation shape or width tag changed")
    honest, overflow = checked_values(width, signed)
    if not checked:
        honest.append(overflow)
    for a, b, result in honest:
        claim = assignment(width, a, b, result, output)
        if evaluate_relation(relation, claim) != claim["public_outputs"]:
            raise AssertionError(f"{kind} {mode}: oracle disagrees at {a} * {b}")
    if checked:
        bad = assignment(width, *overflow, output)
        try:
            evaluate_relation(relation, bad)
        except OracleError as exc:
            if "overflow" not in str(exc):
                raise AssertionError(f"{kind}: rejected for another reason") from exc
        else:
            raise AssertionError(f"{kind}: checked overflow was accepted")
    result = {"kind": kind, "mode": mode, "source_and_oracle_checked": True}
    if not native:
        return result
    package = s31.build(source_file, work / f"{kind}_mul_{mode}-package", "direct-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if (cost["profile"] != "direct-m31-v4" or
            any(cost["raw"][name] != 0 for name in ("eq", "m31_to_u32", "triple_xor", "blake_g"))):
        raise AssertionError(f"{kind} {mode}: circuit has unsupported direct gates")
    # The unsigned witness propagates bits through every limb; the signed
    # witness exercises the high-word sign-extension identity.
    a, b, product = honest[-1] if signed else honest[4]
    honest_file = work / f"{kind}_mul_{mode}-honest.json"
    s31.write_json(honest_file, assignment(width, a, b, product, output))
    trial = s31.trial(package, honest_file, work / f"{kind}_mul_{mode}-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{kind} {mode}: native proof controls failed")
    if checked:
        bad_file = work / f"{kind}_mul_{mode}-overflow.json"
        s31.write_json(bad_file, assignment(width, *overflow, output))
        prover = package / "bin" / f"s31-{kind}_mul_{mode}-prover"
        rejected = subprocess.run([str(prover), "prove", str(bad_file),
                                   str(work / f"{kind}_mul_{mode}-bad.proof")],
                                  capture_output=True, text=True, timeout=120)
        if rejected.returncode == 0:
            raise AssertionError(f"{kind}: native prover accepted overflowing product")
    result.update({"raw": cost["raw"], "padded": cost["padded"],
                   "preprocessed_cells": cost["preprocessed_cells"],
                   "proof_bytes": trial["proof_bytes"],
                   "native_verifier_accepted": True,
                   "changed_public_statement_rejected": True,
                   "native_overflow_rejected": checked})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=KINDS)
    parser.add_argument("--mode", choices=("checked", "wrapping", "both"), default="both")
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    names = (args.case,) if args.case else KINDS
    modes = (True, False) if args.mode == "both" else (args.mode == "checked",)
    with tempfile.TemporaryDirectory(prefix="s31-direct-int-mul-") as directory:
        results = []
        for kind in names:
            for checked in modes:
                if args.native:
                    print(f"direct multiplication: {kind} {'checked' if checked else 'wrapping'}",
                          file=sys.stderr, flush=True)
                results.append(run(Path(directory), kind, checked, args.native))
    print(json.dumps({"schema": "s31-direct-integer-multiplication-v1",
                      "compiler_sha256": s31.compiler_fingerprint(),
                      "native": args.native, "cases": results}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
