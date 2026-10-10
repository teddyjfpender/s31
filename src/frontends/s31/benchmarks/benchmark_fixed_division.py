#!/usr/bin/env python3
"""Compare native division proof profiles on a reproducible witness corpus."""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import evaluate_relation
from text_frontend import compile_text


def encode(kind: str, numerator: int, divisor: int) -> dict:
    width = int(kind.lstrip("ui"))
    mask = (1 << width) - 1
    quotient = abs(numerator) // abs(divisor)
    if (numerator < 0) != (divisor < 0):
        quotient = -quotient
    remainder = numerator - quotient * divisor
    return {
        "public_inputs": {},
        "private_inputs": {"numerator": [numerator & mask], "divisor": [divisor & mask]},
        "public_outputs": {"result": [quotient & mask, remainder & mask]},
    }


def corpus(kind: str, count: int, seed: int) -> list[tuple[int, int]]:
    if count < 5:
        raise ValueError("count must be at least five to retain boundary cases")
    width = int(kind.lstrip("ui"))
    signed = kind.startswith("i")
    fixture_dir = S31 / "examples/math/division/fixtures" / kind
    mask = (1 << width) - 1
    cases: list[tuple[int, int]] = []
    for path in sorted(fixture_dir.glob("*.json")):
        assignment = json.loads(path.read_text())
        n = assignment["private_inputs"]["numerator"][0]
        d = assignment["private_inputs"]["divisor"][0]
        if signed:
            n = n - (1 << width) if n & (1 << (width - 1)) else n
            d = d - (1 << width) if d & (1 << (width - 1)) else d
        cases.append((n, d))
    if len(cases) != 5 or len(set(cases)) != 5:
        raise ValueError(f"expected five distinct seed fixtures for {kind}")
    rng = random.Random(seed)
    seen = set(cases)
    lower = -(1 << (width - 1)) if signed else 0
    upper = (1 << (width - 1)) - 1 if signed else mask
    while len(cases) < count:
        pair = (rng.randint(lower, upper), rng.randint(lower, upper))
        if pair[1] == 0 or pair in seen or (signed and pair == (lower, -1)):
            continue
        seen.add(pair)
        cases.append(pair)
    return cases


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=("u8", "i8", "u16", "i16"))
    parser.add_argument("--count", type=int, default=20)
    parser.add_argument("--seed", type=int, default=0x5310)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    source = S31 / "examples/math/division" / f"{args.kind}_div_rem.s31"
    warmup = source.with_suffix(".valid.json")
    relation, _ = compile_text(source.read_text(), str(source))
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    assignment_paths = []
    for index, (numerator, divisor) in enumerate(corpus(args.kind, args.count, args.seed)):
        assignment = encode(args.kind, numerator, divisor)
        if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
            raise AssertionError(f"independent oracle rejected {args.kind} corpus case {index}")
        path = output / "assignments" / f"{index:03d}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        s31.write_json(path, assignment)
        assignment_paths.append(path)
    report = s31.tune(source, assignment_paths, output / "tune",
                      ["direct-gate", "sparse-wide-gate"], warmup)
    summary = {
        "schema": "s31-fixed-division-benchmark-v1",
        "kind": args.kind,
        "count": args.count,
        "seed": args.seed,
        "distinct_assignments": report["distinct_assignments"],
        "same_visible_fri_settings": report["same_visible_fri_settings"],
        "canonical_ir_sha256": report["canonical_ir_sha256"],
        "assignment_sha256": report["assignment_sha256"],
        "profiles": {
            name: {key: profile[key] for key in (
                "preprocessed_cells", "median_proof_bytes", "median_wall_prove_seconds",
                "median_prove_excluding_pow_seconds", "native_verifier_accepted_all",
                "changed_public_statement_rejected_all", "independent_value_oracle_statuses")}
            for name, profile in report["profiles"].items()
        },
    }
    s31.write_json(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
