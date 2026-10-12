#!/usr/bin/env python3
"""Check a source-bound direct-Gate package against one accepted proof.

Usage:
  python3 check_direct_gate_fixed_root_join.py PACKAGE PROOF STATEMENT --pins PINS.json

The package must carry the checked public four-lane 1..16-gate source
certificate. PINS.json must contain externally authenticated SHA-256 digests
for text, source, key, prover, and verifier. The supplied proof is verified
against the exact statement and sealed key before its header is decoded.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.fixed_root_join import check  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("--pins", type=Path, required=True,
                        help="external SHA-256 pins for text/source/key/prover/verifier")
    args = parser.parse_args()
    def unique_pairs(items: list[tuple[str, str]]) -> dict[str, str]:
        result = {}
        for name, value in items:
            if name in result:
                raise ValueError(f"duplicate pin name: {name}")
            result[name] = value
        return result
    pins = json.loads(args.pins.read_bytes(), object_pairs_hook=unique_pairs)
    if type(pins) is not dict:
        raise ValueError("external pins must be a JSON object")
    print(json.dumps(check(args.package, args.proof, args.statement, pins), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"fixed-root join: {exc}", file=sys.stderr)
        raise SystemExit(1)
