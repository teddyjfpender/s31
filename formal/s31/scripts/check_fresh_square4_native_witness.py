#!/usr/bin/env python3
"""Rebuild square4 and compare a fresh native base trace with pinned evidence.

The native `inspect-physical-rows` command exports uncommitted evaluations
from the prover `writeBase` path. This gate checks reproducibility of that
diagnostic; it does not authenticate proof openings or establish PCS soundness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import tempfile

import check_square4_native_witness as witness

ROOT = Path(__file__).resolve().parents[3]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/direct_gate_release_cost"))

import s31  # noqa: E402
import fixed_columns  # noqa: E402

ASSIGNMENT = S31 / "examples/arithmetic/functional_square4.valid.json"
PINNED_REPORT = ROOT / "formal/s31/fixtures/square4-native-physical.json"
PINNED_LEAN = (ROOT / "formal/s31/S31/Gadgets/Functional/"
               "TextSquare4NativeWitness.lean")


def first_difference(left: object, right: object, path: str = "$") -> str | None:
    """Identify the first changed cell without flooding CI with 10,240 values."""
    if type(left) is not type(right):
        return path
    if isinstance(left, dict):
        if left.keys() != right.keys():
            return path + "keys"
        for key in left:
            found = first_difference(left[key], right[key], f"{path}.{key}")
            if found is not None:
                return found
        return None
    if isinstance(left, list):
        if len(left) != len(right):
            return path + "length"
        for index, (a, b) in enumerate(zip(left, right, strict=True)):
            found = first_difference(a, b, f"{path}[{index}]")
            if found is not None:
                return found
        return None
    return None if left == right else path


def check_pinned(report: dict) -> dict[str, int]:
    summary = witness.check_report(report)
    witness.mutation_controls(report)
    pinned = json.loads(PINNED_REPORT.read_bytes())
    difference = first_difference(report, pinned)
    if difference is not None:
        raise ValueError(f"fresh native square4 report differs from pinned JSON at {difference}")
    rendered = witness.render_lean(report).encode()
    if rendered != PINNED_LEAN.read_bytes():
        raise ValueError("fresh native square4 Lean fixture differs from pinned module")
    summary["mutations_rejected"] = 5
    return summary


def run(report_output: Path | None, lean_output: Path | None) -> dict[str, int | str]:
    requested = json.loads(ASSIGNMENT.read_bytes())
    if requested != {"public_inputs": {"x": witness.PUBLIC[:4]},
                     "private_inputs": {},
                     "public_outputs": {"result": witness.PUBLIC[4:]}}:
        raise ValueError("square4 assignment differs from the pinned public claim")
    # A new temporary output path makes `s31.build` execute, rather than
    # accepting an earlier package from its output-exists cache branch.
    with tempfile.TemporaryDirectory(prefix="s31-fresh-square4-") as directory:
        package = s31.build(fixed_columns.SOURCE, Path(directory) / "package",
                            "direct-gate")
        metadata, fixed_bytes = fixed_columns.native_fixture(package)
        expected_metadata, expected_columns = fixed_columns.read_fixture()
        if (metadata != expected_metadata or
                fixed_bytes != fixed_columns.WORDS.read_bytes()):
            raise ValueError("fresh native fixed columns differ from pinned fixture")
        fixed_columns.check_formal_rows(expected_columns)
        report = witness.inspect_package(package, ASSIGNMENT)
    summary = check_pinned(report)
    if report_output is not None:
        report_output.parent.mkdir(parents=True, exist_ok=True)
        report_output.write_text(json.dumps(report, separators=(",", ":")) + "\n")
    if lean_output is not None:
        lean_output.parent.mkdir(parents=True, exist_ok=True)
        lean_output.write_text(witness.render_lean(report))
    summary["pinned_report_sha256"] = hashlib.sha256(PINNED_REPORT.read_bytes()).hexdigest()
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-report", type=Path)
    parser.add_argument("--write-lean", type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.write_report, args.write_lean), sort_keys=True))


if __name__ == "__main__":
    main()
