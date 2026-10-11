#!/usr/bin/env python3
"""Check a bounded square4 base trace exported by the native direct prover.

This checks uncommitted fixed and main evaluations. The report is produced by
the exact `writeBase` path used before commitment; it is not a proof opening
and does not authenticate interaction columns or PCS/FRI verification.
"""

from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import struct
import subprocess
import sys

import check_early_return_nonvacuity as model

ROOT = Path(__file__).resolve().parents[3]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/direct_gate_release_cost"))
from fixed_columns import SOURCE, read_fixture, native_fixture  # noqa: E402

SCHEMA = "s31-direct-gate-square4-physical-v1"
PROGRAM_SHA256 = "b7d744dd89f487742f2b72cf71fa76c6c37c2f5b01b74b58befa24e8c749979c"
PUBLIC = [0, 1, 2, 7, 0, 1, 16, 2401]
MAIN_COLUMNS = 12
ROWS = 512


def columns(raw: object, count: int, label: str) -> list[list[int]]:
    if (type(raw) is not list or len(raw) != count or
            any(type(col) is not list or len(col) != ROWS for col in raw)):
        raise ValueError(f"invalid {label} shape")
    if any(type(v) is not int or not 0 <= v < model.P for col in raw for v in col):
        raise ValueError(f"noncanonical {label} cell")
    return raw


def check_ideal_gate_balance(fixed: list[list[int]], main: list[list[int]],
                             public: list[int]) -> tuple[int, int, int]:
    """Check exact Gate event multisets for the pinned square4 feeder model.

    The nine external uses are the unit at address 2 and the eight public
    scalar words at addresses 3..10. No external yields are modeled. This is
    a value-level diagnostic, not an authenticated LogUp or PCS check.
    """
    uses: Counter[tuple[int, tuple[int, ...]]] = Counter()
    yields: Counter[tuple[int, tuple[int, ...]]] = Counter()
    uses[(2, (0, 0, 1, 0))] += 1
    for address, word in enumerate(public, start=3):
        uses[(address, (word, 0, 0, 0))] += 1
    producers: dict[int, tuple[int, ...]] = {}
    for index in range(ROWS):
        left = tuple(main[column][index] for column in range(4))
        right = tuple(main[column][index] for column in range(4, 8))
        output = tuple(main[column][index] for column in range(8, 12))
        uses[(fixed[4][index], left)] += 1
        uses[(fixed[5][index], right)] += 1
        multiplicity = fixed[7][index]
        if multiplicity:
            address = fixed[6][index]
            if address in producers and producers[address] != output:
                raise ValueError(f"ideal Gate producer conflict at row {index}")
            producers[address] = output
            yields[(address, output)] += multiplicity
    if uses != yields:
        raise ValueError("ideal Gate balance differs from pinned square4 feeder")
    return sum(uses.values()), sum(yields.values()), len(producers)


def check_report(report: dict) -> dict[str, int]:
    if (type(report) is not dict or report.get("schema") != SCHEMA or
            report.get("program_sha256") != PROGRAM_SHA256):
        raise ValueError("wrong square4 source or physical-row schema")
    fixed = columns(report.get("fixed_columns"), 8, "fixed")
    main = columns(report.get("main_columns"), MAIN_COLUMNS, "main")
    metadata, native_fixed = read_fixture()
    if metadata["program_sha256"] != PROGRAM_SHA256 or fixed != [list(col) for col in native_fixed]:
        raise ValueError("physical fixed cells differ from native key-bound fixture")
    public = report.get("public_words")
    if type(public) is not list or any(type(word) is not int for word in public) or public != PUBLIC:
        raise ValueError("square4 public assignment changed")

    for index in range(ROWS):
        limbs = [main[col][index] for col in range(MAIN_COLUMNS)]
        row = model.Row(fixed[4][index], fixed[5][index], fixed[6][index],
                        tuple(fixed[col][index] for col in range(4)),
                        tuple(limbs[:4]), tuple(limbs[4:8]),
                        tuple(limbs[8:12]), fixed[7][index])
        if any(model.roots(row)):
            raise ValueError(f"arithmetic roots differ at row {index}")

    # Four source-owned public input and output copy rows bind the native main
    # trace to the selected statement, not merely to internally valid gates.
    for lane in range(4):
        for label, index, address, word in (
            ("input", 3 + lane, 3 + lane, public[lane]),
            ("output", 7 + lane, 7 + lane, public[4 + lane]),
        ):
            if ([fixed[col][index] for col in (0, 4, 5, 6)] != [1, fixed[4][index], 0, address] or
                    fixed[7][index] == 0 or
                    [main[col][index] for col in range(8, 12)] != [word, 0, 0, 0]):
                raise ValueError(f"physical public {label} pin differs at lane {lane}")

    # The source squares are pointwise QM31 products at the native grouped
    # rows. The tuples are fully checked, including operand and output limbs.
    for index, operand, output in (
        (502, [0, 1, 2, 7], [0, 1, 4, 49]),
        (503, [0, 1, 4, 49], [0, 1, 16, 2401]),
    ):
        if ([fixed[col][index] for col in (0, 1, 2, 3)] != [0, 0, 0, 1] or
                [main[col][index] for col in range(4)] != operand or
                [main[col][index] for col in range(4, 8)] != operand or
                [main[col][index] for col in range(8, 12)] != output):
            raise ValueError(f"source square row differs at row {index}")
    gate_uses, gate_yields, producers = check_ideal_gate_balance(fixed, main, public)
    return {"rows": ROWS, "fixed_cells": 8 * ROWS, "main_cells": MAIN_COLUMNS * ROWS,
            "arithmetic_roots": 9 * ROWS, "public_pins": 8, "source_rows": 2,
            "ideal_gate_uses": gate_uses, "ideal_gate_yields": gate_yields,
            "unique_gate_producers": producers}


def inspect_package(package: Path, assignment: Path) -> dict:
    fixture_meta, _ = native_fixture(package)
    if (fixture_meta["program_sha256"] != PROGRAM_SHA256 or
            fixture_meta["source_sha256"] != hashlib.sha256(SOURCE.read_bytes()).hexdigest()):
        raise ValueError("native package source differs from square4 fixture")
    prover = package / "bin/s31-functional_square4-prover"
    result = subprocess.run([str(prover), "inspect-physical-rows", str(assignment)],
                            capture_output=True, text=True, check=False)
    if result.returncode:
        raise ValueError(f"native physical-row export failed: {result.stderr}")
    report = json.loads(result.stdout + result.stderr)
    requested = json.loads(assignment.read_bytes())
    if (requested.get("public_inputs", {}).get("x") != PUBLIC[:4] or
            requested.get("public_outputs", {}).get("result") != PUBLIC[4:]):
        raise ValueError("requested public assignment differs from pinned statement")
    check_report(report)
    return report


def mutation_controls(report: dict) -> None:
    for name, edit, expected in (
        ("wrong-main", lambda r: r["main_columns"][8].__setitem__(503, 1), "arithmetic roots differ"),
        ("wrong-fixed", lambda r: r["fixed_columns"][0].__setitem__(11, 0), "fixed cells differ"),
        ("wrong-public-pin", lambda r: r["main_columns"][8].__setitem__(7, 9), "arithmetic roots differ"),
        ("wrong-claim", lambda r: r["public_words"].__setitem__(7, 2400), "public assignment changed"),
        ("local-but-unbalanced", lambda r: (
            r["main_columns"][0].__setitem__(11, 1),
            r["main_columns"][4].__setitem__(11, 2),
            r["main_columns"][8].__setitem__(11, 3)), "ideal Gate balance differs"),
    ):
        changed = copy.deepcopy(report)
        edit(changed)
        try:
            check_report(changed)
        except ValueError as exc:
            if expected not in str(exc):
                raise AssertionError(f"{name}: rejected for wrong reason: {exc}") from exc
        else:
            raise AssertionError(f"{name}: mutation accepted")


def render_lean(report: dict) -> str:
    """Render the inspected main evaluations as a transparent Lean fixture."""
    check_report(report)
    metadata, _ = read_fixture()
    main = report["main_columns"]
    raw = b"".join(struct.pack("<I", word) for column in main for word in column)
    lines = [
        "import S31.Gadgets.Functional.TextSquare4Native",
        "",
        "/-! Exact uncommitted direct-prover base trace for x = [0, 1, 2, 7].",
        "Generated by check_square4_native_witness.py from the pinned native",
        "inspect-physical-rows diagnostic after all-row and key-fixture checks.",
        "This is not a PCS opening or a verifier-acceptance theorem. -/",
        "",
        "namespace S31.Functional.TextSquare4NativeWitness",
        f'def programSha256 : String := "{PROGRAM_SHA256}"',
        f'def preprocessedRoot : String := "{metadata["preprocessed_root"]}"',
        f'def mainColumnMajorSha256 : String := "{hashlib.sha256(raw).hexdigest()}"',
        "def publicWords : List Nat := [" + ", ".join(map(str, PUBLIC)) + "]",
        "def mainRows : List (List Nat) := [",
    ]
    for index in range(ROWS):
        row = ", ".join(str(main[column][index]) for column in range(MAIN_COLUMNS))
        lines.append(f"  [{row}]{',' if index + 1 < ROWS else ''}")
    lines.extend(["]", "end S31.Functional.TextSquare4NativeWitness", ""])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path)
    parser.add_argument("--assignment", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--write-report", type=Path)
    parser.add_argument("--write-lean", type=Path)
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    if args.package and args.assignment and not args.report:
        report = inspect_package(args.package, args.assignment)
    elif args.report and not args.package and not args.assignment:
        report = json.loads(args.report.read_bytes())
    else:
        parser.error("pass --package with --assignment, or --report")
    summary = check_report(report)
    if args.controls:
        mutation_controls(report)
        summary["mutations_rejected"] = 5
    if args.write_report:
        args.write_report.parent.mkdir(parents=True, exist_ok=True)
        args.write_report.write_text(json.dumps(report, separators=(",", ":")) + "\n")
    if args.write_lean:
        args.write_lean.parent.mkdir(parents=True, exist_ok=True)
        args.write_lean.write_text(render_lean(report))
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
