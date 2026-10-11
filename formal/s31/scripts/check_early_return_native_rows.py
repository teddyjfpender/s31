#!/usr/bin/env python3
"""Check the early-return fixture's physical-row premises from native trace data.

The debug exporter calls the same direct `writeBase` routine as the prover.
This checker uses its actual twelve main columns and eight preprocessed columns,
not a guessed value for a Lean Row. It establishes finite physical-row and
all-row nine-root facts for one public assignment. The trace is diagnostic and
uncommitted: accepting a STARK proof is not shown to authenticate these rows,
nor to imply ideal exact Gate balance or unique producers.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

import check_early_return_nonvacuity as model


ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
from package.verify import verify_package  # noqa: E402
from package.correspondence import DIRECT_COLUMN_IDS  # noqa: E402


SCHEMA = "s31-direct-gate-early-return-physical-v1"
SOURCE_SHA256 = "d382cee3a72ba2d22becf0c579580f97077e78e4cc7949f1e71c2800b42887be"
PROGRAM_SHA256 = "93bd19fc72c1e4526ad8bfe788f506bfea4c1787114df6e119dd95760efd888f"
FIXED_FIELDS = ("addFlag", "subFlag", "mulFlag", "pointwiseMulFlag", "in0", "in1", "out", "mults")


def _columns(value: object, count: int, name: str) -> list[list[int]]:
    if (type(value) is not list or len(value) != count or
            any(type(column) is not list or len(column) != 512 for column in value)):
        raise ValueError(f"invalid {name} column shape")
    if any(type(word) is not int or not 0 <= word < model.P for column in value for word in column):
        raise ValueError(f"noncanonical {name} field value")
    return value


def _fixture_cells() -> tuple[list[model.Cell], list[model.Cell], list[model.Cell]]:
    text = model.FIXTURE.read_text()
    instructions, selected = model.certificate(text)
    expected = model.expected_plans(instructions, selected, model.fixture_number(text, "observedAddRows"))
    observed = tuple(model.cells(text, name) for name in
                     ("observedColumnCells", "observedInputCells", "observedOutputCells"))
    if observed != expected or len(observed[0] + observed[1] + observed[2]) != 28:
        raise ValueError("Lean generated physical-cell fixture is stale")
    return observed


def check_report(report: dict, topology: dict | None = None) -> dict[str, int]:
    if (type(report) is not dict or report.get("schema") != SCHEMA or
            report.get("program_sha256") != PROGRAM_SHA256):
        raise ValueError("wrong source or physical-trace schema")
    fixed = _columns(report.get("fixed_columns"), 8, "fixed")
    main = _columns(report.get("main_columns"), 12, "main")
    if topology is not None:
        schema = topology.get("schema") if type(topology) is dict else None
        if (type(topology) is not dict or
                schema not in {"s31-direct-gate-topology-v1", "s31-direct-gate-topology-v2"} or
                (schema == "s31-direct-gate-topology-v2" and
                 (type(topology.get("preprocessed_root")) is not str or
                  re.fullmatch(r"[0-9a-f]{64}", topology["preprocessed_root"]) is None)) or
                topology.get("program_sha256") != PROGRAM_SHA256 or
                type(topology.get("columns")) is not list or
                len(topology["columns"]) != 8 or
                any(type(column) is not dict for column in topology["columns"]) or
                [column.get("id") for column in topology["columns"]] != list(DIRECT_COLUMN_IDS) or
                [column.get("values") for column in topology["columns"]] != fixed):
            raise ValueError("physical fixed columns differ from package topology")
    public = report.get("public_words")
    if (type(public) is not list or len(public) != 8 or
            any(type(word) is not int or not 0 <= word < model.P for word in public)):
        raise ValueError("invalid public words")
    if public[4:] != [word * word % model.P for word in public[:4]]:
        raise ValueError("selected result differs from public input square")

    for index in range(512):
        limbs = [column[index] for column in main]
        physical = model.Row(fixed[4][index], fixed[5][index], fixed[6][index],
                             tuple(column[index] for column in fixed[:4]),
                             tuple(limbs[:4]), tuple(limbs[4:8]),
                             tuple(limbs[8:]), fixed[7][index])
        if any(model.roots(physical)):
            raise ValueError(f"installed arithmetic roots differ at trace row {index}")

    source, inputs, outputs = _fixture_cells()
    selected = source + inputs + outputs
    if len({cell.traceRow for cell in selected}) != len(selected):
        raise ValueError("projected physical rows overlap")
    for cell in selected:
        index = cell.traceRow
        expected_fixed = [getattr(cell, field) for field in FIXED_FIELDS]
        actual_fixed = [column[index] for column in fixed]
        if actual_fixed != expected_fixed:
            raise ValueError(f"fixed cell differs at trace row {index}")
    # The generated input/output copy rows produce Gate addresses 3..6 and
    # 7..10. Their native QM31 output limbs must be the public M31 words,
    # embedded in the base limb. A valid arithmetic trace alone permits an
    # all-zero witness paired with an unrelated x,x² public statement.
    for lane in range(4):
        for role, cells, address, word in (
            ("input", inputs, 3 + lane, public[lane]),
            ("output", outputs, 7 + lane, public[4 + lane]),
        ):
            copies = [cell for cell in cells
                      if cell.out == address and cell.addFlag == 1 and cell.in1 == 0]
            if len(copies) != 1:
                raise ValueError(f"missing unique physical public {role} copy row {lane}")
            actual = [column[copies[0].traceRow] for column in main[8:12]]
            if actual != [word, 0, 0, 0]:
                raise ValueError(f"physical public {role} pin differs at lane {lane}")
    if any(cell.mults <= 0 for cell in inputs + outputs):
        raise ValueError("public boundary row has zero multiplicity")
    if [cell.mults for cell in source] != [6, 1, 0]:
        raise ValueError("source-use multiplicity differs from early-return certificate")
    return {"trace_rows": 512, "source_rows": len(source),
            "input_rows": len(inputs), "output_rows": len(outputs),
            "dead_source_rows": sum(cell.mults == 0 for cell in source)}


def check_package_trace(package: Path, assignment: Path) -> dict[str, int]:
    manifest = verify_package(package)
    if manifest.get("name") != "early_output" or manifest.get("lowering") != "direct-gate":
        raise ValueError("physical trace command is only for the early-return package")
    if hashlib.sha256((package / "source.s31").read_bytes()).hexdigest() != SOURCE_SHA256:
        raise ValueError("source text differs from generated Lean fixture")
    if hashlib.sha256((package / "source.s31.json").read_bytes()).hexdigest() != PROGRAM_SHA256:
        raise ValueError("normalized source differs from generated Lean fixture")
    prover = package / "bin/s31-early_output-prover"
    result = subprocess.run([str(prover), "inspect-physical-rows", str(assignment)],
                            capture_output=True, text=True, check=False)
    if result.returncode:
        raise ValueError(f"native physical-row export failed: {result.stderr}")
    report = json.loads(result.stdout + result.stderr)
    requested = json.loads(assignment.read_text())
    if (type(report) is not dict or
            type(requested) is not dict or
            type(requested.get("public_inputs")) is not dict or
            type(requested.get("public_outputs")) is not dict or
            type(requested["public_inputs"].get("x")) is not list or
            type(requested["public_outputs"].get("a")) is not list or
            report.get("public_words") !=
            requested["public_inputs"]["x"] + requested["public_outputs"]["a"]):
        raise ValueError("native public words differ from requested assignment")
    topology = json.loads((package / "gate-topology.json").read_text())
    return check_report(report, topology)


def _synthetic_control_report() -> dict:
    """Control data only; the normal path above always reads native writeBase."""
    fixed = [[0] * 512 for _ in range(8)]
    fixed[0] = [1] * 512  # Valid zero + zero padding rows.
    main = [[0] * 512 for _ in range(12)]
    for cell in sum(_fixture_cells(), []):
        for column, field in zip(fixed, FIXED_FIELDS, strict=True):
            column[cell.traceRow] = getattr(cell, field)
        row = model.row_for_cell(cell)
        for column, value in zip(main, row.in0 + row.in1 + row.output, strict=True):
            column[cell.traceRow] = value
    return {"schema": SCHEMA, "program_sha256": PROGRAM_SHA256,
            "public_words": [0] * 8, "fixed_columns": fixed, "main_columns": main}


def check_negative_controls() -> None:
    original = _synthetic_control_report()
    check_report(original)
    for label, mutate, expected in (
        ("wrong-fixed", lambda report: report["fixed_columns"][7].__setitem__(502, 7), "fixed cell differs"),
        ("wrong-main", lambda report: report["main_columns"][8].__setitem__(502, 1), "arithmetic roots differ"),
        ("wrong-public", lambda report: report["public_words"].__setitem__(4, 1), "selected result differs"),
        ("coherent-wrong-witness", lambda report: (report["public_words"].__setitem__(0, 1),
                                                   report["public_words"].__setitem__(4, 1)),
         "physical public input pin differs"),
    ):
        altered = copy.deepcopy(original)
        mutate(altered)
        try:
            check_report(altered)
        except ValueError as exc:
            if expected not in str(exc):
                raise AssertionError(f"{label} failed for wrong reason: {exc}") from exc
        else:
            raise AssertionError(f"{label} was accepted")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, help="checked early-return S31 package")
    parser.add_argument("--assignment", type=Path, help="public assignment JSON")
    parser.add_argument("--report", type=Path, help="diagnostic native export JSON")
    parser.add_argument("--controls", action="store_true", help="run mutation controls")
    args = parser.parse_args()
    if args.package is not None and args.assignment is not None and args.report is None:
        print(json.dumps(check_package_trace(args.package, args.assignment), sort_keys=True))
    elif args.report is not None and args.package is None and args.assignment is None:
        print(json.dumps(check_report(json.loads(args.report.read_text())), sort_keys=True))
    elif not args.controls:
        parser.error("pass --package with --assignment, --report, or --controls")
    if args.controls:
        check_negative_controls()
        print("physical_row_mutation_controls=4 rejected")


if __name__ == "__main__":
    main()
