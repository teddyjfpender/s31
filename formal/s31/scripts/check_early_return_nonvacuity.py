#!/usr/bin/env python3
"""Finite witness for the physical/Gate premises of early_return_public_io_sound.

This checks a concrete zero-input execution in the *ideal exact Gate model*.
It reads the three exported ColumnCell lists in the generated Lean fixture,
reconstructs their expected source/input/output plans, and checks the physical
row, arithmetic-root, multiset-balance, producer-uniqueness, constant, and
public-pin premises. The source/normalized-byte relation is proved separately
by the generated Lean fixture. This checker does not authenticate native
trace openings or prove that LogUp/PCS/FRI verification implies these ideal
premises.
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from pathlib import Path
import re


P = 2**31 - 1
ZERO = (0, 0, 0, 0)
FIXTURE = Path(__file__).resolve().parents[1] / "S31/Gadgets/Functional/GeneratedDirectGateMixedReturn.lean"
FIELDS = ("traceRow", "addFlag", "subFlag", "mulFlag", "pointwiseMulFlag", "in0", "in1", "out", "mults")


@dataclass(frozen=True)
class Cell:
    traceRow: int
    addFlag: int
    subFlag: int
    mulFlag: int
    pointwiseMulFlag: int
    in0: int
    in1: int
    out: int
    mults: int

    @property
    def flags(self) -> tuple[int, int, int, int]:
        return (self.addFlag, self.subFlag, self.mulFlag, self.pointwiseMulFlag)


@dataclass(frozen=True)
class Row:
    in0Address: int
    in1Address: int
    outAddress: int
    flags: tuple[int, int, int, int]
    in0: tuple[int, int, int, int]
    in1: tuple[int, int, int, int]
    output: tuple[int, int, int, int]
    multiplicity: int


def fail_if(condition: bool, description: str) -> None:
    if condition:
        raise AssertionError(description)


def section(text: str, name: str) -> str:
    match = re.search(r"def " + re.escape(name) + r" : List ColumnCell :=\s*\[(.*?)\n  \]", text, re.S)
    if match is None:
        raise AssertionError(f"missing generated {name}")
    return match.group(1)


def cells(text: str, name: str) -> list[Cell]:
    result = []
    for literal in re.findall(r"\{([^{}]+)\}", section(text, name)):
        fields = {key: int(value) for key, value in re.findall(r"(\w+) := (\d+)", literal)}
        fail_if(set(fields) != set(FIELDS), f"malformed {name} cell")
        result.append(Cell(**fields))
    return result


def fixture_number(text: str, name: str) -> int:
    match = re.search(r"def " + re.escape(name) + r" : Nat := (\d+)", text)
    if match is None:
        raise AssertionError(f"missing generated {name}")
    return int(match.group(1))


def certificate(text: str) -> tuple[list[tuple[int, int, int, bool]], int]:
    match = re.search(r"def certificate : Certificate :=\s*\{ instructions := \[(.*?)\],\s*output := (\d+) \}", text, re.S)
    if match is None:
        raise AssertionError("missing generated certificate")
    instructions = [
        (int(i), int(lhs), int(rhs), multiply == "true")
        for i, lhs, rhs, multiply in re.findall(
            r"\{ id := (\d+), lhs := (\d+), rhs := (\d+), multiply := (true|false) \}", match.group(1)
        )
    ]
    fail_if(len(instructions) != 3, "early-return certificate changed")
    return instructions, int(match.group(2))


def make_cell(trace: int, op: str, left: int, right: int, out: int, mults: int) -> Cell:
    flags = {"add": (1, 0, 0, 0), "mul": (0, 0, 1, 0), "pointwise": (0, 0, 0, 1)}[op]
    return Cell(trace, *flags, left, right, out, mults)


def source_uses(instructions: list[tuple[int, int, int, bool]], selected: int, target: int) -> int:
    return sum((lhs == target) + (rhs == target) for _, lhs, rhs, _ in instructions) + 4 * (selected == target)


def expected_plans(instructions: list[tuple[int, int, int, bool]], selected: int, total_adds: int) -> tuple[list[Cell], list[Cell], list[Cell]]:
    source = []
    prior_adds = prior_muls = 0
    for ident, lhs, rhs, multiply in instructions:
        trace = total_adds + 28 + prior_muls if multiply else 3 + prior_adds
        source.append(make_cell(trace, "pointwise" if multiply else "add", 22 + lhs, 22 + rhs, 22 + ident, source_uses(instructions, selected, ident)))
        prior_muls += multiply
        prior_adds += not multiply

    inputs = [make_cell(i, "add", 11 if i == 0 else 16 + 2 * i, 17 + 2 * i, 18 + 2 * i,
                             sum((lhs == 0) + (rhs == 0) for _, lhs, rhs, _ in instructions) if i == 2 else 1)
              for i in range(3)]
    basis = (1, 15, 2, 16)
    inputs += [make_cell(total_adds + 1 + i, "mul", basis[i + 1], 12 + i, 17 + 2 * i, 1) for i in range(3)]
    inputs += [make_cell(3 + prior_adds + i, "add", 11 + i, 0, 3 + i, 1) for i in range(4)]
    inputs += [make_cell(total_adds + 32 + prior_muls + i, "pointwise", 11 + i, 1, 11 + i, 3) for i in range(4)]

    n = len(instructions)
    masks = [23 + n if i == 0 else 21 + n + 3 * i for i in range(4)]
    results = [23 + n + 3 * i for i in range(4)]
    outputs = [make_cell(total_adds + 28 + prior_muls + i, "pointwise", 22 + selected, basis[i], masks[i], 1) for i in range(4)]
    outputs += [make_cell(total_adds + 4 + i, "mul", masks[i + 1], 25 + n + 3 * i, results[i + 1], 1) for i in range(3)]
    outputs += [make_cell(7 + prior_adds + i, "add", results[i], 0, 7 + i, 1) for i in range(4)]
    return source, inputs, outputs


def wire(address: int) -> tuple[int, int, int, int]:
    units = {1: (1, 0, 0, 0), 15: (0, 1, 0, 0), 2: (0, 0, 1, 0), 16: (0, 0, 0, 1)}
    inverse_five = pow(5, -1, P)
    inverses = {
        28: (0, P - 1, 0, 0),
        31: (0, 0, 2 * inverse_five % P, -inverse_five % P),
        34: (0, 0, -inverse_five % P, -2 * inverse_five % P),
    }
    return units.get(address, inverses.get(address, ZERO))


def qm31_mul(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, int, int, int]:
    p = x[2] * y[2] - x[3] * y[3]
    q = x[2] * y[3] + x[3] * y[2]
    return tuple(value % P for value in (
        x[0] * y[0] - x[1] * y[1] + 2 * p - q,
        x[0] * y[1] + x[1] * y[0] + p + 2 * q,
        x[0] * y[2] - x[1] * y[3] + x[2] * y[0] - x[3] * y[1],
        x[0] * y[3] + x[1] * y[2] + x[2] * y[1] + x[3] * y[0],
    ))


def roots(row: Row) -> tuple[int, ...]:
    a, s, m, pm = row.flags
    product = qm31_mul(row.in0, row.in1)
    weighted = tuple((m * product[i] + a * (row.in0[i] + row.in1[i]) +
                      s * (row.in0[i] - row.in1[i]) + pm * row.in0[i] * row.in1[i]) % P for i in range(4))
    return ((a + s + m + pm - 1) % P, *((flag * (flag - 1)) % P for flag in row.flags),
            *((row.output[i] - weighted[i]) % P for i in range(4)))


def row_for_cell(cell: Cell) -> Row:
    return Row(cell.in0, cell.in1, cell.out, cell.flags, wire(cell.in0), wire(cell.in1), wire(cell.out), cell.mults)


def check_witness(mutation: str | None = None) -> dict[str, int]:
    text = FIXTURE.read_text()
    instructions, selected = certificate(text)
    total_adds = fixture_number(text, "observedAddRows")
    fail_if((instructions, selected) !=
            ([(1, 0, 0, True), (2, 0, 1, False), (3, 1, 2, True)], 1),
            "this witness is specific to the generated early-return program")
    trace_rows = fixture_number(text, "observedGateRows")
    fail_if(trace_rows != 512, "generated direct-Gate trace height changed")
    expected = expected_plans(instructions, selected, total_adds)
    observed = tuple(cells(text, name) for name in ("observedColumnCells", "observedInputCells", "observedOutputCells"))
    fail_if(observed != expected, "exported cells differ from source-derived fixed-cell plans")
    source, inputs, outputs = observed
    all_cells = source + inputs + outputs
    fail_if(len(all_cells) != 28 or len({cell.traceRow for cell in all_cells}) != 28, "physical projected rows collide")

    rows = [Row(1000 + i, 1000 + i, 1000 + i, (1, 0, 0, 0), ZERO, ZERO, ZERO, 2) for i in range(trace_rows)]
    for cell in all_cells:
        fail_if(cell.traceRow >= len(rows), "projected row lies beyond the physical trace")
        rows[cell.traceRow] = row_for_cell(cell)
    for cell in all_cells:
        row = rows[cell.traceRow]
        fail_if((row.flags, row.in0Address, row.in1Address, row.outAddress, row.multiplicity) !=
                (cell.flags, cell.in0, cell.in1, cell.out, cell.mults), "physical cell/row mismatch")
        fail_if(any(roots(row)), "installed nine arithmetic roots do not vanish")
    fail_if(any(any(roots(row)) for row in rows), "a physical row has nonzero arithmetic roots")
    fail_if(any(cell.mults <= 0 for cell in inputs + outputs), "public boundary has a zero-use row")
    fail_if(any(source_uses(instructions, selected, ident) > 0 and rows[cell.traceRow].multiplicity == 0
                for (ident, _, _, _), cell in zip(instructions, source)), "used source has no Gate yield")
    fail_if(source_uses(instructions, selected, 3) != 0 or rows[503].multiplicity != 0,
            "final source row is not dead")

    constants = {0: 8, 1: 5, 15: 2, 2: 2, 16: 2, 28: 1, 31: 1, 34: 1}
    external_yields = [(address, wire(address)) for address, count in constants.items() for _ in range(count)]
    external_yields += [(address, ZERO) for address in range(3, 11)]  # Four input and four output pins.
    if mutation == "wrong-selected-claim":
        # The selected result is zero, but public output lane zero claims one.
        external_yields[-4] = (7, (1, 0, 0, 0))
    external_uses = [(address, ZERO) for address in range(3, 11) for _ in range(2)]
    if mutation == "unbalanced-external-use":
        external_uses.pop()
    fail_if(mutation not in (None, "wrong-selected-claim", "unbalanced-external-use"),
            "unknown witness mutation")
    row_uses = [(r.in0Address, r.in0) for r in rows] + [(r.in1Address, r.in1) for r in rows]
    row_yields = [(r.outAddress, r.output) for r in rows for _ in range(r.multiplicity)]
    all_uses = Counter(row_uses + external_uses)
    all_yields = Counter(row_yields + external_yields)
    fail_if(all_uses != all_yields, f"ideal Gate multiset is not balanced: {all_uses - all_yields}, {all_yields - all_uses}")
    produced: dict[int, tuple[int, int, int, int]] = {}
    for address, value in all_yields:
        fail_if(address in produced and produced[address] != value, "produced Gate address has two values")
        produced[address] = value
    for address in (0, 1, 15, 2, 16, 28, 31, 34):
        fail_if(all_yields[(address, wire(address))] < 1, "fixed zero/basis event absent")
    for address in range(3, 11):
        fail_if((address, ZERO) not in external_yields, "public pin event absent")
    fail_if(produced[23] != ZERO, "selected output is not the zero-input result")
    return {"physical_rows": len(rows), "projected_rows": len(all_cells),
            "dead_source_rows": sum(cell.mults == 0 for cell in source),
            "gate_events": sum(all_uses.values()), "external_uses": len(external_uses),
            "external_yields": len(external_yields)}


def check_negative_controls() -> None:
    for mutation in ("unbalanced-external-use", "wrong-selected-claim"):
        try:
            check_witness(mutation)
        except AssertionError as exc:
            if "ideal Gate multiset is not balanced" not in str(exc):
                raise AssertionError(f"{mutation} rejected for the wrong reason: {exc}") from exc
        else:
            raise AssertionError(f"{mutation} was accepted")


if __name__ == "__main__":
    print(check_witness())
    check_negative_controls()
    print("mutation_controls=2 rejected")
