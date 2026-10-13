"""Independent public four-lane direct-Gate base-trace reconstruction.

The normalized source and exact fixed schedule determine every base witness
word for this bounded public fragment. This host model does not inspect native
main columns while deriving them. It does not authenticate PCS openings;
callers must separately verify a proof and join its main commitment root.
"""

from __future__ import annotations

from collections import Counter
import hashlib
import struct
from typing import Any

from package.direct_gate_schedule import exact_direct_gate_schedule

P = (1 << 31) - 1
Q = tuple[int, int, int, int]
KINDS = ("add", "sub", "mul", "pointwise_mul")
ZERO: Q = (0, 0, 0, 0)
ONE: Q = (1, 0, 0, 0)
U: Q = (0, 0, 1, 0)
I: Q = (0, 1, 0, 0)
IU: Q = (0, 0, 0, 1)
INV5 = pow(5, -1, P)
INV_I: Q = (0, P - 1, 0, 0)
INV_U: Q = (0, 0, 2 * INV5 % P, -INV5 % P)
INV_IU: Q = (0, 0, -INV5 % P, -2 * INV5 % P)


def _four_words(words: Any) -> Q:
    if (type(words) not in (list, tuple) or len(words) != 4 or
            any(type(word) is not int or not 0 <= word < P for word in words)):
        raise ValueError("expected four canonical M31 input words")
    return tuple(words)  # type: ignore[return-value]


def source_values(syntax: dict, words: Any) -> tuple[list[Q], Q]:
    """Evaluate compact normalized SSA, including v3 CSE and early return."""
    values = [_four_words(words)]
    instructions = syntax.get("instructions")
    if type(instructions) is not list or not 1 <= len(instructions) <= 16:
        raise ValueError("expected 1..16 compact arithmetic instructions")
    for ident, item in enumerate(instructions, 1):
        if (type(item) is not dict or item.get("id") != ident or
                item.get("op") not in ("add", "sub", "mul") or
                type(item.get("lhs")) is not int or type(item.get("rhs")) is not int or
                not 0 <= item["lhs"] < ident or not 0 <= item["rhs"] < ident):
            raise ValueError("invalid compact source instruction")
        left, right = values[item["lhs"]], values[item["rhs"]]
        op = item["op"]
        values.append(tuple((a + b if op == "add" else a - b if op == "sub" else a * b) % P
                            for a, b in zip(left, right, strict=True)))
    output = syntax.get("output")
    if type(output) is not int or not 1 <= output < len(values):
        raise ValueError("invalid compact source return")
    return values, values[output]


def expected_fixed_columns(syntax: dict) -> list[list[int]]:
    """Build all eight 512-row fixed columns without reading a native export."""
    gates, n_vars, rows, _ = exact_direct_gate_schedule(syntax)
    if (n_vars != 512 or rows != 512 or
            sum(len(gates[kind]) for kind in KINDS) != 512):
        raise ValueError("source schedule is not a complete direct-Gate roster")
    reads: Counter[int] = Counter()
    for kind in KINDS:
        for gate in gates[kind]:
            reads[gate["in0"]] += 1
            reads[gate["in1"]] += 1
    reads.update((2, *range(3, 11)))  # one unit and eight public feeder uses
    rows_fixed = [
        [*(int(opcode == column) for column in range(4)),
         gate["in0"], gate["in1"], gate["out"], reads[gate["out"]]]
        for opcode, kind in enumerate(KINDS) for gate in gates[kind]
    ]
    if sorted(row[6] for row in rows_fixed) != list(range(512)):
        raise ValueError("source schedule lacks exactly one producer per address")
    return [[row[column] for row in rows_fixed] for column in range(8)]


def _qm31_mul(x: Q, y: Q) -> Q:
    p = x[2] * y[2] - x[3] * y[3]
    q = x[2] * y[3] + x[3] * y[2]
    return tuple(value % P for value in (
        x[0] * y[0] - x[1] * y[1] + 2 * p - q,
        x[0] * y[1] + x[1] * y[0] + p + 2 * q,
        x[0] * y[2] - x[1] * y[3] + x[2] * y[0] - x[3] * y[1],
        x[0] * y[3] + x[1] * y[2] + x[2] * y[1] + x[3] * y[0],
    ))  # type: ignore[return-value]


def _operate(opcode: int, left: Q, right: Q) -> Q:
    if opcode == 0:
        return tuple((a + b) % P for a, b in zip(left, right, strict=True))  # type: ignore[return-value]
    if opcode == 1:
        return tuple((a - b) % P for a, b in zip(left, right, strict=True))  # type: ignore[return-value]
    if opcode == 2:
        return _qm31_mul(left, right)
    if opcode == 3:
        return tuple(a * b % P for a, b in zip(left, right, strict=True))  # type: ignore[return-value]
    raise ValueError("invalid Gate opcode")


def expected_main_columns(syntax: dict, words: Any) -> tuple[list[list[int]], list[int]]:
    """Solve the fixed Gate DAG from source words and public input anchors.

    Self-copy seed rows are checked after the solve. All other addresses must
    resolve without cycles; every source SSA value and public copy is checked.
    The returned columns are in native column-major order (12 × 512).
    """
    values, result = source_values(syntax, words)
    fixed = expected_fixed_columns(syntax)
    n = len(syntax["instructions"])
    anchors: dict[int, Q] = {
        0: ZERO, 1: ONE, 2: U, 15: I, 16: IU,
        25 + n: INV_I, 28 + n: INV_U, 31 + n: INV_IU,
    }
    anchors.update({11 + i: (values[0][i], 0, 0, 0) for i in range(4)})
    producers = {fixed[6][row]: row for row in range(512)}
    if len(producers) != 512:
        raise ValueError("fixed roster producer addresses are not unique")
    resolved = dict(anchors)
    visiting: set[int] = set()

    def resolve(address: int) -> Q:
        if address in resolved:
            return resolved[address]
        if address in visiting:
            raise ValueError(f"cyclic unanchored Gate address {address}")
        visiting.add(address)
        row = producers[address]
        selector = tuple(fixed[column][row] for column in range(4))
        if selector.count(1) != 1 or sum(selector) != 1:
            raise ValueError(f"invalid Gate selector at row {row}")
        left = resolve(fixed[4][row])
        right = resolve(fixed[5][row])
        result_value = _operate(selector.index(1), left, right)
        visiting.remove(address)
        resolved[address] = result_value
        return result_value

    for address in range(512):
        resolve(address)
    columns = [[0] * 512 for _ in range(12)]
    for row in range(512):
        selector = tuple(fixed[column][row] for column in range(4))
        if selector.count(1) != 1 or sum(selector) != 1:
            raise ValueError(f"invalid Gate selector at row {row}")
        left = resolved[fixed[4][row]]
        right = resolved[fixed[5][row]]
        output = resolved[fixed[6][row]]
        if _operate(selector.index(1), left, right) != output:
            raise ValueError(f"Gate arithmetic differs at seeded row {row}")
        for offset, value in ((0, left), (4, right), (8, output)):
            for lane in range(4):
                columns[offset + lane][row] = value[lane]
    if resolved[22] != values[0]:
        raise ValueError("input packing differs from normalized source")
    for ident, value in enumerate(values[1:], 1):
        if resolved[22 + ident] != value:
            raise ValueError(f"source wire {ident} differs from normalized source")
    public = [*values[0], *result]
    for address, word in enumerate(public, 3):
        if resolved[address] != (word, 0, 0, 0):
            raise ValueError(f"public word at address {address} differs")
    return columns, public


def canonical_column_bytes(columns: Any, count: int) -> bytes:
    if (type(columns) is not list or len(columns) != count or
            any(type(column) is not list or len(column) != 512 or
                any(type(word) is not int or not 0 <= word < P for word in column)
                for column in columns)):
        raise ValueError("invalid canonical direct-Gate column shape or M31 word")
    return b"".join(struct.pack("<I", word) for column in columns for word in column)


def check_export(syntax: dict, words: Any, physical: dict, root_report: dict) -> dict:
    """Compare a native public export/root report to all independently derived cells."""
    fixed = expected_fixed_columns(syntax)
    main, public = expected_main_columns(syntax, words)
    actual_fixed = physical.get("fixed_columns")
    actual_main = physical.get("main_columns")
    if canonical_column_bytes(actual_fixed, 8) != canonical_column_bytes(fixed, 8):
        raise ValueError("native fixed columns differ from source-derived schedule")
    if canonical_column_bytes(actual_main, 12) != canonical_column_bytes(main, 12):
        raise ValueError("native main columns differ from source-derived full trace")
    if (physical.get("public_words") != public or
            root_report.get("public_words") != public):
        raise ValueError("native public claim differs from normalized source")
    digest = hashlib.sha256(canonical_column_bytes(main, 12)).hexdigest()
    if root_report.get("main_columns_sha256") != digest:
        raise ValueError("native main digest differs from source-derived full trace")
    return {"source_derived_public_words": public,
            "source_derived_main_columns_sha256": digest,
            "source_derived_main_cells": 6144}
