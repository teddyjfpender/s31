"""Independent public main-trace reconstruction for short direct-Gate graphs.

The checked source SSA and public input words determine all 12 base columns
for the reviewed one/two-input, one-to-three-lane direct profile. This is an
honest-trace check; it does not authenticate arbitrary PCS openings.
"""

from __future__ import annotations

from collections import Counter
import hashlib
from typing import Any

from package.direct_gate_main_correspondence import (
    I, IU, INV_I, INV_IU, INV_U, ONE, P, U, ZERO, _operate,
    canonical_column_bytes,
)
from package.correspondence import same_json_shape
from package.direct_gate_schedule import exact_direct_gate_schedule

Q = tuple[int, int, int, int]
KINDS = ("add", "sub", "mul", "pointwise_mul")


def _words(value: Any, lanes: int) -> list[int]:
    if (type(value) is not list or len(value) != lanes or
            any(type(word) is not int or not 0 <= word < P for word in value)):
        raise ValueError("expected canonical public M31 input lanes")
    return value


def source_values(ssa: dict, public_inputs: dict[str, Any]) -> tuple[list[Q], list[int]]:
    """Evaluate the source-derived indexed graph without the production evaluator."""
    lanes, inputs, nodes = ssa["lane_count"], ssa["inputs"], ssa["nodes"]
    if (type(lanes) is not int or not 1 <= lanes <= 3 or
            len(inputs) not in (1, 2) or (len(inputs) == 2 and lanes > 2) or
            type(public_inputs) is not dict or
            set(public_inputs) != {item["name"] for item in inputs}):
        raise ValueError("outside reviewed short-lane public graph")
    raw = [_words(public_inputs[item["name"]], lanes) for item in inputs]
    values: list[Q] = [tuple(words + [0] * (4 - lanes)) for words in raw]  # type: ignore[list-item]
    for ident, node in enumerate(nodes, len(inputs)):
        op = node["op"]
        constant_op = op in ("add_const", "mul_const")
        rhs = node.get("constant") if constant_op else node.get("rhs")
        if (node["id"] != ident or
                op not in ("add", "sub", "mul", "add_const", "mul_const") or
                type(node["lhs"]) is not int or type(rhs) is not int or
                not 0 <= node["lhs"] < ident or
                (constant_op and not 2 <= rhs < P) or
                (not constant_op and not 0 <= rhs < ident)):
            raise ValueError("invalid checked SSA node")
        left = values[node["lhs"]]
        right = (rhs,) * 4 if constant_op else values[rhs]
        values.append(tuple((a + b if op in ("add", "add_const") else
                             a - b if op == "sub" else a * b) % P
                            for a, b in zip(left, right, strict=True)))  # type: ignore[arg-type]
    output = ssa["output"]
    if type(output) is not int or not len(inputs) <= output < len(values):
        raise ValueError("invalid checked SSA output")
    return values, [word for words in raw for word in words] + list(values[output][:lanes])


def expected_columns(ssa: dict, public_inputs: dict[str, Any]) -> tuple[list[list[int]], list[list[int]], list[int]]:
    """Solve the complete source-derived Gate DAG, including padding rows."""
    values, used_public = source_values(ssa, public_inputs)
    lanes, input_count, n_nodes = ssa["lane_count"], len(ssa["inputs"]), len(ssa["nodes"])
    syntax = {"lane_count": lanes, "input_count": input_count,
              "instructions": ssa["nodes"], "output": ssa["output"]}
    gates, n_vars, n_rows, source_gates = exact_direct_gate_schedule(syntax)
    if n_vars != n_rows or n_rows != 512:
        raise ValueError("unexpected short-lane direct trace geometry")
    reads: Counter[int] = Counter()
    for kind in KINDS:
        for gate in gates[kind]:
            reads[gate["in0"]] += 1
            reads[gate["in1"]] += 1
    reads.update((2, *range(3, 11)))
    fixed_rows = [[*(int(opcode == column) for column in range(4)),
                   gate["in0"], gate["in1"], gate["out"], reads[gate["out"]]]
                  for opcode, kind in enumerate(KINDS) for gate in gates[kind]]
    if (len(fixed_rows) != 512 or
            sorted(row[6] for row in fixed_rows) != list(range(512))):
        raise ValueError("source schedule does not own every address once")
    fixed = [[row[column] for row in fixed_rows] for column in range(8)]
    extra = (input_count - 1) * (3 * lanes - 2)
    distinct_constants = {node["constant"] for node in ssa["nodes"]
                          if node["op"] in ("add_const", "mul_const")}
    first_output = 11 + 3 * lanes + extra + n_nodes + len(distinct_constants)
    anchors: dict[int, Q] = {0: ZERO, 1: ONE, 2: U,
                             11 + lanes: I, 12 + lanes: IU}
    for lane, inverse in enumerate((INV_I, INV_U, INV_IU)[:lanes - 1], 1):
        anchors[first_output + 3 * lane - 1] = inverse
    for input_index, item in enumerate(ssa["inputs"]):
        raw_start = 11 if input_index == 0 else 11 + 3 * lanes
        for lane, word in enumerate(_words(public_inputs[item["name"]], lanes)):
            anchors[raw_start + lane] = (word, 0, 0, 0)
    producer = {fixed[6][row]: row for row in range(512)}
    if len(producer) != 512:
        raise ValueError("duplicate direct Gate producer")
    resolved = dict(anchors)
    visiting: set[int] = set()

    def resolve(address: int) -> Q:
        if address in resolved:
            return resolved[address]
        if address not in producer or address in visiting:
            raise ValueError(f"unanchored or cyclic Gate address {address}")
        visiting.add(address)
        row = fixed_rows[producer[address]]
        selector = row[:4]
        if selector.count(1) != 1 or sum(selector) != 1:
            raise ValueError("invalid direct Gate selector")
        output = _operate(selector.index(1), resolve(row[4]), resolve(row[5]))
        visiting.remove(address)
        resolved[address] = output
        return output

    for address in range(512):
        resolve(address)
    main = [[0] * 512 for _ in range(12)]
    for row_index, row in enumerate(fixed_rows):
        left, right, output = (resolved[row[4]], resolved[row[5]], resolved[row[6]])
        selector = row[:4]
        if _operate(selector.index(1), left, right) != output:
            raise ValueError(f"seeded direct Gate row {row_index} is inconsistent")
        for offset, value in ((0, left), (4, right), (8, output)):
            for coordinate in range(4):
                main[offset + coordinate][row_index] = value[coordinate]
    for value, gate in zip(values[len(ssa["inputs"]):], source_gates, strict=True):
        if resolved[gate["out"]] != value:
            raise ValueError("source SSA value differs from direct Gate wire")
    public = used_public + [0] * (8 - len(used_public))
    if len(public) != 8:
        raise ValueError("public ABI exceeds eight words")
    for address, word in enumerate(public, 3):
        if resolved[address] != (word, 0, 0, 0):
            raise ValueError("public copy differs from source assignment")
    return fixed, main, public


def check_export(ssa: dict, public_inputs: dict[str, Any], physical: dict,
                 root_report: dict) -> dict[str, Any]:
    fixed, main, public = expected_columns(ssa, public_inputs)
    if canonical_column_bytes(physical.get("fixed_columns"), 8) != canonical_column_bytes(fixed, 8):
        raise ValueError("native fixed columns differ from checked source")
    if canonical_column_bytes(physical.get("main_columns"), 12) != canonical_column_bytes(main, 12):
        raise ValueError("native main columns differ from checked source")
    if (not same_json_shape(physical.get("public_words"), public) or
            not same_json_shape(root_report.get("public_words"), public)):
        raise ValueError("native public words differ from checked source")
    digest = hashlib.sha256(canonical_column_bytes(main, 12)).hexdigest()
    if root_report.get("main_columns_sha256") != digest:
        raise ValueError("native main digest differs from checked source")
    return {"source_derived_main_columns_sha256": digest,
            "source_derived_main_cells": 6144, "source_derived_public_words": public}
