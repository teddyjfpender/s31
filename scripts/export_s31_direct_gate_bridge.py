#!/usr/bin/env python3
"""Render a bounded source/SSA/native-row instance for the Lean checker.

This is an audit bridge, not a standalone verifier. Package admission first
reparses the exact source bytes and replays the complete direct-gate topology.
The resulting Lean instance reparses the emitted bytes in Lean, checks the
derived SSA and public names, checks exact canonical normalized JSON bytes,
and checks observed source rows and eight exported preprocessed cells against
the formal address, selector, and use-count formulas. It also checks the
eleven exported public-output mask, inverse, and ABI-copy cells. SHA-256
strings are informational in Lean. Fourteen public-input packing and binding
cells are checked by the same bounded bridge.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, check_package, parse_canonical_json,
)


_LEAN_TOKEN = re.compile(
    rb"[ \t\n\v\f\r]+|//[^\n]*|->|\.\*|[()\[\];:{}=+]|"
    rb"[A-Za-z_][A-Za-z_0-9]*|[0-9]+"
)


def _mutated_source_bytes(data: bytes, first_op: str) -> bytes:
    """Flip the first real `let` operator, skipping whitespace and comments."""
    tokens: list[tuple[bytes, int, int]] = []
    position = 0
    while position < len(data):
        match = _LEAN_TOKEN.match(data, position)
        if match is None:
            raise ValueError("source exceeds the Lean bridge ASCII token grammar")
        value = match.group()
        if not value.isspace() and not value.startswith(b"//"):
            tokens.append((value, match.start(), match.end()))
        position = match.end()
    for index, (value, _, _) in enumerate(tokens):
        if value == b"let":
            if index + 6 >= len(tokens):
                raise ValueError("first source let is incomplete")
            expected = b".*" if first_op == "mul" else b"+"
            found, start, end = tokens[index + 4]
            if found != expected:
                raise ValueError("first source operator differs from checked SSA")
            replacement = b"+ " if expected == b".*" else b".*"
            return data[:start] + replacement + data[end:]
    raise ValueError("bounded bridge source has no arithmetic let")


def _byte_list(data: bytes) -> str:
    rows = [data[i:i + 16] for i in range(0, len(data), 16)]
    return "[\n    " + ",\n    ".join(
        ", ".join(str(value) for value in row) for row in rows) + "\n  ]"


def _nat_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def _source_term(instructions: list[dict], output: int, index: int = 0) -> str:
    if index == len(instructions):
        if not 1 <= output <= len(instructions):
            raise ValueError("bounded bridge output is not a let wire")
        return f"(.var ⟨{len(instructions) - output}, by decide⟩)"
    instruction = instructions[index]
    if instruction["id"] != index + 1:
        raise ValueError("nonsequential source SSA in Lean bridge")

    def var(wire: int) -> str:
        if not 0 <= wire <= index:
            raise ValueError("forward source SSA operand in Lean bridge")
        return f"(.var ⟨{index - wire}, by decide⟩)"

    operation = "mul" if instruction["op"] == "mul" else "add"
    value = f"(.{operation} {var(instruction['lhs'])} {var(instruction['rhs'])})"
    return f"(.letValue {value} {_source_term(instructions, output, index + 1)})"


def _certificate(instructions: list[dict], output: int,
                 *, flip_first: bool = False) -> str:
    rows = []
    for index, instruction in enumerate(instructions):
        multiply = instruction["op"] == "mul"
        if flip_first and index == 0:
            multiply = not multiply
        rows.append("{ id := %d, lhs := %d, rhs := %d, multiply := %s }" % (
            instruction["id"], instruction["lhs"], instruction["rhs"],
            "true" if multiply else "false"))
    return "{ instructions := [\n      " + ",\n      ".join(rows) + \
        f"],\n    output := {output} }}"


def _normalized_program(relation: dict) -> str:
    """Render the captured relation, not a source-derived expected Program."""
    if (set(relation) != {"version", "name", "inputs", "nodes", "assertions",
                          "public_outputs"} or
            len(relation["inputs"]) != 1 or relation["assertions"] != [] or
            len(relation["public_outputs"]) != 1):
        raise ValueError("Lean bridge normalized Program is outside fixed schema")
    source_input = relation["inputs"][0]
    if (source_input["kind"] != "m31" or source_input["length"] != 4 or
            source_input["visibility"] != "public"):
        raise ValueError("Lean bridge normalized input differs from four public M31 lanes")
    nodes = []
    for node in relation["nodes"]:
        if node["op"] not in {"add", "mul"}:
            raise ValueError("Lean bridge normalized node is not add or mul")
        nodes.append("{ name := %s, op := .%s, lhs := some %s, rhs := some %s }" % (
            json.dumps(node["name"]), node["op"],
            json.dumps(node["lhs"]), json.dumps(node["rhs"])))
    return ("{ version := %d, name := %s, inputs := "
            "[{ name := %s, shape := ⟨.m31, 4⟩, visibility := .«public» }], "
            "nodes := [%s], assertions := [], outputs := [%s] }" % (
                relation["version"], json.dumps(relation["name"]),
                json.dumps(source_input["name"]), ", ".join(nodes),
                json.dumps(relation["public_outputs"][0])))


def _native_rows(checked: dict, *, change_address: bool = False) -> str:
    source = checked["source_ssa"]["instructions"]
    gates = checked["source_gates"]
    schedule = checked["gate_schedule"]
    counts = checked["gate_counts"]
    if len(source) != len(gates) or len(schedule) != len(source) + 1:
        raise ValueError("source/native schedule lengths differ")
    if counts["sub"] != 1 or counts["mul"] != 27 or sum(counts.values()) != 512:
        raise ValueError("Lean bridge only covers the fixed 512-row direct profile")
    seen_add = seen_mul = 0
    rows = []
    for index, (instruction, gate) in enumerate(zip(source, gates, strict=True)):
        if gate["id"] != instruction["id"] or gate["op"] != instruction["op"]:
            raise ValueError("source/native gate identity differs")
        multiply = instruction["op"] == "mul"
        trace_row = (counts["add"] + 28 + seen_mul) if multiply else (3 + seen_add)
        circuit_row = schedule[index + 1]["qm31_start"]
        in0, in1, out = gate["in0"], gate["in1"], gate["out"]
        if change_address and index == 0:
            in1 += 1
        rows.append("{ circuitRow := %d, traceRow := %d, multiply := %s, "
                    "in0 := %d, in1 := %d, out := %d }" % (
                        circuit_row, trace_row, "true" if multiply else "false",
                        in0, in1, out))
        seen_mul += multiply
        seen_add += not multiply
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def _air_column_rows(checked: dict, topology: dict, *, mutation: str | None = None) -> str:
    """Project the eight actual exported preprocessed cells at source rows."""
    columns = topology["columns"]
    if ([column["id"] for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(column["values"]) != 512 for column in columns)):
        raise ValueError("Lean bridge requires eight complete direct-gate columns")
    instructions = checked["source_ssa"]["instructions"]
    counts = checked["gate_counts"]
    seen_add = seen_mul = 0
    rows = []
    for index, instruction in enumerate(instructions):
        multiply = instruction["op"] == "mul"
        trace_row = (counts["add"] + counts["sub"] + counts["mul"] + seen_mul
                     if multiply else 3 + seen_add)
        if index == 0 and mutation == "trace_row":
            trace_row = trace_row - 1 if trace_row == 511 else trace_row + 1
        values = [column["values"][trace_row] for column in columns]
        if index == 0 and mutation == "selector":
            values[0], values[3] = (1, 0) if multiply else (0, 1)
        if index == 0 and mutation == "address":
            values[5] += 1
        if index == 0 and mutation == "multiplicity":
            values[7] += 1
        rows.append(_format_air_cell(trace_row, values))
        seen_add += not multiply
        seen_mul += multiply
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def _format_air_cell(trace_row: int, values: list[int]) -> str:
    return ("{ traceRow := %d, addFlag := %d, subFlag := %d, mulFlag := %d, "
            "pointwiseMulFlag := %d, in0 := %d, in1 := %d, out := %d, mults := %d }" %
            (trace_row, *values))


def _output_air_rows(checked: dict, topology: dict, *, mutation: str | None = None) -> str:
    """Project four public masks, three inverse products, and four ABI copies."""
    columns = topology["columns"]
    if ([column["id"] for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(column["values"]) != 512 for column in columns)):
        raise ValueError("Lean bridge requires eight complete direct-gate columns")
    instructions = checked["source_ssa"]["instructions"]
    total_adds = checked["gate_counts"]["add"]
    source_muls = sum(instruction["op"] == "mul" for instruction in instructions)
    source_adds = len(instructions) - source_muls
    selected = [
        *(('mask', lane, total_adds + 28 + source_muls + lane) for lane in range(4)),
        *(('inverse', lane, total_adds + 4 + lane) for lane in range(3)),
        *(('copy', lane, 7 + source_adds + lane) for lane in range(4)),
    ]
    rows = []
    for kind, lane, trace_row in selected:
        if mutation == "mask_row" and kind == "mask" and lane == 0:
            trace_row += 1
        values = [column["values"][trace_row] for column in columns]
        if kind == "mask" and lane == 0:
            if mutation == "mask_selector":
                values[0], values[3] = 1, 0
            if mutation == "mask_source":
                values[4] += 1
            if mutation == "mask_multiplicity":
                values[7] += 1
        if mutation == "mask_basis" and kind == "mask" and lane == 1:
            values[5] += 1
        if mutation == "inverse_basis" and kind == "inverse" and lane == 0:
            values[5] += 1
        if mutation == "copy_output" and kind == "copy" and lane == 0:
            values[6] += 1
        rows.append(_format_air_cell(trace_row, values))
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def _input_air_rows(checked: dict, topology: dict, *, mutation: str | None = None) -> str:
    """Project input pack adds/muls, public copies, and M31 self-products."""
    columns = topology["columns"]
    if ([column["id"] for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(column["values"]) != 512 for column in columns)):
        raise ValueError("Lean bridge requires eight complete direct-gate columns")
    instructions = checked["source_ssa"]["instructions"]
    total_adds = checked["gate_counts"]["add"]
    source_muls = sum(instruction["op"] == "mul" for instruction in instructions)
    source_adds = len(instructions) - source_muls
    selected = [
        *(('pack_add', index, index) for index in range(3)),
        *(('pack_mul', index, total_adds + 1 + index) for index in range(3)),
        *(('input_copy', lane, 3 + source_adds + lane) for lane in range(4)),
        *(('input_self', lane, total_adds + 32 + source_muls + lane)
          for lane in range(4)),
    ]
    rows = []
    for kind, index, trace_row in selected:
        values = [column["values"][trace_row] for column in columns]
        if kind == "pack_add" and index == 0 and mutation == "pack_operand":
            values[4] += 1
        if kind == "pack_add" and index == 2 and mutation == "pack_multiplicity":
            values[7] += 1
        if kind == "pack_mul" and index == 0 and mutation == "pack_basis":
            values[4] += 1
        if kind == "input_copy" and index == 0 and mutation == "copy_address":
            values[6] += 1
        if kind == "input_self" and index == 0:
            if mutation == "self_selector":
                values[0], values[3] = 1, 0
            if mutation == "self_multiplicity":
                values[7] += 1
        rows.append(_format_air_cell(trace_row, values))
    return "[\n    " + ",\n    ".join(rows) + "\n  ]"


def render_bridge(package: Path) -> str:
    checked = check_package(package)
    source_bytes = (package / "source.s31").read_bytes()
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != checked["source_sha256"]:
        raise ValueError("checked source digest differs from exact source bytes")
    normalized_bytes = (package / "source.s31.json").read_bytes()
    normalized_digest = hashlib.sha256(normalized_bytes).hexdigest()
    if normalized_digest != checked["relation_sha256"]:
        raise ValueError("checked relation digest differs from exact normalized bytes")
    # check_package validates canonical topology bytes and returns their
    # digest. Parse the exact same captured bytes after checking that digest;
    # a second path read after parsing would reopen the TOCTOU gap.
    topology_bytes = (package / "gate-topology.json").read_bytes()
    topology_digest = hashlib.sha256(topology_bytes).hexdigest()
    if topology_digest != checked["gate_topology_sha256"]:
        raise ValueError("checked topology digest differs from exact topology bytes")
    relation = parse_canonical_json(normalized_bytes, "source.s31.json")
    topology = parse_canonical_json(topology_bytes, "gate-topology.json")
    if topology["n_vars"] != 512:
        raise ValueError("Lean bridge only covers 512 direct variables")
    public_addresses = topology["output"]
    if public_addresses != list(range(2, 11)):
        raise ValueError("Lean bridge requires exact direct public address order")
    changed_public_addresses = public_addresses.copy()
    changed_public_addresses[5], changed_public_addresses[6] = (
        changed_public_addresses[6], changed_public_addresses[5])
    instructions = checked["source_ssa"]["instructions"]
    output_id = checked["source_ssa"]["output"]
    if not instructions or not 1 <= output_id <= len(instructions):
        raise ValueError("Lean bridge requires a bound let output")
    source_input_uses = sum((instruction["lhs"] == 0) + (instruction["rhs"] == 0)
                            for instruction in instructions)
    selected_output_uses = 4 + sum(
        (instruction["lhs"] == output_id) + (instruction["rhs"] == output_id)
        for instruction in instructions)
    counts = checked["gate_counts"]
    public_names = (
        checked["key_core"]["name"],
        checked["source_ssa"]["input"],
        checked["source_ssa"]["output_name"],
    )
    all_names = [relation["inputs"][0]["name"],
                 *(node["name"] for node in relation["nodes"])]
    if any(not name.isascii() for name in (*public_names, *all_names)):
        raise ValueError("Lean byte bridge requires ASCII names")
    lean_names = ", ".join(f"token {json.dumps(name)}" for name in public_names)
    lean_wire_tokens = ", ".join(f"token {json.dumps(name)}" for name in all_names)
    lean_wire_names = ", ".join(json.dumps(name) for name in all_names)
    normalized_program = _normalized_program(relation)
    changed_relation = dict(relation)
    changed_relation["nodes"] = [dict(node) for node in relation["nodes"]]
    changed_relation["nodes"][0]["op"] = (
        "add" if changed_relation["nodes"][0]["op"] == "mul" else "mul")
    changed_program = _normalized_program(changed_relation)
    source_term = _source_term(instructions, output_id)
    changed = [dict(node) for node in instructions]
    changed[0]["op"] = "add" if changed[0]["op"] == "mul" else "mul"
    changed_source = _source_term(changed, output_id)
    byte_list = _byte_list(source_bytes)
    changed_bytes = _mutated_source_bytes(source_bytes, instructions[0]["op"])
    changed_byte_list = _byte_list(changed_bytes)
    first_op_bytes = b'"op": "mul"' if instructions[0]["op"] == "mul" else b'"op": "add"'
    flipped_op_bytes = b'"op": "add"' if instructions[0]["op"] == "mul" else b'"op": "mul"'
    if first_op_bytes not in normalized_bytes:
        raise ValueError("checked normalized relation lacks first source opcode")
    changed_normalized_bytes = normalized_bytes.replace(first_op_bytes, flipped_op_bytes, 1)
    normalized_byte_list = _byte_list(normalized_bytes)
    changed_normalized_byte_list = _byte_list(changed_normalized_bytes)
    output_name = checked["source_ssa"]["output_name"].encode("ascii")
    output_marker = b'"public_outputs": [\n    "' + output_name + b'"'
    if normalized_bytes.count(output_marker) != 1:
        raise ValueError("checked normalized relation lacks a unique public output marker")
    changed_first = b"z" if output_name[:1] != b"z" else b"y"
    changed_output_marker = (b'"public_outputs": [\n    "' + changed_first +
                             output_name[1:] + b'"')
    changed_output_bytes = normalized_bytes.replace(output_marker, changed_output_marker, 1)
    changed_output_byte_list = _byte_list(changed_output_bytes)
    return f'''-- Generated by scripts/export_s31_direct_gate_bridge.py from a checked package.
-- Source SHA-256: {digest}
import S31.Gadgets.Functional.SSADirectGateBridge
import S31.Gadgets.Functional.SSAAirRows
import S31.Gadgets.Functional.SSATextBytes
import S31.Gadgets.Functional.SSANormalizedBytes
import S31.Gadgets.Functional.SSAAirColumnCells
import S31.Gadgets.Functional.SSAOutputAirCells
import S31.Gadgets.Functional.SSAInputAirCells
import S31.Gadgets.Functional.SSAGeneralNamedExecution

set_option maxRecDepth 4096

namespace S31.Functional.GeneratedDirectGateBridge

open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirRows
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAGeneralNamedTopology
open S31.Functional.SSAGeneralNamedExecution
open S31.Functional.SSANativeTopologyCheck
open S31.Functional.SSANamedExecution (laneValue)

def sourceBytes : List Nat := {byte_list}
-- Informational digest from the outer package checker; Lean does not hash sourceBytes.
def sourceSha256 : String := "{digest}"
def changedSourceBytes : List Nat := {changed_byte_list}
def normalizedBytes : List Nat := {normalized_byte_list}
-- Informational digest from the outer package checker; Lean does not hash normalizedBytes.
def normalizedSha256 : String := "{normalized_digest}"
def changedNormalizedOpcodeBytes : List Nat := {changed_normalized_byte_list}
def changedNormalizedOutputBytes : List Nat := {changed_output_byte_list}

def source : Source 1 :=
  {source_term}

def certificate : Certificate :=
  {_certificate(instructions, output_id)}

-- This Program is rendered from the captured normalized JSON, while the
-- names below are independently compared to Lean's parse of sourceBytes.
def programName : String := {json.dumps(public_names[0])}
def wireNames : List String := [{lean_wire_names}]
def normalizedProgram : S31.Program :=
  {normalized_program}
def changedOpcodeProgram : S31.Program :=
  {changed_program}

def observedRows : List NativeSourceRow :=
  {_native_rows(checked)}

-- Physical source wire 0 is packed at circuit address 22. This projection
-- preserves the observed gate order and operation flags while renumbering
-- physical source addresses to the logical SSA wire IDs.
def projectedGates : List Gate :=
  observedRows.map (fun row =>
    {{ in0 := row.in0 - 22, in1 := row.in1 - 22,
       out := row.out - 22, multiply := row.multiply }})
def changedOpcodeGates : List Gate :=
  projectedGates.modifyHead (fun gate => {{ gate with multiply := !gate.multiply }})

def observedColumnCells : List ColumnCell :=
  {_air_column_rows(checked, topology)}
def changedSelectorCells : List ColumnCell :=
  {_air_column_rows(checked, topology, mutation="selector")}
def changedColumnAddressCells : List ColumnCell :=
  {_air_column_rows(checked, topology, mutation="address")}
def changedTraceRowCells : List ColumnCell :=
  {_air_column_rows(checked, topology, mutation="trace_row")}
def changedMultiplicityCells : List ColumnCell :=
  {_air_column_rows(checked, topology, mutation="multiplicity")}

def observedOutputCells : List ColumnCell :=
  {_output_air_rows(checked, topology)}
def changedOutputMaskSelector : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="mask_selector")}
def changedOutputMaskSource : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="mask_source")}
def changedOutputMaskRow : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="mask_row")}
def changedOutputMaskMultiplicity : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="mask_multiplicity")}
def changedOutputMaskBasis : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="mask_basis")}
def changedOutputInverseBasis : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="inverse_basis")}
def changedOutputCopyAddress : List ColumnCell :=
  {_output_air_rows(checked, topology, mutation="copy_output")}
def observedPublicAddresses : List Nat := {_nat_list(public_addresses)}
def changedPublicAddressOrder : List Nat := {_nat_list(changed_public_addresses)}

def observedInputCells : List ColumnCell :=
  {_input_air_rows(checked, topology)}
def changedPackOperand : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="pack_operand")}
def changedPackMultiplicity : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="pack_multiplicity")}
def changedPackBasis : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="pack_basis")}
def changedInputCopyAddress : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="copy_address")}
def changedInputSelfSelector : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="self_selector")}
def changedInputSelfMultiplicity : List ColumnCell :=
  {_input_air_rows(checked, topology, mutation="self_multiplicity")}

def observedAddRows : Nat := {counts['add']}
def observedGateRows : Nat := {sum(counts.values())}
def observedVariables : Nat := {topology['n_vars']}

theorem source_byte_count : sourceBytes.length = {len(source_bytes)} := by decide
theorem source_digest_length : sourceSha256.length = 64 := by decide
theorem bytes_parse_to_certificate :
    (parseBytes sourceBytes).map Parsed.certificate = some certificate := by decide
theorem bytes_parse_public_names :
    (parseBytes sourceBytes).map
      (fun p => (p.circuitName, p.inputName, p.outputName)) =
      some ({lean_names}) := by decide
theorem bytes_parse_all_wire_names :
    (parseBytes sourceBytes).map Parsed.wireNames =
      some [{lean_wire_tokens}] := by decide
theorem normalized_bytes_check :
    checkRelation sourceBytes normalizedBytes = some certificate := by decide
theorem changed_normalized_opcode_rejected :
    checkRelation sourceBytes changedNormalizedOpcodeBytes = none := by decide
theorem changed_normalized_public_output_rejected :
    checkRelation sourceBytes changedNormalizedOutputBytes = none := by decide
theorem changed_bytes_change_certificate :
    (parseBytes changedSourceBytes).map Parsed.certificate ≠
      some certificate := by decide
theorem source_ssa_checked : check source certificate = some () := by decide
theorem deterministic_emitter_matches : compile source = certificate := by decide
theorem source_native_rows_match :
    observedRows = expectedRows certificate observedAddRows := by decide
theorem named_program_source_rows_checked :
    checkNamedSourceRows source certificate programName wireNames
      normalizedProgram projectedGates =
      some (List.range (certificate.instructions.length + 1)) := by decide
theorem changed_named_opcode_rejected :
    checkNamedSourceRows source certificate programName wireNames
      changedOpcodeProgram projectedGates = none := by decide
theorem changed_projected_gate_rejected :
    checkNamedSourceRows source certificate programName wireNames
      normalizedProgram changedOpcodeGates = none := by decide
theorem observed_source_columns_match :
    observedColumnCells = expectedCells certificate observedAddRows := by decide
theorem changed_selector_cell_rejected :
    changedSelectorCells ≠ expectedCells certificate observedAddRows := by decide
theorem changed_column_address_cell_rejected :
    changedColumnAddressCells ≠ expectedCells certificate observedAddRows := by decide
theorem changed_trace_row_cell_rejected :
    changedTraceRowCells ≠ expectedCells certificate observedAddRows := by decide
theorem changed_multiplicity_cell_rejected :
    changedMultiplicityCells ≠ expectedCells certificate observedAddRows := by decide
theorem observed_output_cells_match :
    observedOutputCells = expectedOutputCells certificate observedAddRows := by decide
theorem selected_source_output_use_count :
    sourceUses certificate certificate.output = {selected_output_uses} := by decide
theorem changed_output_mask_selector_rejected :
    changedOutputMaskSelector ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_mask_source_rejected :
    changedOutputMaskSource ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_mask_row_rejected :
    changedOutputMaskRow ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_mask_multiplicity_rejected :
    changedOutputMaskMultiplicity ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_mask_basis_rejected :
    changedOutputMaskBasis ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_inverse_basis_rejected :
    changedOutputInverseBasis ≠ expectedOutputCells certificate observedAddRows := by decide
theorem changed_output_copy_address_rejected :
    changedOutputCopyAddress ≠ expectedOutputCells certificate observedAddRows := by decide
theorem observed_public_addresses_match :
    observedPublicAddresses = expectedPublicAddresses := by decide
theorem changed_public_address_order_rejected :
    changedPublicAddressOrder ≠ expectedPublicAddresses := by decide
theorem observed_input_cells_match :
    observedInputCells = expectedInputCells certificate observedAddRows := by decide
theorem source_input_use_count : sourceInputUses certificate = {source_input_uses} := by decide
theorem changed_pack_operand_rejected :
    changedPackOperand ≠ expectedInputCells certificate observedAddRows := by decide
theorem changed_pack_multiplicity_rejected :
    changedPackMultiplicity ≠ expectedInputCells certificate observedAddRows := by decide
theorem changed_pack_basis_rejected :
    changedPackBasis ≠ expectedInputCells certificate observedAddRows := by decide
theorem changed_input_copy_address_rejected :
    changedInputCopyAddress ≠ expectedInputCells certificate observedAddRows := by decide
theorem changed_input_self_selector_rejected :
    changedInputSelfSelector ≠ expectedInputCells certificate observedAddRows := by decide
theorem changed_input_self_multiplicity_rejected :
    changedInputSelfMultiplicity ≠ expectedInputCells certificate observedAddRows := by decide
theorem complete_native_shape :
    observedGateRows = 512 ∧ observedVariables = 512 := by decide

def changedSource : Source 1 :=
  {changed_source}

def changedOpcode : Certificate :=
  {_certificate(instructions, output_id, flip_first=True)}

theorem changed_bytes_parse_changed_opcode :
    (parseBytes changedSourceBytes).map Parsed.certificate =
      some changedOpcode := by decide

def changedAddressRows : List NativeSourceRow :=
  {_native_rows(checked, change_address=True)}

theorem changed_source_rejected : check changedSource certificate = none := by decide
theorem changed_opcode_rejected : check source changedOpcode = none := by decide
theorem changed_address_rejected :
    changedAddressRows ≠ expectedRows certificate observedAddRows := by decide

/-- Source semantics for every four-lane input follow from the concrete
certificate check. The native-row premise remains a package-checker output,
and lookup/PCS soundness remains outside this theorem. -/
theorem checked_instance_sound (input : Lanes) :
    executeNormalized certificate input =
      some (source.value (fun _ => input)) :=
  (checked_rows_source_sound source certificate input observedRows
    observedAddRows source_ssa_checked source_native_rows_match).2

/-- The same result now starts from the actual embedded source bytes and
requires exact equality with the embedded canonical normalized JSON bytes.
Python's emitted Lean source term is not a premise of this theorem. -/
theorem checked_bytes_sound (input : Lanes) :
    executeNormalized certificate input = denotation sourceBytes input :=
  checked_relation_sound sourceBytes normalizedBytes certificate input
    normalized_bytes_check

/-- The captured normalized JSON runs through the actual named evaluator.
The admission test checks the package before rendering these constants;
Lean's byte and structural checks bind this concrete generated instance. -/
theorem checked_named_environment (assignment : S31.Assignment)
    (input : Lanes)
    (hprivate : assignment.privateInputs = [])
    (hinput : S31.assigned assignment.publicInputs (nameAt wireNames 0)
      ⟨.m31, 4⟩ = .ok (laneValue input)) :
    ∃ env,
      normalizedProgram.environment assignment = .ok env ∧
      S31.lookup env (nameAt wireNames certificate.output) =
        some (laneValue (source.value (fun _ => input))) :=
  checked_named_environment_sound wireNames source certificate programName
    normalizedProgram projectedGates
    (List.range (certificate.instructions.length + 1)) assignment input
    named_program_source_rows_checked hprivate hinput

/-- The named result is also the denotation of the captured source bytes,
because Lean separately checked the exact normalized JSON byte sequence. -/
theorem checked_named_source_bytes (assignment : S31.Assignment)
    (input : Lanes)
    (hprivate : assignment.privateInputs = [])
    (hinput : S31.assigned assignment.publicInputs (nameAt wireNames 0)
      ⟨.m31, 4⟩ = .ok (laneValue input)) :
    ∃ env,
      normalizedProgram.environment assignment = .ok env ∧
      (∃ value, S31.lookup env (nameAt wireNames certificate.output) =
        some (laneValue value) ∧ denotation sourceBytes input = some value) := by
  obtain ⟨env, henv, hlookup⟩ :=
    checked_named_environment assignment input hprivate hinput
  refine ⟨env, henv, source.value (fun _ => input), hlookup, ?_⟩
  rw [← checked_bytes_sound input]
  exact (checked_instance_sound input)

/-- Exact source selectors, addresses and output use counts from the exported
preprocessed cells agree with the SSA-derived row plan. The byte relation
premise is discharged for this concrete package instance. -/
theorem checked_column_cells_sound (input : Lanes) :
    observedColumnCells = expectedCells certificate observedAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  checked_air_cells_sound sourceBytes normalizedBytes certificate input
    observedAddRows observedColumnCells normalized_bytes_check
    observed_source_columns_match

/-- The same exact byte admission also fixes the eleven exported public
output rows, subject to the package-to-Lean artifact premise. -/
theorem checked_output_cells_sound_instance (input : Lanes) :
    observedOutputCells = expectedOutputCells certificate observedAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  checked_output_cells_sound sourceBytes normalizedBytes certificate input
    observedAddRows observedOutputCells normalized_bytes_check
    observed_output_cells_match

/-- Four public M31 words pack into the SSA input wire at address 22. The
value relation and lookup authentication remain native premises. -/
theorem checked_input_cells_sound_instance (input : Lanes) :
    observedInputCells = expectedInputCells certificate observedAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  checked_input_cells_sound sourceBytes normalizedBytes certificate input
    observedAddRows observedInputCells normalized_bytes_check
    observed_input_cells_match

/-- Any complete accepted local arithmetic-row trace for these exact source
instructions has the source result, provided the row operands are the values
authenticated at their addressed prior wires. This does not discharge that
lookup premise or establish PCS binding of the observed row artifact. -/
theorem checked_instance_air_claim (input claimed : Lanes)
    (final : List Lanes)
    (hrows : AcceptsTrace [input] certificate.instructions final)
    (hclaim : final[certificate.output]? = some claimed) :
    observedRows = expectedRows certificate observedAddRows ∧
      observedColumnCells = expectedCells certificate observedAddRows ∧
      observedOutputCells = expectedOutputCells certificate observedAddRows ∧
      observedInputCells = expectedInputCells certificate observedAddRows ∧
      observedPublicAddresses = expectedPublicAddresses ∧
      denotation sourceBytes input = some claimed := by
  have hrun := accepted_trace_executes hrows
  have hbytes := checked_bytes_sound input
  rw [execute_normalized_eq_execute] at hbytes
  simp [execute, hrun, hclaim] at hbytes
  exact ⟨source_native_rows_match, observed_source_columns_match,
    observed_output_cells_match, observed_input_cells_match,
    observed_public_addresses_match, hbytes.symm⟩

end S31.Functional.GeneratedDirectGateBridge
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true",
                        help="require the output to match regenerated Lean source")
    args = parser.parse_args()
    rendered = render_bridge(args.package)
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            raise SystemExit("checked native bridge differs from generated Lean source")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
