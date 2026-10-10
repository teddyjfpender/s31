#!/usr/bin/env python3
"""Render a bounded source/SSA/native-row instance for the Lean checker.

This is an audit bridge, not a standalone verifier. Package admission first
reparses the exact source bytes and replays the complete direct-gate topology.
The resulting Lean instance reparses the emitted bytes in Lean, checks the
derived SSA and public names, and checks observed source rows against the
formal address formula. The SHA-256 string is not verified in Lean.
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

from package.correspondence import check_package, read_canonical_json  # noqa: E402


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


def _source_term(instructions: list[dict], index: int = 0) -> str:
    if index == len(instructions):
        return "(.var ⟨0, by decide⟩)"
    instruction = instructions[index]
    if instruction["id"] != index + 1:
        raise ValueError("nonsequential source SSA in Lean bridge")

    def var(wire: int) -> str:
        if not 0 <= wire <= index:
            raise ValueError("forward source SSA operand in Lean bridge")
        return f"(.var ⟨{index - wire}, by decide⟩)"

    operation = "mul" if instruction["op"] == "mul" else "add"
    value = f"(.{operation} {var(instruction['lhs'])} {var(instruction['rhs'])})"
    return f"(.letValue {value} {_source_term(instructions, index + 1)})"


def _certificate(instructions: list[dict], *, flip_first: bool = False) -> str:
    rows = []
    for index, instruction in enumerate(instructions):
        multiply = instruction["op"] == "mul"
        if flip_first and index == 0:
            multiply = not multiply
        rows.append("{ id := %d, lhs := %d, rhs := %d, multiply := %s }" % (
            instruction["id"], instruction["lhs"], instruction["rhs"],
            "true" if multiply else "false"))
    return "{ instructions := [\n      " + ",\n      ".join(rows) + \
        f"],\n    output := {instructions[-1]['id']} }}"


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


def render_bridge(package: Path) -> str:
    checked = check_package(package)
    source_bytes = (package / "source.s31").read_bytes()
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != checked["source_sha256"]:
        raise ValueError("checked source digest differs from exact source bytes")
    topology = read_canonical_json(package / "gate-topology.json")
    if topology["n_vars"] != 512:
        raise ValueError("Lean bridge only covers 512 direct variables")
    instructions = checked["source_ssa"]["instructions"]
    if not instructions or checked["source_ssa"]["output"] != instructions[-1]["id"]:
        raise ValueError("Lean bridge requires final SSA output")
    counts = checked["gate_counts"]
    public_names = (
        checked["key_core"]["name"],
        checked["source_ssa"]["input"],
        checked["source_ssa"]["output_name"],
    )
    if any(not name.isascii() for name in public_names):
        raise ValueError("Lean byte bridge requires ASCII public names")
    lean_names = ", ".join(f"token {json.dumps(name)}" for name in public_names)
    source_term = _source_term(instructions)
    changed = [dict(node) for node in instructions]
    changed[0]["op"] = "add" if changed[0]["op"] == "mul" else "mul"
    changed_source = _source_term(changed)
    byte_rows = [source_bytes[i:i + 16] for i in range(0, len(source_bytes), 16)]
    byte_list = "[\n    " + ",\n    ".join(
        ", ".join(str(value) for value in row) for row in byte_rows) + "\n  ]"
    changed_bytes = _mutated_source_bytes(source_bytes, instructions[0]["op"])
    changed_rows = [changed_bytes[i:i + 16] for i in range(0, len(changed_bytes), 16)]
    changed_byte_list = "[\n    " + ",\n    ".join(
        ", ".join(str(value) for value in row) for row in changed_rows) + "\n  ]"
    return f'''-- Generated by scripts/export_s31_direct_gate_bridge.py from a checked package.
-- Source SHA-256: {digest}
import S31.Gadgets.Functional.SSADirectGateBridge
import S31.Gadgets.Functional.SSAAirRows
import S31.Gadgets.Functional.SSATextBytes

set_option maxRecDepth 4096

namespace S31.Functional.GeneratedDirectGateBridge

open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirRows
open S31.Functional.SSATextBytes

def sourceBytes : List Nat := {byte_list}
-- Informational digest from the outer package checker; Lean does not hash sourceBytes.
def sourceSha256 : String := "{digest}"
def changedSourceBytes : List Nat := {changed_byte_list}

def source : Source 1 :=
  {source_term}

def certificate : Certificate :=
  {_certificate(instructions)}

def observedRows : List NativeSourceRow :=
  {_native_rows(checked)}

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
theorem changed_bytes_change_certificate :
    (parseBytes changedSourceBytes).map Parsed.certificate ≠
      some certificate := by decide
theorem source_ssa_checked : check source certificate = some () := by decide
theorem deterministic_emitter_matches : compile source = certificate := by decide
theorem source_native_rows_match :
    observedRows = expectedRows certificate observedAddRows := by decide
theorem complete_native_shape :
    observedGateRows = 512 ∧ observedVariables = 512 := by decide

def changedSource : Source 1 :=
  {changed_source}

def changedOpcode : Certificate :=
  {_certificate(instructions, flip_first=True)}

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

/-- The same result now starts from the actual embedded source bytes. The
certificate is derived by the Lean byte parser; Python's emitted Lean source
term is not a premise of this theorem. -/
theorem checked_bytes_sound (input : Lanes) :
    executeNormalized certificate input = denotation sourceBytes input :=
  parsed_certificate_sound sourceBytes input certificate bytes_parse_to_certificate

/-- Any complete accepted local arithmetic-row trace for these exact source
instructions has the source result, provided the row operands are the values
authenticated at their addressed prior wires. This does not discharge that
lookup premise or establish PCS binding of the observed row artifact. -/
theorem checked_instance_air_claim (input claimed : Lanes)
    (final : List Lanes)
    (hrows : AcceptsTrace [input] certificate.instructions final)
    (hclaim : final[certificate.output]? = some claimed) :
    observedRows = expectedRows certificate observedAddRows ∧
      denotation sourceBytes input = some claimed := by
  have hrun := accepted_trace_executes hrows
  have hbytes := checked_bytes_sound input
  rw [execute_normalized_eq_execute] at hbytes
  simp [execute, hrun, hclaim] at hbytes
  exact ⟨source_native_rows_match, hbytes.symm⟩

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
