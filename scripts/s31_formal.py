#!/usr/bin/env python3
"""Deterministically bind S31's Lean inventory/constants to repository sources.

Generation does not establish compiler correctness. The committed bindings make
semantic source changes visible to the formal CI gate and its reviewer.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENGINE_ROOT = ROOT / "deps/stwo-zig"
if __package__ in (None, ""):
    sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ENGINE_ROOT))
from scripts.s31_formal_lib.checks import (
    FormalError, check_audit, check_coverage, check_kernel_log, check_schedule_report,
    inventory, render_coverage,
)
from scripts.s31_formal_lib.protocol_order import check_protocol_order
from scripts.riscv_refinement import _skip_lean_string, _strip_lean_comments
from scripts.riscv_refinement_lib.model import RefinementError

FORMAL = ROOT / "formal/s31"
RELATION = "src/frontends/s31/language/relation.zig"
POSEIDON = "src/frontends/riscv/air/memory_commitment/poseidon2_constants.zig"
SHA = "src/frontends/riscv/air/guest_precompile/sha256_compression.zig"
SIGMA = "src/core/crypto/blake_sigma.zig"
GATE_WITNESS = "src/frontends/circuit/witness/components.zig"
QM31_EVALUATOR = "src/frontends/circuit/air_eval/manual/circuit.zig"
TEXT_SQUARE4 = "src/frontends/s31/examples/arithmetic/functional_square4.s31"
TEXT_POLY4 = "src/frontends/s31/examples/arithmetic/functional_poly4.s31"
TEXT_POLY4_DIRECT = "src/frontends/s31/examples/arithmetic/functional_poly4_manual.s31"
TEXT_CURRIED = "src/frontends/s31/examples/arithmetic/curried_sum.s31"
TEXT_CURRIED_DIRECT = "src/frontends/s31/examples/arithmetic/curried_sum_manual.s31"
TEXT_NAMED_SQUARE = "src/frontends/s31/examples/arithmetic/named_square4.s31"
TEXT_NAMED_SQUARE_DIRECT = "src/frontends/s31/examples/arithmetic/named_square4_manual.s31"
TEXT_TUPLE_SUM = "src/frontends/s31/examples/arithmetic/tuple_square_sum.s31"
TEXT_TUPLE_SUM_DIRECT = "src/frontends/s31/examples/arithmetic/tuple_square_sum_manual.s31"
TEXT_STATIC_STEP = "src/frontends/s31/examples/recurrence/functional_step16.s31"
TEXT_STATIC_STEP_DIRECT = "src/frontends/s31/examples/recurrence/functional_step16_manual.s31"
TEXT_CAPTURED_STEP = "src/frontends/s31/examples/recurrence/captured_step16.s31"
TEXT_CAPTURED_STEP_DIRECT = "src/frontends/s31/examples/recurrence/captured_step16_manual.s31"
TEXT_RETURNED_MIX = "src/frontends/s31/examples/recurrence/returned_mix4_3.s31"
TEXT_RETURNED_MIX_DIRECT = "src/frontends/s31/examples/recurrence/returned_mix4_3_manual.s31"
BINDINGS = [
    RELATION,
    TEXT_SQUARE4,
    TEXT_POLY4,
    TEXT_POLY4_DIRECT,
    TEXT_CURRIED,
    TEXT_CURRIED_DIRECT,
    TEXT_NAMED_SQUARE,
    TEXT_NAMED_SQUARE_DIRECT,
    TEXT_TUPLE_SUM,
    TEXT_TUPLE_SUM_DIRECT,
    TEXT_STATIC_STEP,
    TEXT_STATIC_STEP_DIRECT,
    TEXT_CAPTURED_STEP,
    TEXT_CAPTURED_STEP_DIRECT,
    TEXT_RETURNED_MIX,
    TEXT_RETURNED_MIX_DIRECT,
    "src/frontends/s31/build.zig",
    "src/frontends/s31/entry/export_square4_topology.zig",
    "src/frontends/s31/tools/formal/export_square4_topology.zig",
    "src/frontends/s31/language/canonical.zig",
    "src/frontends/s31/language/relation_compiler.zig",
    "src/frontends/s31/language/gadgets/integer_multiply.zig",
    "src/frontends/s31/language/gadgets/integer_bits.zig",
    "src/frontends/s31/language/gadgets/integer_division.zig",
    "src/frontends/s31/language/finalization/constant_base.zig",
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/library/hash/poseidon2.zig",
    "src/core/crypto/blake2s_terminal_parallel.zig",
    "src/frontends/s31/library/hash/sha256d.zig",
    "src/frontends/s31/bitcoin/consensus/bitcoin_target.zig",
    "src/frontends/s31/bitcoin/consensus/bitcoin_work.zig",
    "src/frontends/circuit/builder/wrappers.zig",
    "src/frontends/circuit/builder/simd.zig",
    "src/frontends/circuit/builder/context.zig",
    "src/frontends/circuit/air_eval/manual/circuit.zig",
    "src/frontends/circuit/export_qm31_ops.zig",
    "src/frontends/circuit/export_logup_air.zig",
    "src/frontends/circuit/export_logup_batches.zig",
    "src/frontends/circuit/build.zig",
    "src/frontends/circuit/stark_verifier/logup.zig",
    "src/frontends/circuit/stark_verifier/constraint_eval.zig",
    "src/frontends/circuit/common/component_list.zig",
    "src/frontends/circuit/witness/trace.zig",
    "deps/stwo-zig/src/prover/air/logup_columns.zig",
    "src/frontends/circuit/common/direct_arithmetic.zig",
    "src/frontends/circuit/common/preprocessed.zig",
    GATE_WITNESS,
    "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig",
    "deps/stwo-zig/src/prover/prove.zig",
    "deps/stwo-zig/src/core/verifier.zig",
    "src/frontends/circuit/stark_verifier/verify.zig",
    "src/frontends/s31/runtime/native_verifier.zig",
    "src/frontends/s31/sha/proving/sha_direct_circuit_prover.zig",
    "src/frontends/s31/sha/verification/sha_direct_circuit_native_verifier.zig",
    "src/core/fields/m31.zig",
    "src/core/fields/cm31.zig",
    "src/core/fields/qm31.zig",
    "formal/riscv-refinement/RiscvRefinement/Field/M31.lean",
    "formal/riscv-refinement/RiscvRefinement/Recursion/CompactPoseidon.lean",
    "formal/riscv-refinement/lakefile.toml",
    "formal/s31/lakefile.toml",
    "formal/s31/lake-manifest.json",
    "formal/s31/lean-toolchain",
    "src/frontends/s31/python/oracle.py",
    "src/frontends/s31/python/poseidon2_oracle.py",
    "src/frontends/s31/python/s31.py",
    "src/frontends/s31/python/s31_stdlib.py",
    "src/frontends/s31/python/s31_mathlib.py",
    "src/frontends/s31/python/library/__init__.py",
    "src/frontends/s31/python/library/stdlib.py",
    "src/frontends/s31/python/library/math.py",
    "src/frontends/s31/python/library/addition_chains.py",
    "src/frontends/s31/python/text_frontend.py",
    "src/frontends/s31/python/inspection/__init__.py",
    "src/frontends/s31/python/inspection/reports.py",
    "src/frontends/s31/python/cli/__init__.py",
    "src/frontends/s31/python/cli/parser.py",
    "src/frontends/s31/python/cli/commands.py",
    "src/frontends/s31/python/package/__init__.py",
    "src/frontends/s31/python/package/context.py",
    "src/frontends/s31/python/package/build.py",
    "src/frontends/s31/python/package/verify.py",
    "src/frontends/s31/python/runtime/__init__.py",
    "src/frontends/s31/python/runtime/trials.py",
    "src/frontends/s31/python/runtime/folds.py",
    "src/frontends/s31/python/language/syntax.py",
    "src/frontends/s31/python/language/types.py",
    "src/frontends/s31/python/language/parser.py",
    "src/frontends/s31/python/language/builtin_types.py",
    "src/frontends/s31/python/language/elaborate.py",
    "src/frontends/s31/python/language/effects.py",
    "src/frontends/s31/python/language/specialize.py",
    "src/frontends/s31/python/language/builtins.py",
    POSEIDON, SHA, SIGMA,
]


def lean_code(source: str) -> str:
    """Reuse the refinement lexer at the command's cross-package boundary."""
    try:
        result = _strip_lean_comments(source)
    except RefinementError as error:
        raise FormalError(str(error)) from error
    rendered = list(result)
    index = 0
    while index < len(result):
        if result[index] == '"':
            end = _skip_lean_string(result, index)
            for i in range(index, end):
                if rendered[i] != "\n":
                    rendered[i] = " "
            index = end
        else:
            index += 1
    return "".join(rendered)


def array_values(path: str, name: str, count: int) -> list[int]:
    source = (ROOT / path).read_text()
    body = source.split(f"pub const {name}", 1)[1].split("=", 1)[1]
    body = body.split(";", 1)[0]
    body = re.sub(r"//[^\n]*", "", body)
    # A type expression after '=' may contain dimension identifiers, but the
    # source arrays used here contain no numeric dimensions before the body.
    values = [int(n.replace("_", ""), 0 if n.startswith("0x") else 10)
              for n in re.findall(r"\b(?:0x[0-9a-fA-F_]+|[0-9][0-9_]*)\b", body)]
    if len(values) != count:
        raise ValueError(f"{path}:{name}: expected {count}, got {len(values)}")
    return values


def lean_list(values: list[int]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def generated_gate_roster() -> str:
    """Extract arithmetic and Eq Gate lookups from the native witness emitter."""
    source = (ROOT / GATE_WITNESS).read_text()
    eq_block = source.split("pub const eq = struct {", 1)[1].split(
        "// ---------------------------------------------------------------------------", 1)[0]
    if "out.* = value.toM31Array();" not in eq_block:
        raise FormalError(f"{GATE_WITNESS}: Eq base-row limb layout changed")
    eq_calls = re.findall(r"Lookup\.use\([^;\n]+\)", eq_block)
    if len(eq_calls) != 2:
        raise FormalError(f"{GATE_WITNESS}: expected two Eq Gate reads")
    eq_slots = []
    for call in eq_calls:
        match = re.fullmatch(
            r"Lookup\.use\(\.\{\s*gate,\s*pp\.(in0|in1),\s*"
            r"((?:c\[\d+\],?\s*){4})\}\s*\)", call)
        if match is None:
            raise FormalError(f"{GATE_WITNESS}: unrecognized Eq lookup: {call}")
        address, limbs = match.groups()
        indexes = [int(value) for value in re.findall(r"c\[(\d+)\]", limbs)]
        if indexes != [0, 1, 2, 3]:
            raise FormalError(f"{GATE_WITNESS}: Eq lookup limb order changed: {call}")
        eq_slots.append((address, indexes[0]))
    block = source.split("pub const qm31_ops = struct {", 1)[1].split(
        "// ---------------------------------------------------------------------------", 1)[0]
    for start, end, operand in [(0, 4, "in0"), (4, 8, "in1"), (8, 12, "out_value")]:
        assignment = f"out[{start}..{end}].* = {operand}.toM31Array();"
        if assignment not in block:
            raise FormalError(f"{GATE_WITNESS}: qm31_ops limb layout changed: {assignment}")
    calls = re.findall(r"Lookup\.(?:use|yield)\([^;\n]+\)", block)
    if len(calls) != 3:
        raise FormalError(f"{GATE_WITNESS}: expected three qm31_ops Gate lookups")
    slots = []
    for call in calls:
        match = re.fullmatch(
            r"Lookup\.(use|yield)\(\s*(pp\.mults,\s*)?\.\{\s*gate,\s*"
            r"pp\.(in0|in1|out),\s*((?:c\[\d+\],?\s*){4})\}\s*\)", call)
        if match is None:
            raise FormalError(f"{GATE_WITNESS}: unrecognized qm31_ops lookup: {call}")
        kind, multiplier, address, limbs = match.groups()
        if (kind == "yield") != (multiplier is not None):
            raise FormalError(f"{GATE_WITNESS}: qm31_ops lookup weight changed: {call}")
        indexes = [int(value) for value in re.findall(r"c\[(\d+)\]", limbs)]
        if indexes != list(range(indexes[0], indexes[0] + 4)):
            raise FormalError(f"{GATE_WITNESS}: nonconsecutive qm31_ops limbs: {call}")
        slots.append((kind == "yield", "dst" if address == "out" else address, indexes[0]))
    rendered = ",\n  ".join(
        f"⟨{'true' if is_yield else 'false'}, .{address}, {offset}⟩"
        for is_yield, address, offset in slots)
    eq_rendered = ",\n  ".join(
        f"⟨false, .{address}, {offset}⟩" for address, offset in eq_slots)
    return (
        "/-! Generated from circuit/witness/components.zig by scripts/s31_formal.py. -/\n"
        "namespace S31.Gadgets.Air.NativeGateRoster\n\n"
        "inductive AddressSlot where\n  | in0 | in1 | dst\n"
        "deriving DecidableEq, Repr\n\n"
        "structure LookupSlot where\n  isYield : Bool\n"
        "  address : AddressSlot\n  limbStart : Nat\n"
        "deriving DecidableEq, Repr\n\n"
        "def qm31OpsRoster : List LookupSlot := [\n  " + rendered + "\n]\n\n"
        "def eqRoster : List LookupSlot := [\n  " + eq_rendered + "\n]\n\n"
        "end S31.Gadgets.Air.NativeGateRoster\n"
    )


def generated_native_air(step: str, imported: str) -> str:
    """Execute a pinned Zig exporter over production AIR builder code."""
    try:
        result = subprocess.run(
            ["zig", "build", "--build-file", "src/frontends/circuit/build.zig",
             step, "-Doptimize=ReleaseFast"],
            cwd=ENGINE_ROOT, capture_output=True, text=True, timeout=300,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise FormalError(f"native AIR export {step} timed out") from error
    if result.returncode != 0:
        raise FormalError(f"native AIR export {step} failed: " + result.stderr[-4000:])
    if not result.stdout.startswith(f"import S31.Gadgets.Air.{imported}\n"):
        raise FormalError(f"native AIR export {step} returned unexpected output")
    return result.stdout


def check_native_qm31_relation_schedule() -> None:
    """Check the native caller supplies the three terms modeled by the batch proof."""
    source = (ROOT / QM31_EVALUATOR).read_text()
    body = source.split("pub fn evaluateQm31Ops(", 1)[1].split(
        "pub fn evaluateVerifyBitwiseXor12(", 1)[0]
    arithmetic_fold = (
        "inline for (qm31_ops_constraints) |constraint| {\n"
        "        try acc.addConstraint(ctx, try tree.emit(constraint, ctx, &operands));\n"
        "    }"
    )
    first_relation = body.find("try acc.addToRelation(")
    if arithmetic_fold not in body or first_relation < 0 or \
            body.index(arithmetic_fold) >= first_relation:
        raise FormalError(f"{QM31_EVALUATOR}: arithmetic constraints moved after Gate terms")
    if "const relation = try constantM31(ctx, component_list.GATE_RELATION_ID);" not in body:
        raise FormalError(f"{QM31_EVALUATOR}: qm31_ops Gate relation changed")
    if "const neg_mults = try ctx.sub(ctx.zero(), multiplicity);" not in body:
        raise FormalError(f"{QM31_EVALUATOR}: qm31_ops yield sign changed")
    calls = re.findall(
        r"acc\.addToRelation\(ctx,\s*([^,]+),\s*&\.\{\s*relation,\s*"
        r"([^,]+),\s*([^}]+)\}\);", body)
    expected = [
        ("ctx.one()", "op0_addr", ",".join(f"cols[{i}]" for i in range(0, 4))),
        ("ctx.one()", "op1_addr", ",".join(f"cols[{i}]" for i in range(4, 8))),
        ("neg_mults", "dst_addr", ",".join(f"cols[{i}]" for i in range(8, 12))),
    ]
    actual = [(weight.strip(), addr.strip(),
               re.sub(r"\s+", "", limbs))
              for weight, addr, limbs in calls]
    if actual != expected or len(re.findall(r"\baddToRelation(?:WithElements)?\(", body)) != 3:
        raise FormalError(f"{QM31_EVALUATOR}: qm31_ops lookup order/layout changed")
    evaluator = (ROOT / "src/frontends/circuit/stark_verifier/constraint_eval.zig").read_text()
    if ("const shifted = try ctx.mul(self.accumulation, self.composition_polynomial_coeff);\n"
        "            self.accumulation = try ctx.add(shifted, constraint_eval_at_oods);"
            not in evaluator or
        "try statement.evaluateComponent(index, ctx, &data, &acc);\n"
        "        try acc.finalizeLogupInPairs(ctx, data.interaction, &data, claimed_sum);"
            not in evaluator):
        raise FormalError("circuit LogUp/constraint fold order changed")


def check_native_eq_relation_schedule() -> None:
    """Check that the source Eq caller supplies one paired Gate final batch."""
    source = (ROOT / QM31_EVALUATOR).read_text()
    body = source.split("pub fn evaluateEq(", 1)[1].split(
        "// Operand indices of the qm31_ops constraint trees.", 1)[0]
    if "const relation = try constantM31(ctx, component_list.GATE_RELATION_ID);" not in body:
        raise FormalError(f"{QM31_EVALUATOR}: Eq Gate relation changed")
    calls = re.findall(
        r"interp\.acc\.addToRelation\(ctx,\s*([^,]+),\s*&\.\{\s*relation,\s*"
        r"([^,]+),\s*([^}]+)\}\);", body)
    limb_names = ",".join(f"cols[{i}]" for i in range(4))
    actual = [(weight.strip(), addr.strip(), re.sub(r"\s+", "", limbs))
              for weight, addr, limbs in calls]
    if (actual != [("ctx.one()", "in0_address", limb_names),
                   ("ctx.one()", "in1_address", limb_names)] or
            len(re.findall(r"\baddToRelation(?:WithElements)?\(", body)) != 2 or
            "addConstraint" in body):
        raise FormalError(f"{QM31_EVALUATOR}: Eq Gate lookup schedule changed")


def generated_text_square4() -> str:
    """Bind one real functional source file to a kernel-checkable IR program."""
    from src.frontends.s31.python.text_frontend import compile_file

    program, _ = compile_file(ROOT / TEXT_SQUARE4)
    if set(program) != {"version", "name", "inputs", "nodes", "assertions", "public_outputs"}:
        raise FormalError(f"{TEXT_SQUARE4}: unsupported compiler output shape")
    if program["version"] != 1 or not isinstance(program["name"], str):
        raise FormalError(f"{TEXT_SQUARE4}: unsupported version or name")
    if len(program["inputs"]) != 1 or len(program["nodes"]) != 2 or program["assertions"]:
        raise FormalError(f"{TEXT_SQUARE4}: expected a two-node functional sample")
    item = program["inputs"][0]
    if set(item) != {"name", "kind", "length", "visibility"}:
        raise FormalError(f"{TEXT_SQUARE4}: unexpected input fields")
    if item["kind"] not in {"m31", "u16"} or item["visibility"] not in {"public", "private"}:
        raise FormalError(f"{TEXT_SQUARE4}: unsupported input encoding")
    if not isinstance(item["name"], str) or not isinstance(item["length"], int):
        raise FormalError(f"{TEXT_SQUARE4}: invalid input shape")
    if any(set(node) != {"name", "op", "lhs", "rhs"} for node in program["nodes"]):
        raise FormalError(f"{TEXT_SQUARE4}: unsupported node fields")
    if any(not all(isinstance(node[key], str) for key in node)
           for node in program["nodes"]):
        raise FormalError(f"{TEXT_SQUARE4}: invalid node value")
    if not all(isinstance(name, str) for name in program["public_outputs"]):
        raise FormalError(f"{TEXT_SQUARE4}: invalid output name")
    relation = (ROOT / RELATION).read_text()
    op_names = {name.strip() for name in re.search(
        r"pub const Op = enum \{([^}]+)\};", relation).group(1).split(",")}
    if any(node["op"] not in op_names for node in program["nodes"]):
        raise FormalError(f"{TEXT_SQUARE4}: unknown normalized opcode")

    quote = lambda value: json.dumps(value, ensure_ascii=True)
    nodes = ",\n    ".join(
        "{ name := " + quote(node["name"]) + ", op := ." + node["op"] +
        ", lhs := some " + quote(node["lhs"]) +
        ", rhs := some " + quote(node["rhs"]) + " }"
        for node in program["nodes"])
    outputs = ", ".join(quote(name) for name in program["public_outputs"])
    return (
        "import S31.Semantics.Program\n\n"
        "/-! Generated by the S31 text compiler from functional_square4.s31. -/\n"
        "namespace S31.Functional.TextSquare4\n\n"
        "def compiled : S31.Program := {\n"
        f"  version := {program['version']},\n"
        f"  name := {quote(program['name'])},\n"
        "  inputs := [{ name := " + quote(item["name"]) +
        f", shape := ⟨.{item['kind']}, {item['length']}⟩, "
        f"visibility := .«{item['visibility']}» }}],\n"
        f"  nodes := [\n    {nodes}\n  ],\n"
        f"  assertions := [],\n  outputs := [{outputs}]\n"
        "}\n\nend S31.Functional.TextSquare4\n"
    )


def generated_native_square4_topology() -> str:
    """Run the actual direct compiler on IR freshly produced from `.s31` text."""
    from src.frontends.s31.python.text_frontend import compile_file

    program, _ = compile_file(ROOT / TEXT_SQUARE4)
    with tempfile.TemporaryDirectory(prefix="s31-square4-topology-") as directory:
        ir = Path(directory) / "program.json"
        ir.write_text(json.dumps(program, sort_keys=True) + "\n")
        try:
            result = subprocess.run(
                ["zig", "build", "--build-file", "src/frontends/s31/build.zig",
                 "export-square4-topology-lean", "-Doptimize=ReleaseFast",
                 f"-Ds31-source={ir}"],
                cwd=ROOT, capture_output=True, text=True, timeout=300,
                check=False,
            )
        except subprocess.TimeoutExpired as error:
            raise FormalError("native square4 topology export timed out") from error
    if result.returncode != 0:
        raise FormalError("native square4 topology export failed: " + result.stderr[-4000:])
    expected = "import S31.Gadgets.Functional.TextSquare4Air\n"
    if not result.stdout.startswith(expected):
        raise FormalError("native square4 topology exporter returned unexpected output")
    return result.stdout


def generated() -> dict[Path, str]:
    check_native_qm31_relation_schedule()
    check_native_eq_relation_schedule()
    source = (ROOT / RELATION).read_text()
    ops = [op.strip() for op in re.search(
        r"pub const Op = enum \{([^}]+)\};", source).group(1).split(",")]
    op = "/-! Generated by scripts/s31_formal.py from S31 relation IR v1. -/\n"
    op += "namespace S31\n\ninductive Op where\n"
    op += "".join(f"  | {name}\n" for name in ops)
    op += "deriving DecidableEq, Repr, BEq\n\n"
    op += "def Op.wireName : Op → String\n"
    op += "".join(f'  | .{name} => "{name}"\n' for name in ops)
    op += "\ndef Op.ofWireName : String → Option Op\n"
    op += "".join(f'  | "{name}" => some .{name}\n' for name in ops)
    op += "  | _ => none\n\ndef allOps : List Op := [\n"
    op += ",\n".join(f"  .{name}" for name in ops)
    op += "]\n\nend S31\n"

    constants = "/-! Generated by scripts/s31_formal.py; do not edit by hand. -/\n"
    constants += "namespace S31.Constants\n\n"
    for name, path, zig_name, count, row in [
        ("poseidonExternal", POSEIDON, "EXTERNAL_ROUND", 128, 16),
        ("poseidonInternal", POSEIDON, "INTERNAL_ROUND", 14, 0),
        ("poseidonDiagonal", POSEIDON, "INTERNAL_MATRIX", 16, 0),
        ("hashIV", SHA, "initial_state", 8, 0),
        ("shaRound", SHA, "round_constants", 64, 0),
        ("blakeSigma", SIGMA, "BLAKE_SIGMA", 160, 16),
        ("genesisBytes", RELATION, "mainnet_genesis_hash_raw", 32, 0),
    ]:
        values = array_values(path, zig_name, count)
        if row:
            rows = [lean_list(values[i:i + row]) for i in range(0, count, row)]
            constants += f"def {name} : List (List Nat) := [\n  "
            constants += ",\n  ".join(rows) + "]\n\n"
        else:
            constants += f"def {name} : List Nat := {lean_list(values)}\n\n"
    constants += "end S31.Constants\n"

    identity = {"schema": 1, "boundary": "normalized relation IR v1", "ops": ops,
                "sources": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                            for p in BINDINGS}}
    return {
        FORMAL / "S31/Semantics/Op.lean": op,
        FORMAL / "S31/Semantics/Constants.lean": constants,
        FORMAL / "S31/Gadgets/Air/NativeGateRoster.lean": generated_gate_roster(),
        FORMAL / "S31/Gadgets/Air/NativeQm31Air.lean": generated_native_air(
            "export-qm31-air-lean", "Qm31Ops"),
        FORMAL / "S31/Gadgets/Air/NativeLogUpAir.lean": generated_native_air(
            "export-logup-air-lean", "LogUpInteraction"),
        FORMAL / "S31/Gadgets/Air/NativeLogUpBatches.lean": generated_native_air(
            "export-logup-batches-lean", "NativeLogUpAir"),
        FORMAL / "S31/Gadgets/Functional/TextSquare4.lean": generated_text_square4(),
        FORMAL / "S31/Gadgets/Functional/TextSquare4Native.lean":
            generated_native_square4_topology(),
        FORMAL / "S31/Evidence/Coverage.lean": render_coverage(
            json.loads((FORMAL / "coverage.json").read_text())),
        FORMAL / "source-bindings.json": json.dumps(identity, indent=2) + "\n",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate reviewed bindings")
    parser.add_argument("--audit", type=Path, help="validate the live Lean theorem/axiom log")
    parser.add_argument("--parity", type=Path, help="compare the built s31-check to the Python oracle")
    parser.add_argument("--controls", action="store_true", help="compile honest/false/mutated gadget controls")
    parser.add_argument("--lake", default="lake", help="Lake executable used for live controls")
    parser.add_argument("--kernel-log", type=Path, help="validate the successful verbose kernel replay log")
    parser.add_argument("--report", type=Path, help="write complete live CI evidence (requires all live checks)")
    args = parser.parse_args()
    if args.report and (args.write or not all((args.audit, args.parity, args.controls, args.kernel_log))):
        parser.error("--report requires --audit, --kernel-log, --parity and --controls; exclude --write")
    check_protocol_order(ROOT)
    print("S31 protocol order: main and interaction commitments precede their challenge draws")
    failures = []
    for path, expected in generated().items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
        elif not path.exists() or path.read_text() != expected:
            failures.append(str(path.relative_to(ROOT)))
    source_inventory = inventory(ROOT, lean_code)
    inventory_path = FORMAL / "proof-inventory.json"
    expected_inventory = json.dumps(source_inventory, indent=2) + "\n"
    if args.write:
        inventory_path.write_text(expected_inventory)
    elif not inventory_path.is_file() or inventory_path.read_text() != expected_inventory:
        failures.append("formal/s31/proof-inventory.json")
    if failures:
        raise SystemExit("stale S31 formal bindings: " + ", ".join(failures))
    print("S31 formal source bindings: OK")
    ops = json.loads((FORMAL / "source-bindings.json").read_text())["ops"]
    check_coverage(ROOT, ops, json.loads((FORMAL / "coverage.json").read_text()),
                   set(source_inventory["theorems"]))
    print(f"S31 operation/proof inventory: {len(ops)} operations, "
          f"{len(source_inventory['theorems'])} theorems")
    evidence = {"schema": "s31-formal-live-evidence-v1", "operations": len(ops),
                "source_inventory_sha256": hashlib.sha256(expected_inventory.encode()).hexdigest(),
                "production_compiler_correctness_proved": False,
                "stark_soundness_or_zero_knowledge_proved": False}
    if args.audit:
        result = check_audit(args.audit.read_text(), set(source_inventory["theorems"]))
        print(f"S31 axiom audit: {result['theorems']} theorems, approved axioms only")
        evidence["axiom_audit"] = result
    if args.kernel_log:
        result = check_kernel_log(args.kernel_log.read_text(), source_inventory["files"])
        print(f"S31 kernel replay: {result['replayed_modules']} modules")
        evidence["kernel_replay"] = result
    if args.parity:
        from scripts.s31_formal_lib.parity import run
        evidence["semantic_parity"] = run(args.parity.resolve())
        print("S31 independent semantic parity: " + json.dumps(evidence["semantic_parity"], sort_keys=True))
        try:
            schedule = subprocess.run([str(args.parity.resolve()), "--schedule-check"],
                                      capture_output=True, text=True, timeout=120, check=False)
        except subprocess.TimeoutExpired as error:
            raise FormalError("Lean schedule checker timed out") from error
        if schedule.returncode != 0:
            raise FormalError("Lean schedule checker failed: " + schedule.stdout + schedule.stderr)
        evidence["schedule_validity"] = check_schedule_report(schedule.stdout)
        print("S31 hash schedule validity: 57 profiles and 2 malformed controls")
    if args.controls:
        from scripts.s31_formal_lib.controls import run
        evidence["controls"] = run(ROOT, args.lake)
        print("S31 kernel controls: " + json.dumps(evidence["controls"], sort_keys=True))
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(evidence, indent=2) + "\n")


if __name__ == "__main__":
    try:
        main()
    except (FormalError, OSError, ValueError, KeyError) as error:
        raise SystemExit(str(error)) from error
