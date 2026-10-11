#!/usr/bin/env python3
"""Export the pinned STWZEVA/1 Gate arithmetic prefix into checked Lean.

This decoder intentionally supports one bounded native program. Its generated
Lean artifacts prove identities for all eleven roots at arbitrary QM31 cells,
record the exact interaction offset order, and reduce the selected component's
quotient-root Horner fold. Authentication of OODS samples, transcript binding,
and PCS/FRI remain explicit correspondence obligations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
from package.context import AIR_BUNDLE_SHA256  # noqa: E402
from package.correspondence import check_package  # noqa: E402

BUNDLE = ROOT / "deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin"
GATE_PROGRAM_SHA256 = "b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6"
BASE_OPS = ("trace_col", "preprocessed_col", "param", "constant", "add", "sub", "mul", "neg", "inv")
EXT_OPS = ("secure_col", "param", "constant", "add", "sub", "mul", "neg")
READ_ORDER = (0, 2, 3, 1, 4, 5, 6, 7)


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def integer(data: bytes, offset: int, fmt: str) -> tuple[int, ...]:
    size = struct.calcsize(fmt)
    require(0 <= offset <= len(data) - size, "truncated STWZEVA/1 record")
    return struct.unpack_from(fmt, data, offset)


def gate_program(bundle: bytes) -> bytes:
    require(hashlib.sha256(bundle).hexdigest() == AIR_BUNDLE_SHA256,
            "installed AIR bundle digest changed")
    require(bundle[:8] == b"STWZEVA\0" and integer(bundle, 8, "<I") == (1,),
            "unsupported installed AIR bundle")
    count = integer(bundle, 28, "<I")[0]
    require(count == 11, "installed component count changed")
    cursor = 40
    selected = None
    for component_index in range(count):
        (label_len, reserved, _instance, _trace_log, _eval_log, constraints,
         _random_offset, n_spans, n_preprocessed, n_denominators, n_ext,
         n_parts) = integer(bundle, cursor, "<HH10I")
        require(reserved == 0 and 0 < label_len <= 256 and n_parts == 1,
                "unsupported component framing")
        cursor += 44
        require(cursor + label_len <= len(bundle), "truncated component label")
        label = bundle[cursor:cursor + label_len]
        cursor += label_len
        cursor += 12 * n_spans + 4 * n_preprocessed + 4 * n_denominators
        if component_index == 1:
            require(n_ext == 7, "Gate extension source count changed")
            sources = [integer(bundle, cursor + 32 * i, "<IIII4I")
                       for i in range(n_ext)]
            require(sources == [(2, i, 0, 0, 0, 0, 0, 0) for i in range(1, 6)] +
                    [(1, 0, 0, 0, 0, 0, 0, 0), (3, 0, 0, 0, 0, 0, 0, 0)],
                    "Gate challenge/claim source order changed")
        cursor += 32 * n_ext
        require(cursor + 16 <= len(bundle), "truncated selected part")
        rc_base, size, semantic = integer(bundle, cursor, "<IIQ")
        cursor += 16
        require(cursor + size <= len(bundle), "truncated evaluation program")
        program = bundle[cursor:cursor + size]
        cursor += size
        if component_index == 1:
            require(label == b"qm31_ops" and constraints == 11 and rc_base == 0 and
                    semantic == 0x3FA1236478F103EF,
                    "selected Gate component identity changed")
            selected = program
    require(cursor == len(bundle) and selected is not None, "bundle framing changed")
    require(hashlib.sha256(selected).hexdigest() == GATE_PROGRAM_SHA256,
            "selected Gate bytecode digest changed")
    return selected


def decoded_program(data: bytes) -> tuple[list[tuple[int, int, int, int, int, int]],
                                          list[tuple[int, int, int, int, int, int, int]],
                                          tuple[int, ...]]:
    (magic, major, minor, n_sections, flags, semantic_hash, caps,
     interactions, base_params, ext_params, roots_count, max_base, max_ext,
     secure_degree, domain_log) = integer(data, 0, "<IHHIIQQ8I")
    require((magic, major, minor, n_sections, flags, interactions, base_params,
             ext_params, roots_count, max_base, max_ext, secure_degree, domain_log) ==
            (0x31505453, 1, 0, 5, 1, 3, 0, 7, 11, 134, 97, 4, 23),
            "selected Gate evaluator header changed")
    require(semantic_hash == 0x3FA1236478F103EF and caps & 4 != 0,
            "selected Gate semantic identity changed")
    require(data[64:96] == bytes(32), "nonzero reserved evaluator header")
    sections = [integer(data, 96 + 24 * i, "<IIQQ") for i in range(n_sections)]
    require([row[0] for row in sections] == [1, 2, 3, 4, 5] and
            [row[1] for row in sections] == [4, 16, 16, 20, 4] and
            [row[3] for row in sections] == [0, 0, 134, 97, 11],
            "selected Gate section table changed")
    payload = 96 + 24 * n_sections
    chunks = []
    for _kind, width, offset, count in sections:
        require(offset + width * count <= len(data) - payload,
                "selected Gate section out of bounds")
        chunks.append(data[payload + offset:payload + offset + width * count])
    require([row[2] for row in sections] == [0, 0, 0, 2144, 4084],
            "selected Gate payload offsets changed")
    require(payload + max(s[2] + s[1] * s[3] for s in sections) == len(data),
            "selected Gate program has trailing bytes")
    computed_semantic = 0xCBF29CE484222325
    for byte in b"".join(chunks):
        computed_semantic ^= byte
        computed_semantic = (computed_semantic * 0x100000001B3) & ((1 << 64) - 1)
    require(computed_semantic == semantic_hash, "Gate bytecode semantic hash changed")
    base = [integer(chunks[2], 16 * i, "<BBHIIi") for i in range(134)]
    ext = [integer(chunks[3], 20 * i, "<BBHIIII") for i in range(97)]
    roots = integer(chunks[4], 0, "<11I")
    require(roots == (*range(9), 88, 96), "selected Gate root order changed")
    require(all(op < len(BASE_OPS) and dst < 134 for op, _, dst, _, _, _ in base),
            "unsupported base opcode/register")
    require(all(op < len(EXT_OPS) and reserved == 0 and dst < 97
                for op, reserved, dst, *_ in ext), "unsupported extension opcode/register")
    for index, (op, tree, dst, a, b, imm) in enumerate(base):
        require(dst == index, "base register order changed")
        if op == 0:
            require(tree in (0, 1, 2) and a < (8, 12, 8)[tree] and imm in (0, -1),
                    "unsupported Gate trace read")
        elif op == 3:
            require(a < (1 << 31) - 1, "noncanonical Gate constant")
        elif op in (4, 5, 6):
            require(a < index and b < index, "Gate base read before write")
        else:
            require(False, "unsupported Gate base arithmetic opcode")
    for index, (op, _, dst, a, b, c, d) in enumerate(ext):
        require(dst == index, "extension register order changed")
        if op == 0:
            require(max(a, b, c, d) < 134, "Gate extension base read out of bounds")
        elif op == 1:
            require(a < 7, "Gate extension parameter out of bounds")
        elif op == 2:
            require(max(a, b, c, d) < (1 << 31) - 1,
                    "noncanonical Gate extension constant")
        elif op in (3, 4, 5):
            require(a < index and b < index, "Gate extension read before write")
        elif op == 6:
            require(a < index, "Gate extension read before write")
    for root, expected in zip(roots[:9], (24, 28, 31, 34, 37, 61, 85, 103, 121), strict=True):
        require(ext[root] == (0, 0, root, expected, 25, 25, 25),
                "arithmetic root is no longer an injected base residual")
    require(base[25] == (3, 0, 25, 0, 0, 0), "arithmetic extension padding is not zero")
    return base, ext, roots


def evaluate_row(
    decoded: tuple[list[tuple[int, int, int, int, int, int]],
                   list[tuple[int, int, int, int, int, int, int]], tuple[int, ...]],
    fixed: tuple[int, ...], main: tuple[int, ...], current: tuple[int, ...],
    previous: tuple[int, ...], alpha: tuple[int, int, int, int],
    z: tuple[int, int, int, int], claimed: tuple[int, int, int, int],
    row_count: int,
) -> tuple[tuple[int, int, int, int], ...]:
    """Independent scalar replay of native opcodes at one base-field row.

    The native verifier evaluates the same program over QM31 OODS samples;
    this scalar replay tests bytecode roots and source-row indices only. It
    makes no assertion about polynomial openings or previous-row mask proof.
    """
    from export_s31_direct_gate_evaluator_fixture import add, base, mul, sub

    base_insts, ext_insts, roots = decoded
    p = (1 << 31) - 1
    require(all(len(group) == expected for group, expected in
                ((fixed, 8), (main, 12), (current, 8), (previous, 8))),
            "invalid Gate row width")
    require(0 < row_count < p, "invalid Gate row count")
    registers = [0] * 134
    for op, tree, dst, a, b, imm in base_insts:
        if op == 0:
            registers[dst] = (fixed, main, previous if imm == -1 else current)[tree][a]
        elif op == 3:
            registers[dst] = a
        elif op == 4:
            registers[dst] = (registers[a] + registers[b]) % p
        elif op == 5:
            registers[dst] = (registers[a] - registers[b]) % p
        elif op == 6:
            registers[dst] = registers[a] * registers[b] % p
        else:
            raise ValueError("unexpected Gate base opcode")
    powers = []
    power = base(1)
    for _ in range(5):
        power = mul(power, alpha)
        powers.append(power)
    params = (*powers, z, tuple(value * pow(row_count, -1, p) % p
                                  for value in claimed))
    extension = [base(0)] * 97
    for op, _reserved, dst, a, b, c, d in ext_insts:
        if op == 0:
            extension[dst] = (registers[a], registers[b], registers[c], registers[d])
        elif op == 1:
            extension[dst] = params[a]
        elif op == 2:
            extension[dst] = (a, b, c, d)
        elif op == 3:
            extension[dst] = add(extension[a], extension[b])
        elif op == 4:
            extension[dst] = sub(extension[a], extension[b])
        elif op == 5:
            extension[dst] = mul(extension[a], extension[b])
        elif op == 6:
            extension[dst] = sub(base(0), extension[a])
        else:
            raise ValueError("unexpected Gate extension opcode")
    return tuple(extension[root] for root in roots)


def render(package: Path) -> str:
    checked = check_package(package)
    require(checked["air_profile"]["component_manifest_sha256"] and
            checked["source_sha256"], "missing checked package identity")
    bundle = BUNDLE.read_bytes()
    base, _ext, _roots = decoded_program(gate_program(bundle))
    lines = [
        "-- Generated from the exact checked STWZEVA/1 qm31_ops program.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Native rebind changes domain log size (23 to 9), not these instructions.",
        "import S31.Gadgets.Air.DirectGatePolynomial", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic", "",
        "open S31.Gadgets.Packed", "",
        "open S31.Gadgets.Air.DirectGateEvaluatorCells", "",
        "open S31.Gadgets.Air.DirectGatePolynomial", "",
        "set_option linter.unusedVariables false", "",
        "/-- The first nine installed roots are secure-column injections of",
        "base registers 24, 28, 31, 34, 37, 61, 85, 103, 121.",
        "Registers 25 in their other coordinates are the bytecode constant zero. -/",
        "def bytecodeArithmeticOver {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) : List K := Id.run do",
    ]
    for op, tree, dst, a, b, imm in base[:122]:
        if op == 0:
            require(imm == 0 and tree in (0, 1), "arithmetic prefix reads a shifted/interaction cell")
            expression = f"cells.{('localFixed', 'main')[tree]} {a}"
        elif op == 3:
            expression = str(a)
        else:
            expression = f"r{a} { {4: '+', 5: '-', 6: '*'}[op] } r{b}"
        lines.append(f"  let r{dst} : K := {expression}")
    lines += ["  return [r24, r28, r31, r34, r37, r61, r85, r103, r121]", "",
              "/-- Ring-polynomial identity for arbitrary sampled base-column",
              "values. This includes native QM31 OODS samples. -/",
              "theorem bytecode_arithmetic_over_eq {K : Type*} [CommRing K]",
              "    (cells : ArithmeticCells K) :",
              "    bytecodeArithmeticOver cells = modeledArithmetic cells := by",
              "  simp [bytecodeArithmeticOver, modeledArithmetic]", "",
              "def bytecodeArithmetic (cells : Cells) : List F :=",
              "  bytecodeArithmeticOver (fromM31Cells cells)", "",
              "/-- The generic identity specializes to the earlier M31 model. -/",
              "theorem bytecode_arithmetic_eq (cells : Cells) :",
              "    bytecodeArithmetic cells = arithmetic cells := by",
              "  simpa [bytecodeArithmetic, bytecode_arithmetic_over_eq] using",
              "    modeled_m31_eq_pure cells", "",
              "/-- Zero arithmetic roots of the selected program enforce the",
              "decoded Gate operation and output for arbitrary local cells. -/",
              "theorem bytecode_zero_decodes (cells : Cells)",
              "    (hzero : ∀ residual ∈ bytecodeArithmetic cells, residual = 0) :",
              "    ∃ op, (decodedRow cells).flags = S31.Gadgets.Air.Qm31Ops.encode op ∧",
              "      (decodedRow cells).output = S31.Gadgets.Air.Qm31Ops.evaluate op",
              "        (decodedRow cells).in0 (decodedRow cells).in1 := by",
              "  apply arithmetic_zero_decodes cells",
              "  simpa [bytecode_arithmetic_eq] using hzero", "",
              "end S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic", ""]
    return "\n".join(lines)


def active_zig_source(source: str) -> str:
    """Mask comments and quoted strings while preserving braces and offsets."""
    result = list(source)
    i = 0
    while i < len(source):
        if source.startswith("//", i):
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            result[i:end] = " " * (end - i)
            i = end
        elif source.startswith("/*", i):
            begin, depth = i, 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/*", i):
                    depth += 1
                    i += 2
                elif source.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            require(depth == 0, "unterminated Zig comment")
            result[begin:i] = ["\n" if ch == "\n" else " " for ch in source[begin:i]]
        elif source[i] in ('"', "'"):
            quote, begin = source[i], i
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == quote:
                    i += 1
                    break
                else:
                    i += 1
            require(i <= len(source) and source[i - 1] == quote,
                    "unterminated Zig quoted literal")
            result[begin:i] = ["\n" if ch == "\n" else " " for ch in source[begin:i]]
        else:
            i += 1
    return "".join(result)


def braced_body(source: str, opening: int) -> tuple[str, int]:
    """Return the active body and closing brace at a known opening brace."""
    require(source[opening] == "{", "expected Zig scope opening brace")
    depth = 1
    for i in range(opening + 1, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return source[opening + 1:i], i
    raise ValueError("unterminated Zig scope")


def check_base_vm_source_contract(verifier: str) -> None:
    """Pin the unique active base-instruction loop and its whole switch."""
    source = active_zig_source(verifier)
    functions = list(re.finditer(r"\bfn\s+evaluateProgram\s*\(", source))
    require(len(functions) == 1, "native Gate base opcode source contract changed")
    function_open = source.find("{", functions[0].end())
    require(function_open >= 0, "native Gate base opcode source contract changed")
    function, _ = braced_body(source, function_open)
    loops = list(re.finditer(
        r"\bfor\s*\(\s*program\.base_insts\s*\)\s*\|\s*instruction\s*\|\s*\{",
        function))
    require(len(loops) == 1, "native Gate base opcode source contract changed")
    loop, _ = braced_body(function, loops[0].end() - 1)
    expected = """base[instruction.dst] = switch (instruction.op) {
                .trace_col, .preprocessed_col => try self.traceValue(
                    mask,
                    base_offsets,
                    interaction_offsets,
                    instruction.interaction,
                    instruction.a,
                    instruction.imm,
                ),
                .param => return Error.InvalidProgram,
                .constant => QM31.fromBase(M31.fromCanonical(instruction.a)),
                .add => base[instruction.a].add(base[instruction.b]),
                .sub => base[instruction.a].sub(base[instruction.b]),
                .mul => base[instruction.a].mul(base[instruction.b]),
                .neg => base[instruction.a].neg(),
                .inv => try base[instruction.a].inv(),
            };
            if (std.process.hasEnvVarConstant("STWO_ZIG_SN2_LOG_VERIFIER_LOGUP_INPUTS") and
                self.captured.random_coefficient_offset == 0 and instruction.op == .trace_col and
                instruction.interaction == 2)
            {
                std.debug.print(
                    "verifier_logup_base dst={} column={} offset={} value={any}\\n",
                    .{ instruction.dst, instruction.a, instruction.imm, qm31Words(base[instruction.dst]) },
                );
            }"""
    require(re.sub(r"\s+", "", loop) ==
            re.sub(r"\s+", "", active_zig_source(expected)),
            "native Gate base opcode source contract changed")


def render_base_vm(package: Path) -> str:
    """Reflect the selected Gate's arithmetic base opcodes into a Lean VM.

    The first 38 cover flags; the first 122 cover all arithmetic roots. Their
    bytes are checked by the pinned bundle/program digest as other exports.
    """
    checked = check_package(package)
    base, _extension, _roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig").read_text()
    check_base_vm_source_contract(verifier)
    constructors = {4: "add", 5: "sub", 6: "mul"}
    instructions = []
    for op, tree, dst, a, b, imm in base[:122]:
        if op == 0:
            require(imm == 0 and tree in (0, 1), "arithmetic prefix has unsupported trace read")
            operation = f".{'fixed' if tree == 0 else 'main'} {a}"
        elif op == 3:
            operation = f".constant {a}"
        else:
            require(op in constructors, "arithmetic prefix has unsupported opcode")
            operation = f".{constructors[op]} {a} {b}"
        instructions.append(f"  ⟨{dst}, {operation}⟩")
    lines = [
        "-- Generated from the checked first 122 STWZEVA/1 Gate base instructions.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Native opcode switch wording is checked by the exporter; Zig execution is external.",
        "import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateBaseVm", "",
        "open S31.Gadgets.Air.DirectGatePolynomial", "",
        "set_option maxRecDepth 2048",
        "set_option maxHeartbeats 3000000", "",
        "inductive BaseOp where",
        "  | fixed (column : Fin 8)",
        "  | main (column : Fin 12)",
        "  | constant (value : Nat)",
        "  | add (left right : Nat)",
        "  | sub (left right : Nat)",
        "  | mul (left right : Nat)", "",
        "structure Instruction where",
        "  dst : Nat",
        "  op : BaseOp", "",
        "def execute {K : Type*} [CommRing K] (cells : ArithmeticCells K)",
        "    (registers : Nat → K) (instruction : Instruction) : Nat → K :=",
        "  let value := match instruction.op with",
        "    | .fixed column => cells.localFixed column",
        "    | .main column => cells.main column",
        "    | .constant n => (n : K)",
        "    | .add left right => registers left + registers right",
        "    | .sub left right => registers left - registers right",
        "    | .mul left right => registers left * registers right",
        "  fun index => if index == instruction.dst then value else registers index", "",
        "def executeAll {K : Type*} [CommRing K] (cells : ArithmeticCells K)",
        "    (instructions : List Instruction) : Nat → K :=",
        "  instructions.foldl (execute cells) (fun _ => 0)", "",
        "/-- Exactly the installed base instruction prefix through register 37. -/",
        "def flagPrefix : List Instruction := [",
        ",\n".join(instructions[:38]),
        "]", "",
        "/-- Remaining arithmetic instructions, before interaction reads. -/",
        "def arithmeticTail : List Instruction := [",
        ",\n".join(instructions[38:]),
        "]", "",
        "def arithmeticProgram : List Instruction := flagPrefix ++ arithmeticTail", "",
        "def flagRoots {K : Type*} [CommRing K] (cells : ArithmeticCells K) : List K :=",
        "  let registers := executeAll cells flagPrefix",
        "  [registers 24, registers 28, registers 31, registers 34, registers 37]", "",
        "/-- The reflected opcode interpreter agrees with the first five",
        "generated Gate arithmetic roots for every commutative ring, including",
        "QM31 samples. This does not prove native Zig executes the opcode switch. -/",
        "theorem flagRoots_eq_generated {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) :",
        "    flagRoots cells =",
        "      (GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver cells).take 5 := by",
        "  simp [flagRoots, executeAll, flagPrefix, execute,",
        "    GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver]", "",
        "/-- These interpreted roots are the first five Gate AIR polynomials. -/",
        "theorem flagRoots_eq_modeled {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) :",
        "    flagRoots cells = (modeledArithmetic cells).take 5 := by",
        "  rw [flagRoots_eq_generated,",
        "    GeneratedDirectGateBytecodeArithmetic.bytecode_arithmetic_over_eq]", "",
        "def arithmeticRoots {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) : List K :=",
        "  let registers := executeAll cells arithmeticProgram",
        "  [registers 24, registers 28, registers 31, registers 34, registers 37,",
        "   registers 61, registers 85, registers 103, registers 121]", "",
        "/-- The reflected 122-opcode base interpreter gives all nine",
        "selected arithmetic roots for arbitrary ring-valued cells. -/",
        "theorem arithmeticRoots_eq_generated {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) :",
        "    arithmeticRoots cells =",
        "      GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver cells := by",
        "  simp [arithmeticRoots, arithmeticProgram, arithmeticTail, flagPrefix,",
        "    executeAll, execute,",
        "    GeneratedDirectGateBytecodeArithmetic.bytecodeArithmeticOver]", "",
        "theorem arithmeticRoots_eq_modeled {K : Type*} [CommRing K]",
        "    (cells : ArithmeticCells K) :",
        "    arithmeticRoots cells = modeledArithmetic cells := by",
        "  rw [arithmeticRoots_eq_generated,",
        "    GeneratedDirectGateBytecodeArithmetic.bytecode_arithmetic_over_eq]", "",
        "end S31.Gadgets.Air.GeneratedDirectGateBaseVm", "",
    ]
    return "\n".join(lines)


def check_ext_vm_source_contract(verifier: str) -> None:
    """Pin the unique active extension loop, including writes after switch."""
    source = active_zig_source(verifier)
    functions = list(re.finditer(r"\bfn\s+evaluateProgram\s*\(", source))
    require(len(functions) == 1, "native Gate extension opcode source contract changed")
    function, _ = braced_body(source, source.find("{", functions[0].end()))
    loops = list(re.finditer(
        r"\bfor\s*\(\s*program\.ext_insts\s*\)\s*\|\s*instruction\s*\|\s*\{",
        function))
    require(len(loops) == 1, "native Gate extension opcode source contract changed")
    loop, _ = braced_body(function, loops[0].end() - 1)
    expected = """extension[instruction.dst] = switch (instruction.op) {
                .secure_col => QM31.fromPartialEvals(.{
                    base[instruction.a],
                    base[instruction.b],
                    base[instruction.c],
                    base[instruction.d],
                }),
                .param => ext_params[instruction.a],
                .constant => QM31.fromU32Unchecked(
                    instruction.a,
                    instruction.b,
                    instruction.c,
                    instruction.d,
                ),
                .add => extension[instruction.a].add(extension[instruction.b]),
                .sub => extension[instruction.a].sub(extension[instruction.b]),
                .mul => extension[instruction.a].mul(extension[instruction.b]),
                .neg => extension[instruction.a].neg(),
            };
            if (std.process.hasEnvVarConstant("STWO_ZIG_SN2_LOG_VERIFIER_LOGUP_INPUTS") and
                self.captured.random_coefficient_offset == 0 and
                (instruction.op == .secure_col or instruction.op == .param))
            {
                std.debug.print(
                    "verifier_logup_ext op={s} dst={} slot={} value={any}\\n",
                    .{ @tagName(instruction.op), instruction.dst, instruction.a, qm31Words(extension[instruction.dst]) },
                );
            }"""
    require(re.sub(r"\s+", "", loop) ==
            re.sub(r"\s+", "", active_zig_source(expected)),
            "native Gate extension opcode source contract changed")


def render_ext_vm(package: Path) -> str:
    """Reflect selected extension opcodes 9–96 into Lean QM31 interpreter."""
    checked = check_package(package)
    base, extension, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    require(roots[-2:] == (88, 96), "selected Gate LogUp roots changed")
    verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig").read_text()
    check_ext_vm_source_contract(verifier)
    used_base = sorted({slot for op, _, _, a, b, c, d in extension[9:]
                        if op == 0 for slot in (a, b, c, d)})
    require(used_base == [*range(4, 20), 25, *range(122, 134)],
            "selected extension base dependencies changed")
    base_reads = []
    for index in used_base:
        op, tree, _dst, a, _b, imm = base[index]
        if op == 3:
            require(index == 25 and a == 0, "selected extension zero register changed")
            expression = "0"
        else:
            require(op == 0, "selected extension base register is not a read")
            if tree == 0:
                require(imm == 0, "shifted fixed read in extension")
                expression = f"cells.localFixed {a}"
            elif tree == 1:
                require(imm == 0, "shifted main read in extension")
                expression = f"cells.main {a}"
            else:
                require(tree == 2 and imm in (0, -1), "unsupported interaction read")
                expression = (f"cells.previousInteraction {a}" if imm == -1
                              else f"cells.interaction {a}")
        base_reads.append(f"  | {index} => {expression}")
    op_names = {3: "add", 4: "sub", 5: "mul"}
    instructions = []
    for op, _reserved, dst, a, b, c, d in extension[9:]:
        if op == 0:
            operation = f".secure {a} {b} {c} {d}"
        elif op == 1:
            operation = f".param {a}"
        elif op == 2:
            require(b == c == d == 0, "selected extension constant is nonbase")
            operation = f".constant {a}"
        elif op in op_names:
            operation = f".{op_names[op]} {a} {b}"
        else:
            require(op == 6, "unsupported selected extension opcode")
            operation = f".neg {a}"
        instructions.append(f"  ⟨{dst}, {operation}⟩")
    lines = [
        "-- Generated from checked STWZEVA/1 Gate extension instructions 9–96.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Native extension loop is source checked; Zig execution remains external.",
        "import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateExtVm", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic", "",
        "open S31.Gadgets.Air.DirectGateOodsLogUp", "",
        "set_option maxRecDepth 2048",
        "set_option maxHeartbeats 3000000", "",
        "inductive ExtOp where",
        "  | secure (a b c d : Nat)",
        "  | param (slot : Nat)",
        "  | constant (value : Nat)",
        "  | add (left right : Nat)",
        "  | sub (left right : Nat)",
        "  | mul (left right : Nat)",
        "  | neg (source : Nat)", "",
        "structure Instruction where",
        "  dst : Nat",
        "  op : ExtOp", "",
        "def baseRead (cells : Cells) : Nat → QM",
        *base_reads,
        "  | _ => 0", "",
        "def paramRead (alpha z claimedScaled : QM) : Nat → QM",
        "  | 0 => alpha ^ 1",
        "  | 1 => alpha ^ 2",
        "  | 2 => alpha ^ 3",
        "  | 3 => alpha ^ 4",
        "  | 4 => alpha ^ 5",
        "  | 5 => z",
        "  | 6 => claimedScaled",
        "  | _ => 0", "",
        "def execute (cells : Cells) (alpha z claimedScaled : QM)",
        "    (registers : Nat → QM) (instruction : Instruction) : Nat → QM :=",
        "  let value := match instruction.op with",
        "    | .secure a b c d => fromPartialEvals",
        "        (baseRead cells a) (baseRead cells b)",
        "        (baseRead cells c) (baseRead cells d)",
        "    | .param slot => paramRead alpha z claimedScaled slot",
        "    | .constant n => (n : QM)",
        "    | .add left right => registers left + registers right",
        "    | .sub left right => registers left - registers right",
        "    | .mul left right => registers left * registers right",
        "    | .neg source => -registers source",
        "  fun index => if index == instruction.dst then value else registers index", "",
        "def extensionProgram : List Instruction := [",
        ",\n".join(instructions),
        "]", "",
        "def logupRoots (cells : Cells) (alpha z claimedScaled : QM) : QM × QM :=",
        "  let registers := extensionProgram.foldl",
        "    (execute cells alpha z claimedScaled) (fun _ => 0)",
        "  (registers 88, registers 96)", "",
        "/-- The interpreted selected extension suffix yields exactly the two",
        "source-bound LogUp roots at arbitrary QM31 OODS cells. -/",
        "theorem logupRoots_eq_generated (cells : Cells)",
        "    (alpha z claimedScaled : QM) :",
        "    logupRoots cells alpha z claimedScaled =",
        "      GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled := by",
        "  simp [logupRoots, extensionProgram, execute, baseRead, paramRead,",
        "    GeneratedDirectGateBytecodeLogUp.bytecodeLogup]", "",
        "end S31.Gadgets.Air.GeneratedDirectGateExtVm", "",
    ]
    return "\n".join(lines)


def render_logup(package: Path) -> str:
    """Emit the selected two QM31 LogUp roots from the same pinned program."""
    checked = check_package(package)
    require(checked["air_profile"]["component_manifest_sha256"] and
            checked["source_sha256"], "missing checked package identity")
    base, extension, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    require(roots[-2:] == (88, 96), "selected LogUp root order changed")
    used_base = sorted({slot for op, _, _, a, b, c, d in extension[9:]
                        if op == 0 for slot in (a, b, c, d)})
    require(used_base == [*range(4, 20), 25, *range(122, 134)],
            "selected LogUp base register dependencies changed")
    for index in range(122, 126):
        require(base[index] == (0, 2, index, index - 122, 0, 0),
                "selected current interaction read changed")
    for index in range(126, 134):
        expected_column = 4 + (index - 126) // 2
        expected_offset = -1 if index % 2 == 0 else 0
        require(base[index] == (0, 2, index, expected_column, 0, expected_offset),
                "selected previous/current interaction read changed")
    offset_order: list[list[int]] = [[] for _ in range(8)]
    for op, tree, _dst, column, _b, offset in base:
        if op == 0 and tree == 2 and offset not in offset_order[column]:
            offset_order[column].append(offset)
    require(offset_order == [[0]] * 4 + [[-1, 0]] * 4,
            "selected interaction offset order changed")
    lines = [
        "-- Generated from checked STWZEVA/1 qm31_ops LogUp roots 9–10.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Sample authentication and OODS shift provenance remain separate.",
        "import S31.Gadgets.Air.DirectGateOodsLogUp", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsLogUp", "",
        "set_option linter.unusedVariables false", "",
        "/-- Unique offsets in bytecode instruction order, as used by native",
        "`resident_geometry.componentOffsets` and `traceValue`. -/",
        "def interactionOffsets (column : Fin 8) : List Int :=",
        "  match column.val with",
    ]
    for column, offsets in enumerate(offset_order):
        lines.append(f"  | {column} => [{', '.join(map(str, offsets))}]")
    lines += ["  | _ => []", "",
              "/-- Native `offsetIndex` returns the first matching sample slot. -/",
              "def offsetIndex : List Int → Int → Option Nat",
              "  | [], _ => none",
              "  | first :: rest, wanted =>",
              "      if first == wanted then some 0 else (offsetIndex rest wanted).map (· + 1)", "",
              "def interactionMaskRead (samples : Fin 8 → List QM)",
              "    (column : Fin 8) (offset : Int) : Option QM :=",
              "  (offsetIndex (interactionOffsets column) offset).bind fun index =>",
              "    (samples column)[index]?", "",
              "/-- For columns 4–7, native `at_prev` is sample slot zero and",
              "`at_oods` is sample slot one; columns 0–3 have only `at_oods`. -/",
              "theorem mask_slots (column : Fin 8) :",
              "    (if column.val < 4 then",
              "      interactionOffsets column = [0] ∧",
              "        offsetIndex (interactionOffsets column) 0 = some 0 ∧",
              "        offsetIndex (interactionOffsets column) (-1) = none",
              "    else",
              "      interactionOffsets column = [-1, 0] ∧",
              "        offsetIndex (interactionOffsets column) (-1) = some 0 ∧",
              "        offsetIndex (interactionOffsets column) 0 = some 1) := by",
              "  fin_cases column <;> decide", "",
              "/-- The selected previous/current roots use precisely these two",
              "sample positions for each last-column limb. -/",
              "theorem last_mask_reads (samples : Fin 8 → List QM)",
              "    (column : Fin 8) (h : 4 ≤ column.val) :",
              "    interactionMaskRead samples column (-1) = (samples column)[0]? ∧",
              "      interactionMaskRead samples column 0 = (samples column)[1]? := by",
              "  fin_cases column <;> simp_all [interactionMaskRead, interactionOffsets, offsetIndex]", "",
        "/-- Native base registers execute in QM31 at an OODS point. The",
        "seven extension parameters are `[α, α², α³, α⁴, α⁵, z, claimedScaled]`. -/",
        "def bytecodeLogup (cells : Cells) (alpha z claimedScaled : QM) :",
        "    QM × QM := Id.run do",
    ]
    for index in used_base:
        op, tree, dst, a, _b, imm = base[index]
        require(dst == index, "selected LogUp base register order changed")
        if op == 0:
            if tree == 0:
                require(imm == 0, "shifted fixed-column read")
                expression = f"cells.localFixed {a}"
            elif tree == 1:
                require(imm == 0, "shifted main-column read")
                expression = f"cells.main {a}"
            else:
                expression = (f"cells.previousInteraction {a}" if imm == -1
                              else f"cells.interaction {a}")
        else:
            require(index == 25 and op == 3 and a == 0,
                    "selected LogUp zero register changed")
            expression = "0"
        lines.append(f"  let r{index} : QM := {expression}")
    for op, _reserved, dst, a, b, c, d in extension[9:]:
        if op == 0:
            expression = f"fromPartialEvals r{a} r{b} r{c} r{d}"
        elif op == 1:
            expression = f"alpha ^ {a + 1}" if a < 5 else ("z" if a == 5 else "claimedScaled")
        elif op == 2:
            require(b == c == d == 0, "unsupported nonbase selected constant")
            expression = str(a)
        elif op in (3, 4, 5):
            expression = f"e{a} { {3: '+', 4: '-', 5: '*'}[op] } e{b}"
        elif op == 6:
            expression = f"-e{a}"
        else:
            raise ValueError("unsupported selected LogUp opcode")
        lines.append(f"  let e{dst} : QM := {expression}")
    lines += ["  return (e88, e96)", "",
              "/-- Polynomial equality of the installed LogUp root pair over",
              "arbitrary QM31 fixed, main, and interaction samples. -/",
              "theorem bytecode_logup_eq (cells : Cells) (alpha z claimedScaled : QM) :",
              "    bytecodeLogup cells alpha z claimedScaled =",
              "      (pair cells alpha z, last cells alpha z claimedScaled) := by",
              "  dsimp [bytecodeLogup, pair, last, inputZeroDenominator,",
              "    inputOneDenominator, outputDenominator, denominator,",
              "    firstColumn, lastColumn, previousLastColumn]",
              "  simp only [fromPartialEvals_three_zero, pow_succ, Prod.mk.injEq]",
              "  constructor <;> ring", "",
              "end S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp", ""]
    return "\n".join(lines)


def check_composition_source_contract(verifier: str, accumulator: str,
                                      component_fold: str) -> None:
    """Fail closed on changes to the pinned native quotient-fold statements."""
    require("const denominator_inverse = try zeroifier.inv();" in verifier and
            "for (program.constraint_roots, 0..) |root, root_index|" in verifier and
            "const evaluation = extension[root].mul(denominator_inverse);" in verifier and
            "accumulator.accumulate(evaluation);" in verifier and
            ".accumulation = QM31.zero()," in accumulator and
            "self.accumulation = self.accumulation.mul(self.random_coeff).add(evaluation);" in accumulator and
            "PointEvaluationAccumulator.init(random_coeff)" in component_fold and
            "for (self.components, 0..) |component, ordinal|" in component_fold,
            "native Gate quotient accumulation source changed")


def render_composition(package: Path) -> str:
    """Emit the selected Gate quotient-root and Horner composition link."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    components = manifest["components"]
    require(len(components) == 1 and
            components[0]["name"] == "qm31_ops" and
            components[0]["source_index"] == 1 and
            components[0]["proof_index"] == 0 and
            components[0]["trace_log_size"] == 9 and
            components[0]["n_constraints"] == 11 and
            components[0]["random_coefficient_offset"] == 0 and
            roots == (*range(9), 88, 96),
            "selected direct Gate composition shape changed")
    verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig").read_text()
    accumulator = (ROOT / "deps/stwo-zig/src/core/air/accumulation.zig").read_text()
    component_fold = (ROOT / "deps/stwo-zig/src/core/air/components.zig").read_text()
    check_composition_source_contract(verifier, accumulator, component_fold)
    lines = [
        "-- Generated from the checked one-component STWZEVA/1 direct Gate package.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Root order: extension registers 0..8 (base injections), then 88 and 96.",
        "-- Native quotient/accumulator statements are checked source contracts.",
        "import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp",
        "import S31.Gadgets.Air.DirectGateOodsComposition", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateComposition", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsLogUp",
        "open S31.Gadgets.Air.DirectGateOodsComposition", "",
        "/-- The installed root order of the selected direct Gate component. -/",
        "def bytecodeRoots (cells : Cells) (alpha z claimedScaled : QM) : List QM :=",
        "  installedArithmeticRoots (arithmeticCells cells) ++",
        "    [(GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled).1,",
        "     (GeneratedDirectGateBytecodeLogUp.bytecodeLogup cells alpha z claimedScaled).2]", "",
        "theorem bytecode_roots_eq_pure (cells : Cells) (alpha z claimedScaled : QM) :",
        "    bytecodeRoots cells alpha z claimedScaled =",
        "      pureRoots cells alpha z claimedScaled := by",
        "  simp [bytecodeRoots, pureRoots,",
        "    installed_arithmetic_roots_eq_oods_polynomials,",
        "    GeneratedDirectGateBytecodeLogUp.bytecode_logup_eq]", "",
        "/-- Native `zeroifier.inv()` succeeds only when the zeroifier is",
        "nonzero. The selected component's eleven ordered quotient evaluations",
        "then contribute this exact Horner fold. -/",
        "theorem bytecode_composition_eq_pure (cells : Cells)",
        "    (alpha z claimedScaled coefficient zeroifier : QM)",
        "    (_hzero : zeroifier ≠ 0) :",
        "    quotientFold coefficient zeroifier⁻¹",
        "      (bytecodeRoots cells alpha z claimedScaled) =",
        "      S31.Gadgets.Air.CompositionFold.fold coefficient",
        "        (pureRoots cells alpha z claimedScaled) / zeroifier := by",
        "  rw [bytecode_roots_eq_pure, quotient_fold_factor]",
        "  rfl", "",
        "end S31.Gadgets.Air.GeneratedDirectGateComposition", "",
    ]
    return "\n".join(lines)


def check_transcript_parameter_source_contract(native: str, lookup: str,
                                               resident: str) -> None:
    """Check the selected direct verifier's local draw/claim/parameter path."""
    require(native.count("fn verifyDirectProfile(") == 1,
            "selected direct verifier entry changed")
    selected = native.split("fn verifyDirectProfile(", 1)[1]
    markers = [
        "const sum_count: usize = if (private_boundary != null) 3 else if (has_chip) 2 else 1;",
        "sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);",
        "try scheme.commit(allocator, roots[1], main_logs, &channel);",
        "const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);",
        "const circuit_sum = try circuit.witness.direct_arithmetic.lookupSum(&outputs, sums[0], lookup.z, lookup.alpha);",
        "else if (!circuit_sum.isZero()) return error.InvalidLookupSum;",
        "core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..sum_count]);",
        "try scheme.commit(allocator, roots[2], interaction_logs, &channel);",
        "captured[0] = .init(allocator, &bound.components[0], &pp_logs, lifting_bound, lookup.z, lookup.alpha, sums[0]);",
    ]
    positions = [selected.find(marker) for marker in markers]
    require(all(position >= 0 for position in positions) and positions == sorted(positions)
            and all(selected.count(marker) == 1 for marker in markers),
            "selected direct Gate transcript/claim order changed")
    require("return .{ .z = values[0], .alpha = values[1] };" in lookup and
            "channel.mixFelts(claimed_sums);" in lookup,
            "lookup challenge/claim transcript mapping changed")
    require("const claimed_scale = try M31.fromCanonical(" in resident and
            "@as(u32, 1) << @intCast(self.captured.trace_log_size)," in resident and
            ".lookup_z => self.lookup_z," in resident and
            ".lookup_alpha_power => |power| self.lookup_alpha.pow(power)," in resident and
            ".claimed_sum_scaled => self.claimed_sum.mulM31(claimed_scale)," in resident,
            "resident Gate extension parameter mapping changed")


def render_transcript_params(package: Path) -> str:
    """Emit the selected Gate lookup draw and scaled-claim parameter link."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    component = manifest["components"]
    require(len(component) == 1 and component[0]["source_index"] == 1 and
            component[0]["trace_log_size"] == 9 and
            component[0]["random_coefficient_offset"] == 0 and
            roots == (*range(9), 88, 96),
            "selected Gate transcript parameter profile changed")
    engine = ROOT / "deps/stwo-zig/src"
    check_transcript_parameter_source_contract(
        (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (engine / "core/channel/lookup_transcript.zig").read_text(),
        (engine / "frontends/cairo/witness/resident_verifier.zig").read_text(),
    )
    return "\n".join([
        "-- Generated from the checked selected direct Gate package and native source contracts.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        "-- Extension source order: alpha^1..alpha^5, z, claimed_sum / 512.",
        "-- `z` is draw 0 and `alpha` is draw 1 after main commitment.",
        "import S31.Gadgets.Air.DirectGateTranscriptParams",
        "import S31.Gadgets.Air.GeneratedDirectGateComposition", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsLogUp",
        "open S31.Gadgets.Air.DirectGateOodsComposition",
        "open S31.Gadgets.Air.DirectGateTranscriptParams", "",
        "/-- Supply the installed bytecode using the exact selected verifier",
        "lookup pair `(z, alpha)` and first claimed sum. -/",
        "def transcriptRoots (cells : Cells) (z alpha claimed : QM) : List QM :=",
        "  GeneratedDirectGateComposition.bytecodeRoots cells alpha z",
        "    (extensionParam z alpha claimed 6)", "",
        "theorem transcript_roots_eq_pure (cells : Cells) (z alpha claimed : QM) :",
        "    transcriptRoots cells z alpha claimed =",
        "      pureRoots cells alpha z (claimed / 512) := by",
        "  simp [transcriptRoots, extensionParam, claimed_scaled_eq_div,",
        "    GeneratedDirectGateComposition.bytecode_roots_eq_pure]", "",
        "theorem transcript_composition_eq_pure (cells : Cells)",
        "    (z alpha claimed coefficient zeroifier : QM)",
        "    (_hzero : zeroifier ≠ 0) :",
        "    quotientFold coefficient zeroifier⁻¹",
        "      (transcriptRoots cells z alpha claimed) =",
        "      S31.Gadgets.Air.CompositionFold.fold coefficient",
        "        (pureRoots cells alpha z (claimed / 512)) / zeroifier := by",
        "  rw [transcript_roots_eq_pure, quotient_fold_factor]",
        "  rfl", "",
        "end S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
    ])


def check_oods_opening_source_contract(core: str, resident: str) -> None:
    """Bind the accepted OODS claim to the very samples read by Gate bytecode.

    This checks pass-through and indexing. It does not prove that the PCS
    verifier authenticates those samples or that FRI establishes low degree.
    """
    markers = [
        "const composition_oods_eval = proof.extractCompositionOodsEvalWithSplit(",
        "if (!composition_oods_eval.eql(try components.evalCompositionPolynomialAtPoint(",
        "&proof.commitment_scheme_proof.sampled_values,",
        "return VerificationError.OodsNotMatching;",
        "const pcs_proof = proof.commitment_scheme_proof;",
        "try commitment_scheme.verifyValuesWithProofCapture(",
        "try commitment_scheme.verifyValuesWithBorrowedProofCapture(",
        "try commitment_scheme.verifyValuesWithQueryCapture(",
        "try commitment_scheme.verifyValues(",
    ]
    positions = [core.find(marker) for marker in markers]
    require(all(position >= 0 for position in positions) and positions == sorted(positions)
            and all(core.count(marker) == 1 for marker in markers),
            "native OODS claim/sample pass-through changed")
    require("verifyValuesWithProofCapture(allocator, sample_points, pcs_proof, channel, challenges, capture)" in core and
            "verifyValuesWithBorrowedProofCapture(allocator, sample_points, &pcs_proof, channel, challenges, capture)" in core and
            core.count("            pcs_proof,\n            channel,") == 2,
            "native PCS proof forwarding changed")
    reads = [
        "const global = component.preprocessed_indices[local_column];",
        "if (global >= mask.items[0].len or mask.items[0][global].len != 1)",
        "break :blk mask.items[0][global][0];",
        "const sample_index = offsetIndex(offsets[local_column].items, offset) orelse",
        "const global = span.start + local_column;",
        "break :blk mask.items[interaction][global][sample_index];",
    ]
    read_positions = [resident.find(marker) for marker in reads]
    require(all(position >= 0 for position in read_positions) and
            read_positions == sorted(read_positions) and
            all(resident.count(marker) == 1 for marker in reads),
            "resident Gate OODS sample read changed")
    require(".trace_col, .preprocessed_col => try self.traceValue(" in resident and
            "instruction.interaction," in resident and
            "instruction.a," in resident and "instruction.imm," in resident,
            "resident Gate bytecode trace dispatch changed")


def render_oods_openings(package: Path) -> str:
    """Emit the sampled-value-tree to selected Gate claim reduction."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    entries = manifest["components"]
    require(len(entries) == 1 and entries[0]["source_index"] == 1 and
            entries[0]["preprocessed_indices"] == list(READ_ORDER) and
            roots == (*range(9), 88, 96),
            "selected Gate opening geometry changed")
    core = (ROOT / "deps/stwo-zig/src/core/verifier.zig").read_text()
    resident = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig").read_text()
    check_oods_opening_source_contract(core, resident)
    return "\n".join([
        "-- Generated from the checked selected direct Gate package and native OODS source contracts.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        f"-- Core verifier SHA-256: {hashlib.sha256(core.encode()).hexdigest()}",
        f"-- Resident verifier SHA-256: {hashlib.sha256(resident.encode()).hexdigest()}",
        "-- PCS sample authentication and FRI remain separate assumptions.",
        "import S31.Gadgets.Air.DirectGateOodsOpenings",
        "import S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateOodsOpenings", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsOpenings",
        "open S31.Gadgets.Air.DirectGateOodsComposition",
        "open S31.Gadgets.Air.DirectGateOodsLogUp", "",
        "open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
        "/-- Accepted claim equation at the resident Gate component. `accepted`",
        "is the core verifier's OODS equality check, with the exact sampled",
        "values later passed to PCS verification. `Shape` makes every read",
        "defined; authentication of the values is an external premise. -/",
        "theorem accepted_claim_eq_pure (samples : Samples)",
        "    (_shape : DirectGateOodsOpenings.Shape samples)",
        "    (z alpha claimed coefficient zeroifier compositionClaim : QM)",
        "    (_hzero : zeroifier ≠ 0)",
        "    (accepted : compositionClaim =",
        "      quotientFold coefficient zeroifier⁻¹",
        "        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots",
        "          (cellsOfSamples samples) z alpha claimed)) :",
        "    compositionClaim = S31.Gadgets.Air.CompositionFold.fold coefficient",
        "      (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier := by",
        "  rw [accepted]",
        "  exact transcript_composition_eq_pure (cellsOfSamples samples)",
        "      z alpha claimed coefficient zeroifier _hzero", "",
        "end S31.Gadgets.Air.GeneratedDirectGateOodsOpenings", "",
    ])


def check_composition_opening_source_contract(core: str, proof: str,
                                              types: str, resident: str,
                                              components: str, field: str) -> None:
    """Check selected split-one composition extraction and OODS comparison.

    This contract checks reviewed Zig statements; it is not a verified Zig
    interpreter, PCS-opening theorem, or proof of circle arithmetic.
    """
    require("pub const COMPOSITION_LOG_SPLIT: u32 = 1;" in types and
            "return verifier_types.COMPOSITION_LOG_SPLIT;" in components,
            "default composition split changed")
    require("pub const SECURE_EXTENSION_DEGREE: usize = 4;" in field and
            "out = out.add(evals[1].mul(QM31.fromU32Unchecked(0, 1, 0, 0)));" in field and
            "out = out.add(evals[2].mul(QM31.fromU32Unchecked(0, 0, 1, 0)));" in field and
            "out = out.add(evals[3].mul(QM31.fromU32Unchecked(0, 0, 0, 1)));" in field,
            "native composition coordinate basis changed")
    vtable = resident.split("pub fn asComponent(", 1)[-1].split("fn cast(", 1)[0]
    require(".evaluateConstraintQuotientsAtPoint = evaluateConstraintQuotientsAtPoint," in vtable
            and ".compositionLogSplit" not in vtable,
            "selected resident component split override changed")
    extraction = proof.split("pub fn extractCompositionOodsEvalWithSplit(", 1)[-1].split(
        "pub fn sizeEstimate(", 1)[0]
    markers = [
        "self.commitment_scheme_proof.sampled_values.items.len - 1",
        "const expected_cols = verifier_types.compositionColumnCount(",
        "if (masks.len != expected_cols) return null;",
        "chunk_index * qm31.SECURE_EXTENSION_DEGREE + coordinate_index",
        "if (column.len != 1) return null;",
        "coordinate.* = column[0];",
        "chunk_eval.* = QM31.fromPartialEvals(coordinates);",
        "return reconstructCompositionChunkEvals(",
    ]
    positions = [extraction.find(marker) for marker in markers]
    require(all(position >= 0 for position in positions) and positions == sorted(positions)
            and all(extraction.count(marker) == 1 for marker in markers),
            "composition sampled-value extraction changed")
    reconstruction = proof.split("pub fn reconstructCompositionChunkEvals(", 1)[-1].split(
        "pub fn ExtendedStarkProof(", 1)[0]
    require("var parent_log = composition_log_size - split_depth + 1;" in reconstruction and
            "const factor = point.repeatedDouble(parent_log - 2).x;" in reconstruction and
            "chunk_evals[out_index] = chunk_evals[input_index].add(" in reconstruction and
            "factor.mul(chunk_evals[input_index + 1])," in reconstruction and
            "active /= 2;" in reconstruction,
            "composition chunk reconstruction changed")
    require("try appendCompositionMaskTree(" in core and
            "const composition_oods_eval = proof.extractCompositionOodsEvalWithSplit(" in core
            and "composition_log_split," in core and
            "if (!composition_oods_eval.eql(try components.evalCompositionPolynomialAtPoint(" in core,
            "composition opening/OODS comparison changed")


def render_composition_opening(package: Path) -> str:
    """Emit the selected proof's last-tree composition opening reduction."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    entry = manifest["components"]
    require(len(entry) == 1 and entry[0]["source_index"] == 1 and
            entry[0]["evaluation_log_size"] == 10 and
            entry[0]["random_coefficient_offset"] == 0 and
            roots == (*range(9), 88, 96),
            "selected Gate composition opening profile changed")
    engine = ROOT / "deps/stwo-zig/src"
    core = (engine / "core/verifier.zig").read_text()
    proof = (engine / "core/proof.zig").read_text()
    types = (engine / "core/verifier_types.zig").read_text()
    resident = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
    components = (engine / "core/air/components.zig").read_text()
    field = (engine / "core/fields/qm31.zig").read_text()
    check_composition_opening_source_contract(core, proof, types, resident, components, field)
    return "\n".join([
        "-- Generated from the selected Gate package and split-one native composition extraction.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        f"-- Core verifier SHA-256: {hashlib.sha256(core.encode()).hexdigest()}",
        f"-- Proof extraction SHA-256: {hashlib.sha256(proof.encode()).hexdigest()}",
        f"-- Verifier types SHA-256: {hashlib.sha256(types.encode()).hexdigest()}",
        f"-- QM31 field SHA-256: {hashlib.sha256(field.encode()).hexdigest()}",
        "-- `factor` is native `oods_point.repeatedDouble(composition_log_size - 2).x`.",
        "-- PCS authentication, circle-point implementation and FRI are premises.",
        "import S31.Gadgets.Air.DirectGateCompositionOpening",
        "import S31.Gadgets.Air.GeneratedDirectGateOodsOpenings", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateCompositionOpening", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsOpenings",
        "open S31.Gadgets.Air.DirectGateOodsLogUp",
        "open S31.Gadgets.Air.DirectGateOodsComposition",
        "open S31.Gadgets.Air.DirectGateCompositionOpening", "",
        "open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
        "/-- The native `extractCompositionOodsEvalWithSplit` reads exactly the",
        "last eight singleton columns when split is one. `accepted` is the",
        "subsequent core-verifier comparison to Gate quotient evaluation. -/",
        "theorem accepted_tree_eq_pure (samples : Samples)",
        "    (_shape : DirectGateOodsOpenings.Shape samples)",
        "    (compositionTree : List (List QM))",
        "    (factor z alpha claimed coefficient zeroifier : QM)",
        "    (hzero : zeroifier ≠ 0)",
        "    (accepted : extractSplitOne factor compositionTree =",
        "      some (quotientFold coefficient zeroifier⁻¹",
        "        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots",
        "          (cellsOfSamples samples) z alpha claimed))) :",
        "    extractSplitOne factor compositionTree =",
        "      some (S31.Gadgets.Air.CompositionFold.fold coefficient",
        "        (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier) := by",
        "  rw [← transcript_composition_eq_pure (cellsOfSamples samples)",
        "    z alpha claimed coefficient zeroifier hzero]",
        "  exact accepted", "",
        "end S31.Gadgets.Air.GeneratedDirectGateCompositionOpening", "",
    ])


def check_circle_factor_source_contract(core: str, circle: str, proof: str,
                                        types: str) -> None:
    """Bind the selected OODS point and split-factor path to reviewed Zig."""
    require("const oods_seed = channel.drawSecureFelt();" in core and
            "const oods_point = try pointFromOodsSeed(oods_seed);" in core and
            "return circle.secureFieldPointFromRandomSeedChecked(seed) catch" in core and
            "return VerificationError.InvalidOodsSeed;" in core and
            "InvalidOodsSeed," in types and
            "const composition_oods_eval = proof.extractCompositionOodsEvalWithSplit(" in core,
            "native checked OODS seed/point path changed")
    point = circle.split("pub fn secureFieldPointFromRandomSeedChecked(", 1)[-1].split(
        "pub fn randomSecureFieldPoint(", 1)[0]
    require("const t_square = t.square();" in point and
            "const one_plus_t_square_inv = try t_square.add(QM31.one()).inv();" in point and
            "const x = QM31.one().sub(t_square).mul(one_plus_t_square_inv);" in point and
            "const y = t.add(t).mul(one_plus_t_square_inv);" in point and
            "return .{ .x = x, .y = y };" in point and
            "return secureFieldPointFromRandomSeedChecked(t) catch unreachable;" in circle,
            "native OODS seed-to-circle map changed")
    algebra = circle.split("pub fn CirclePoint(comptime F: type) type {", 1)[-1].split(
        "pub const CirclePointM31", 1)[0]
    require("const x = lhs.x.mul(rhs.x).sub(lhs.y.mul(rhs.y));" in algebra and
            "const y = lhs.x.mul(rhs.y).add(lhs.y.mul(rhs.x));" in algebra and
            "return self.add(self);" in algebra and
            "out = out.double();" in algebra and
            "while (i < n) : (i += 1)" in algebra,
            "native circle repeated-double arithmetic changed")
    require("const factor = point.repeatedDouble(parent_log - 2).x;" in proof and
            "var parent_log = composition_log_size - split_depth + 1;" in proof and
            "if (composition_log_size <= split_depth or chunk_evals_in.len != chunk_count)" in proof,
            "native composition factor selection changed")


def render_circle_factor(package: Path) -> str:
    """Emit a seed-indexed Gate composition factor theorem."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    entry = manifest["components"]
    require(len(entry) == 1 and entry[0]["source_index"] == 1 and
            entry[0]["evaluation_log_size"] == 10 and
            roots == (*range(9), 88, 96),
            "selected Gate circle-factor profile changed")
    engine = ROOT / "deps/stwo-zig/src/core"
    core = (engine / "verifier.zig").read_text()
    circle = (engine / "circle.zig").read_text()
    proof = (engine / "proof.zig").read_text()
    types = (engine / "verifier_types.zig").read_text()
    check_circle_factor_source_contract(core, circle, proof, types)
    return "\n".join([
        "-- Generated from the selected Gate package and native OODS circle source contract.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
        f"-- Core verifier SHA-256: {hashlib.sha256(core.encode()).hexdigest()}",
        f"-- Circle SHA-256: {hashlib.sha256(circle.encode()).hexdigest()}",
        f"-- Proof extraction SHA-256: {hashlib.sha256(proof.encode()).hexdigest()}",
        f"-- Verifier errors SHA-256: {hashlib.sha256(types.encode()).hexdigest()}",
        "-- Successful checked seed conversion replaces the denominator premise.",
        "-- Native Zig refinement and PCS/FRI remain premises.",
        "import S31.Gadgets.Air.DirectGateCircleFactor",
        "import S31.Gadgets.Air.GeneratedDirectGateCompositionOpening", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateCircleFactor", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsOpenings",
        "open S31.Gadgets.Air.DirectGateOodsLogUp",
        "open S31.Gadgets.Air.DirectGateOodsComposition",
        "open S31.Gadgets.Air.DirectGateCircleFactor",
        "open S31.Gadgets.Air.DirectGateCompositionOpening",
        "open S31.Gadgets.Air.GeneratedDirectGateCompositionOpening", "",
        "/-- Reduce a native-shaped OODS check whose factor is the x-coordinate",
        "after `compositionLogSize - 2` doublings of the seed-derived point.",
        "The native channel draw and PCS opening authentication are premises. -/",
        "theorem accepted_seeded_tree_eq_pure (samples : Samples)",
        "    (shape : DirectGateOodsOpenings.Shape samples)",
        "    (compositionTree : List (List QM))",
        "    (seed z alpha claimed coefficient zeroifier : QM)",
        "    (compositionLogSize : Nat)",
        "    (_hsize : 2 ≤ compositionLogSize)",
        "    (seedAccepted : checkedFromSeed seed = some (fromSeed seed))",
        "    (hzero : zeroifier ≠ 0)",
        "    (accepted : extractSplitOne",
        "      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x",
        "      compositionTree = some (quotientFold coefficient zeroifier⁻¹",
        "        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots",
        "          (cellsOfSamples samples) z alpha claimed))) :",
        "    extractSplitOne (factor seed compositionLogSize) compositionTree =",
        "      some (S31.Gadgets.Air.CompositionFold.fold coefficient",
        "        (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier) := by",
        "  have hden := checked_seed_success_nonzero seed (fromSeed seed) seedAccepted",
        "  rw [factor_eq_repeated_double seed hden compositionLogSize]",
        "  exact accepted_tree_eq_pure samples shape compositionTree",
        "    _ z alpha claimed coefficient zeroifier hzero accepted", "",
        "end S31.Gadgets.Air.GeneratedDirectGateCircleFactor", "",
    ])


def check_pcs_opening_source_contract(core: str, pcs: str,
                                      fri_answers: str, samples: str,
                                      resident: str, geometry: str,
                                      circle: str, canonic: str,
                                      components: str) -> None:
    """Check the native dataflow that passes one proof's OODS values to PCS.

    This is a reviewed source contract, not a cryptographic or Zig refinement
    proof. The Lean PCS opening property remains an explicit assumption.
    """
    verifier = core.split("fn verifyImpl(", 1)[-1].split(
        "fn pointFromOodsSeed(", 1)[0]
    markers = [
        "const composition_oods_eval = proof.extractCompositionOodsEvalWithSplit(",
        "&proof.commitment_scheme_proof.sampled_values,",
        "return VerificationError.OodsNotMatching;",
        "const pcs_proof = proof.commitment_scheme_proof;",
        "try commitment_scheme.verifyValues(",
    ]
    positions = [verifier.find(marker) for marker in markers]
    require(all(position >= 0 for position in positions) and
            positions == sorted(positions) and
            all(verifier.count(marker) == 1 for marker in markers),
            "core OODS-to-PCS proof sample identity changed")
    require("sample_points,\n            pcs_proof,\n            channel," in verifier and
            "try appendCompositionMaskTree(" in verifier and
            "verifyValuesWithProofCapture(allocator, sample_points, pcs_proof, channel, challenges, capture)" in verifier and
            "verifyValuesWithBorrowedProofCapture(allocator, sample_points, &pcs_proof, channel, challenges, capture)" in verifier and
            "try commitment_scheme.verifyValuesWithQueryCapture(" in verifier,
            "core PCS sample points or proof handoff changed")
    pcs_impl = pcs.split("fn verifyValuesImpl(", 1)[-1].split(
        "fn maxOrDefault(", 1)[0]
    pcs_markers = [
        "flattenSampledValues(allocator, proof.sampled_values)",
        "channel.mixFelts(sampled_values_flat);",
        "tree.verify(",
        "const fri_answers = try quotients.friAnswers(",
        "proof.sampled_values,",
        "fri_verifier.decommit(allocator, fri_answers)",
    ]
    pcs_positions = [pcs_impl.find(marker) for marker in pcs_markers]
    require(all(position >= 0 for position in pcs_positions) and
            pcs_positions == sorted(pcs_positions),
            "PCS transcript/Merkle/FRI sampled-value dataflow changed")
    flatten = pcs.split("fn flattenSampledValues(", 1)[-1].split(
        "fn duplicateColumnLogSizes(", 1)[0]
    require("for (sampled_values.items) |tree|" in flatten and
            "for (tree) |column|" in flatten and
            "@memcpy(out[at .. at + column.len], column);" in flatten,
            "PCS tree/column/sample flatten order changed")
    require("pub fn friAnswers(" in fri_answers and
            "buildColumnSampleBatchesFromParallelInputs(" in fri_answers and
            "sampled_values," in fri_answers,
            "PCS quotient answer sampled-value input changed")
    require("for (sampled_points.items, sampled_values.items, 0..)" in samples and
            "for (points_per_col, values_per_col) |point, value|" in samples and
            "if (points_per_col.len != values_per_col.len) return error.ShapeMismatch;" in samples,
            "PCS point/value column pairing changed")
    require("const oods_point = try pointFromOodsSeed(oods_seed);" in verifier and
            "var sample_points = try components.maskPoints(\n        allocator,\n        oods_point,\n        max_log_degree_bound," in verifier,
            "OODS seed or selected maximum bound mask input changed")
    mask = resident.split("    fn maskPoints(", 1)[-1].split(
        "    fn preprocessedColumnIndices(", 1)[0]
    require("canonic.CanonicCoset.new(max_log_degree_bound).step()" in mask and
            "QM31.fromBase(trace_step_m31.x)" in mask and
            "QM31.fromBase(trace_step_m31.y)" in mask and
            "pointsFromOffsets(allocator, base_offsets, point, trace_step)" in mask and
            "pointsFromOffsets(allocator, interaction_offsets, point, trace_step)" in mask,
            "resident Gate canonical trace step or mask points changed")
    require("sample_point.* = point.add(step.mulSigned(offset));" in geometry and
            "pub fn mulSigned(self: Self, off: isize) Self" in circle and
            "return self.conjugate().mul(@intCast(-off));" in circle and
            "pub inline fn conjugate(self: Self) Self" in circle and
            "return .{ .x = self.x, .y = self.y.neg() };" in circle and
            "const x = lhs.x.mul(rhs.x).sub(lhs.y.mul(rhs.y));" in circle and
            "const y = lhs.x.mul(rhs.y).add(lhs.y.mul(rhs.x));" in circle,
            "native circle offset/group law changed")
    require("return .{ .coset_value = Coset.odds(log_size) };" in canonic and
            "return self.coset_value.step;" in canonic and
            "CirclePointIndex.subgroupGen(log_size)" in circle and
            "M31_CIRCLE_LOG_ORDER - log_size" in circle and
            ".x = M31.fromCanonical(2)" in circle and
            ".y = M31.fromCanonical(1_268_011_823)" in circle,
            "canonical circle step derivation changed")
    require("col.*[0] = point;" in components and
            "new_preprocessed[idx] = replacement;" in components and
            "col.*[0] = oods_point;" in core,
            "fixed or composition OODS mask point changed")


def render_pcs_opening_link(package: Path) -> str:
    """Emit the selected Gate's conditional committed-opening theorem."""
    checked = check_package(package)
    _base, _ext, roots = decoded_program(gate_program(BUNDLE.read_bytes()))
    manifest = json.loads((package / "component-manifest.json").read_text())
    entries = manifest["components"]
    require(len(entries) == 1 and entries[0]["source_index"] == 1 and
            entries[0]["preprocessed_indices"] == list(READ_ORDER) and
            roots == (*range(9), 88, 96),
            "selected Gate PCS opening geometry changed")
    engine = ROOT / "deps/stwo-zig/src/core"
    paths = [engine / "verifier.zig", engine / "pcs/verifier.zig",
             engine / "pcs/quotients/fri_answers.zig",
             engine / "pcs/quotients/samples.zig",
             ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_verifier.zig",
             ROOT / "deps/stwo-zig/src/frontends/cairo/witness/resident_geometry.zig",
             engine / "circle.zig", engine / "poly/circle/canonic.zig",
             engine / "air/components.zig"]
    sources = [path.read_text() for path in paths]
    check_pcs_opening_source_contract(*sources)
    lines = [
        "-- Generated from the selected Gate package and reviewed OODS-to-PCS source dataflow.",
        f"-- Bundle SHA-256: {AIR_BUNDLE_SHA256}",
        f"-- Gate program SHA-256: {GATE_PROGRAM_SHA256}",
        f"-- Source SHA-256: {checked['source_sha256']}",
    ]
    lines += [f"-- {label} SHA-256: {hashlib.sha256(source.encode()).hexdigest()}"
              for label, source in zip(("Core verifier", "PCS verifier", "FRI answers",
                                        "PCS samples", "Resident Gate verifier",
                                        "Resident Gate geometry", "Circle group",
                                        "Canonical coset", "Component masks"),
                                       sources, strict=True)]
    lines += [
        "-- This theorem is conditional on PCS opening authentication; it does not prove it.",
        "import S31.Gadgets.Air.DirectGatePcsOpeningLink", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGatePcsOpeningLink", "",
        "open S31.Gadgets.Air.DirectGateOodsArithmetic",
        "open S31.Gadgets.Air.DirectGateOodsOpenings",
        "open S31.Gadgets.Air.DirectGateOodsLogUp",
        "open S31.Gadgets.Air.DirectGateOodsComposition",
        "open S31.Gadgets.Air.DirectGateCircleFactor",
        "open S31.Gadgets.Air.DirectGatePcsOpeningLink",
        "open S31.Gadgets.Air.DirectGateCompositionOpening",
        "open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams", "",
        "/-- The native verifier's shared proof-sample dataflow permits this",
        "reduction only under an authenticated PCS-opening assumption. -/",
        "theorem selected_gate_accepted_of_authenticated (samples : Samples)",
        "    (compositionTree : List (List QM)) (roots : TreeRoots)",
        "    (polys : PolynomialInventory)",
        "    (commitmentBinds : TreeRoots → PolynomialInventory → Prop)",
        "    (maxLogDegreeBound : Nat)",
        "    (seed z alpha claimed coefficient zeroifier : QM)",
        "    (compositionLogSize : Nat) (hsize : 2 ≤ compositionLogSize)",
        "    (hbound : 1 ≤ maxLogDegreeBound ∧ maxLogDegreeBound ≤ 31)",
        "    (auth : PcsOpeningAssumption samples compositionTree roots polys",
        "      commitmentBinds seed maxLogDegreeBound)",
        "    (seedAccepted : checkedFromSeed seed = some (fromSeed seed))",
        "    (hzero : zeroifier ≠ 0)",
        "    (accepted : extractSplitOne",
        "      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x",
        "      compositionTree = some (quotientFold coefficient zeroifier⁻¹",
        "        (transcriptRoots (cellsOfSamples samples) z alpha claimed))) :",
        "    extractSplitOne (factor seed compositionLogSize)",
        "      (expectedCompositionTree polys seed) =",
        "      some (S31.Gadgets.Air.CompositionFold.fold coefficient",
        "        (pureRoots (expectedCells polys seed maxLogDegreeBound)",
        "          alpha z (claimed / 512)) /",
        "        zeroifier) := by",
        "  exact accepted_of_authenticated_openings samples compositionTree roots",
        "    polys commitmentBinds maxLogDegreeBound seed z alpha claimed coefficient",
        "    zeroifier compositionLogSize hsize hbound auth seedAccepted hzero accepted", "",
        "end S31.Gadgets.Air.GeneratedDirectGatePcsOpeningLink", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--logup-output", type=Path,
                        help="also regenerate the selected two-root QM31 LogUp theorem")
    parser.add_argument("--composition-output", type=Path,
                        help="also regenerate the selected direct Gate composition theorem")
    parser.add_argument("--transcript-output", type=Path,
                        help="also regenerate the selected Gate transcript parameter theorem")
    parser.add_argument("--oods-openings-output", type=Path,
                        help="also regenerate the selected Gate OODS sampled-value theorem")
    parser.add_argument("--composition-opening-output", type=Path,
                        help="also regenerate the split-one composition-tree theorem")
    parser.add_argument("--circle-factor-output", type=Path,
                        help="also regenerate the selected OODS circle-factor theorem")
    parser.add_argument("--pcs-opening-output", type=Path,
                        help="also regenerate the conditional PCS opening link")
    parser.add_argument("--base-vm-output", type=Path,
                        help="also regenerate the selected Gate base opcode interpreter")
    parser.add_argument("--ext-vm-output", type=Path,
                        help="also regenerate the selected Gate extension opcode interpreter")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = render(args.package)
    logup = render_logup(args.package) if args.logup_output is not None else None
    composition = (render_composition(args.package)
                   if args.composition_output is not None else None)
    transcript = (render_transcript_params(args.package)
                  if args.transcript_output is not None else None)
    openings = (render_oods_openings(args.package)
                if args.oods_openings_output is not None else None)
    composition_opening = (render_composition_opening(args.package)
                           if args.composition_opening_output is not None else None)
    circle_factor = (render_circle_factor(args.package)
                     if args.circle_factor_output is not None else None)
    pcs_opening = (render_pcs_opening_link(args.package)
                   if args.pcs_opening_output is not None else None)
    base_vm = render_base_vm(args.package) if args.base_vm_output is not None else None
    ext_vm = render_ext_vm(args.package) if args.ext_vm_output is not None else None
    if args.check:
        if not args.output.is_file() or args.output.read_text() != result:
            raise SystemExit("installed Gate bytecode Lean export changed")
        if logup is not None and (not args.logup_output.is_file() or
                                  args.logup_output.read_text() != logup):
            raise SystemExit("installed Gate LogUp bytecode Lean export changed")
        if composition is not None and (not args.composition_output.is_file() or
                                        args.composition_output.read_text() != composition):
            raise SystemExit("installed Gate composition Lean export changed")
        if transcript is not None and (not args.transcript_output.is_file() or
                                       args.transcript_output.read_text() != transcript):
            raise SystemExit("installed Gate transcript Lean export changed")
        if openings is not None and (not args.oods_openings_output.is_file() or
                                     args.oods_openings_output.read_text() != openings):
            raise SystemExit("installed Gate OODS openings Lean export changed")
        if composition_opening is not None and (
            not args.composition_opening_output.is_file() or
            args.composition_opening_output.read_text() != composition_opening
        ):
            raise SystemExit("installed Gate composition opening Lean export changed")
        if circle_factor is not None and (
            not args.circle_factor_output.is_file() or
            args.circle_factor_output.read_text() != circle_factor
        ):
            raise SystemExit("installed Gate circle factor Lean export changed")
        if pcs_opening is not None and (
            not args.pcs_opening_output.is_file() or
            args.pcs_opening_output.read_text() != pcs_opening
        ):
            raise SystemExit("installed Gate PCS opening link Lean export changed")
        if base_vm is not None and (
            not args.base_vm_output.is_file() or
            args.base_vm_output.read_text() != base_vm
        ):
            raise SystemExit("installed Gate base VM Lean export changed")
        if ext_vm is not None and (
            not args.ext_vm_output.is_file() or
            args.ext_vm_output.read_text() != ext_vm
        ):
            raise SystemExit("installed Gate extension VM Lean export changed")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
        if logup is not None:
            args.logup_output.parent.mkdir(parents=True, exist_ok=True)
            args.logup_output.write_text(logup)
        if composition is not None:
            args.composition_output.parent.mkdir(parents=True, exist_ok=True)
            args.composition_output.write_text(composition)
        if transcript is not None:
            args.transcript_output.parent.mkdir(parents=True, exist_ok=True)
            args.transcript_output.write_text(transcript)
        if openings is not None:
            args.oods_openings_output.parent.mkdir(parents=True, exist_ok=True)
            args.oods_openings_output.write_text(openings)
        if composition_opening is not None:
            args.composition_opening_output.parent.mkdir(parents=True, exist_ok=True)
            args.composition_opening_output.write_text(composition_opening)
        if circle_factor is not None:
            args.circle_factor_output.parent.mkdir(parents=True, exist_ok=True)
            args.circle_factor_output.write_text(circle_factor)
        if pcs_opening is not None:
            args.pcs_opening_output.parent.mkdir(parents=True, exist_ok=True)
            args.pcs_opening_output.write_text(pcs_opening)
        if base_vm is not None:
            args.base_vm_output.parent.mkdir(parents=True, exist_ok=True)
            args.base_vm_output.write_text(base_vm)
        if ext_vm is not None:
            args.ext_vm_output.parent.mkdir(parents=True, exist_ok=True)
            args.ext_vm_output.write_text(ext_vm)


if __name__ == "__main__":
    main()
