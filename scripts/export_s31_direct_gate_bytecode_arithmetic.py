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
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = render(args.package)
    logup = render_logup(args.package) if args.logup_output is not None else None
    composition = (render_composition(args.package)
                   if args.composition_output is not None else None)
    transcript = (render_transcript_params(args.package)
                  if args.transcript_output is not None else None)
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


if __name__ == "__main__":
    main()
