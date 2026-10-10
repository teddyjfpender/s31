#!/usr/bin/env python3
"""Export the pinned STWZEVA/1 Gate arithmetic prefix into checked Lean.

This decoder intentionally supports one bounded native program. The Lean
artifact proves a universal identity for its nine arithmetic roots. The two
LogUp roots, OODS mask selection, committed openings and PCS/FRI are outside
this exporter and remain explicit correspondence obligations.
"""

from __future__ import annotations

import argparse
import hashlib
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
        "import S31.Gadgets.Air.DirectGateEvaluatorCells", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic", "",
        "open S31.Gadgets.Packed", "",
        "open S31.Gadgets.Air.DirectGateEvaluatorCells", "",
        "set_option linter.unusedVariables false", "",
        "/-- The first nine installed roots are secure-column injections of",
        "base registers 24, 28, 31, 34, 37, 61, 85, 103, 121.",
        "Registers 25 in their other coordinates are the bytecode constant zero. -/",
        "def bytecodeArithmetic (cells : Cells) : List F := Id.run do",
    ]
    for op, tree, dst, a, b, imm in base[:122]:
        if op == 0:
            require(imm == 0 and tree in (0, 1), "arithmetic prefix reads a shifted/interaction cell")
            expression = f"cells.{('localFixed', 'main')[tree]} {a}"
        elif op == 3:
            expression = str(a)
        else:
            expression = f"r{a} { {4: '+', 5: '-', 6: '*'}[op] } r{b}"
        lines.append(f"  let r{dst} : F := {expression}")
    lines += ["  return [r24, r28, r31, r34, r37, r61, r85, r103, r121]", "",
              "/-- Universal M31 arithmetic correspondence for the selected",
              "installed bytecode prefix; LogUp roots 9–10 remain separate. -/",
              "theorem bytecode_arithmetic_eq (cells : Cells) :",
              "    bytecodeArithmetic cells = arithmetic cells := by",
              "  simp [bytecodeArithmetic, arithmetic, decodedRow, semanticFixed,",
              "    S31.Gadgets.Air.NativeQm31Air.residuals,",
              "    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,",
              "    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal]", "",
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = render(args.package)
    if args.check:
        if not args.output.is_file() or args.output.read_text() != result:
            raise SystemExit("installed Gate bytecode Lean export changed")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)


if __name__ == "__main__":
    main()
