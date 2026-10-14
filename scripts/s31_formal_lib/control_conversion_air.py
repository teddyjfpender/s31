"""Fail-closed source guard for the installed M31-to-u32 local AIR theorem.

The binary check pins the evaluator that the native verifier executes; the
source check pins the witness-side lookup tuple schedule. This is a source
identity and local expression check, not a proof of LogUp or PCS acceptance.
"""

from __future__ import annotations

import hashlib
import re
import struct
from pathlib import Path

from scripts.s31_formal_lib.checks import FormalError

BUNDLE = "deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin"
WITNESS = "deps/stwo-zig/src/frontends/circuit/witness/components.zig"
BUNDLE_SHA = "7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2"
PROGRAM_SHA = "bdf5fdb121c65c45bf7f6fa7b8e8916936753800d331272bcccab7a4dd97b1a3"
FIRST_BASE = (
    (0, 0, 0, 0, 0, 0), (0, 0, 1, 1, 0, 0),
    (0, 0, 2, 2, 0, 0), (0, 1, 3, 0, 0, 0),
    (0, 1, 4, 1, 0, 0), (0, 1, 5, 2, 0, 0),
    (0, 1, 6, 3, 0, 0), (3, 0, 7, 0, 0, 0),
    (3, 0, 8, 32767, 0, 0), (5, 0, 9, 8, 5, 0),
    (6, 0, 10, 3, 6, 0), (3, 0, 11, 1, 0, 0),
    (5, 0, 12, 10, 11, 0), (6, 0, 13, 12, 4, 0),
    (3, 0, 14, 65536, 0, 0), (6, 0, 15, 5, 14, 0),
    (4, 0, 16, 4, 15, 0), (5, 0, 17, 3, 16, 0),
)
LOOKUPS = (
    "Lookup.use(.{ rc16, c[1] })",
    "Lookup.use(.{ rc16, c[2] })",
    "Lookup.use(.{ rc16, m(32767).sub(c[2]) })",
    "Lookup.use(.{ gate, pp.input, c[0] })",
    "Lookup.yield(pp.mults, .{ gate, pp.output, c[1], c[2] })",
)


def _require(ok: bool, why: str) -> None:
    if not ok:
        raise FormalError("M31-to-u32 source guard: " + why)


def _unpack(data: bytes, offset: int, fmt: str) -> tuple[int, ...]:
    size = struct.calcsize(fmt)
    _require(0 <= offset <= len(data) - size, "truncated evaluator bundle")
    return struct.unpack_from(fmt, data, offset)


def selected_program(bundle: bytes) -> bytes:
    _require(hashlib.sha256(bundle).hexdigest() == BUNDLE_SHA,
             "installed AIR bundle changed")
    _require(bundle[:8] == b"STWZEVA\0" and _unpack(bundle, 8, "<I") == (1,),
             "unsupported AIR bundle version")
    _require(_unpack(bundle, 28, "<I") == (11,), "component roster changed")
    cursor = 40
    selected = None
    for index in range(11):
        (label_len, reserved, _, _, _, constraints, _, n_spans,
         n_preprocessed, n_denominators, n_ext, n_parts) = \
            _unpack(bundle, cursor, "<HH10I")
        _require(reserved == 0 and 0 < label_len <= 256 and n_parts == 1,
                 "unsupported component framing")
        cursor += 44
        _require(cursor + label_len <= len(bundle), "truncated component label")
        label = bundle[cursor:cursor + label_len]
        cursor += label_len + 12 * n_spans + 4 * n_preprocessed + \
            4 * n_denominators + 32 * n_ext
        _require(cursor + 16 <= len(bundle), "truncated evaluator part")
        root_base, size, semantic = _unpack(bundle, cursor, "<IIQ")
        cursor += 16
        _require(cursor + size <= len(bundle), "truncated evaluator")
        program = bundle[cursor:cursor + size]
        cursor += size
        if index == 3:
            _require(label == b"m_31_to_u_32" and constraints == 5 and
                     root_base == 0 and semantic == 0x035D2F1D6835C6B1 and
                     n_preprocessed == 3 and n_ext == 5,
                     "conversion component identity changed")
            selected = program
    _require(cursor == len(bundle) and selected is not None,
             "AIR bundle has trailing bytes or missing conversion")
    _require(hashlib.sha256(selected).hexdigest() == PROGRAM_SHA,
             "conversion evaluator bytecode changed")
    return selected


def check_program(program: bytes) -> None:
    header = _unpack(program, 0, "<IHHIIQQ8I")
    _require(header == (0x31505453, 1, 0, 5, 1, 0x035D2F1D6835C6B1,
                        7, 3, 0, 5, 5, 34, 78, 4, 21),
             "conversion evaluator header changed")
    _require(program[64:96] == bytes(32), "nonzero reserved evaluator header")
    sections = [_unpack(program, 96 + 24 * i, "<IIQQ") for i in range(5)]
    _require(sections == [(1, 4, 0, 0), (2, 16, 0, 0),
                          (3, 16, 0, 34), (4, 20, 544, 78),
                          (5, 4, 2104, 5)], "conversion evaluator sections changed")
    payload = 96 + 24 * 5
    _require(payload + 2104 + 4 * 5 == len(program),
             "conversion evaluator payload size changed")
    base = [_unpack(program, payload + 16 * i, "<BBHIIi") for i in range(34)]
    ext = [_unpack(program, payload + 544 + 20 * i, "<BBHIIII")
           for i in range(78)]
    roots = _unpack(program, payload + 2104, "<5I")
    _require(tuple(base[:18]) == FIRST_BASE and
             roots == (21, 22, 65, 69, 77) and
             ext[21] == (0, 0, 21, 13, 7, 7, 7) and
             ext[22] == (0, 0, 22, 17, 7, 7, 7),
             "conversion residual registers or root order changed")


def check_witness(source: str) -> None:
    _require("pub const m31_to_u32 = struct {" in source,
             "conversion witness component missing")
    block = source.split("pub const m31_to_u32 = struct {", 1)[1].split(
        "// ---------------------------------------------------------------------------", 1)[0]
    compact = re.sub(r"\s+", " ", block)
    _require("pub const n_columns = 4;" in compact and
             "pub const n_lookups = 5;" in compact,
             "conversion trace/lookup shape changed")
    calls = re.findall(r"Lookup\.(?:use|yield)\([^;\n]+\)", block)
    _require(tuple(re.sub(r"\s+", " ", call) for call in calls) == LOOKUPS,
             "conversion range or Gate lookup tuple schedule changed")


def check(root: Path, *, bundle: bytes | None = None,
          witness: str | None = None) -> None:
    data = (root / BUNDLE).read_bytes() if bundle is None else bundle
    source = (root / WITNESS).read_text() if witness is None else witness
    check_program(selected_program(data))
    check_witness(source)
