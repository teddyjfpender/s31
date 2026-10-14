#!/usr/bin/env python3
"""Independent executable XDM04 framing, topology and certificate audit.

Input is a fixture emitted by the exact experimental CAS05 draft. This code
uses Python's hashlib and local integer/index formulas, not the Zig hash or
topology helpers. It does not turn a finite differential test into a proof of
Zig semantics, prove BLAKE2s collision resistance, or enable CAS05 in S31.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
from pathlib import Path
from typing import Any

Q = 2**31 - 1
MAGIC = b"S31XDM04"
LEAF_TAG = b"S31XDL03"
UPPER_TAG = b"S31XDU03"
INSERTED_TAG = b"S31XDI03"


class AuditError(ValueError):
    pass


def need(ok: bool, message: str) -> None:
    if not ok:
        raise AuditError(message)


def digest(preimage: bytes) -> bytes:
    return hashlib.blake2s(preimage, digest_size=32).digest()


def row_bytes(row: list[int]) -> bytes:
    need(0 < len(row) <= 64, "invalid row width")
    need(all(type(v) is int and 0 <= v < Q for v in row), "noncanonical M31 row")
    return struct.pack("<H", len(row)) + b"".join(struct.pack("<I", v) for v in row)


def leaf_preimage(row: list[int]) -> bytes:
    return LEAF_TAG + row_bytes(row)


def upper_preimage(left: bytes, right: bytes) -> bytes:
    need(len(left) == len(right) == 32, "invalid child digest width")
    return UPPER_TAG + left + right


def inserted_preimage(left: bytes, right: bytes, row: list[int]) -> bytes:
    return INSERTED_TAG + digest(upper_preimage(left, right)) + row_bytes(row)


def leaf(row: list[int]) -> bytes:
    return digest(leaf_preimage(row))


def upper(left: bytes, right: bytes) -> bytes:
    return digest(upper_preimage(left, right))


def inserted(left: bytes, right: bytes, row: list[int]) -> bytes:
    return digest(inserted_preimage(left, right, row))


def children(level: int, index: int) -> tuple[int, int]:
    if level == 0:
        return (0, 1)
    first = (index & 1) | ((index >> 1) << 2)
    return (first, first | 2)


def sibling(level: int, index: int) -> int:
    return index ^ (1 if level == 1 else 2)


def parent(level: int, index: int) -> int:
    return 0 if level == 1 else (index & 1) | ((index >> 2) << 1)


def pair_base(raw: int, height: int) -> int:
    return (raw >> (height + 1)) << 1


def path_position(level: int, index: int) -> int:
    position = 0
    place = 1
    while level:
        position += place * (((index if level == 1 else index >> 1) & 1))
        index = parent(level, index)
        level -= 1
        place <<= 1
    return position


class Cursor:
    def __init__(self, wire: bytes):
        self.wire = wire
        self.at = 0

    def take(self, count: int) -> bytes:
        need(0 <= count <= len(self.wire) - self.at, "truncated XDM04 wire")
        out = self.wire[self.at : self.at + count]
        self.at += count
        return out

    def u16(self) -> int:
        return struct.unpack("<H", self.take(2))[0]

    def u32(self) -> int:
        return struct.unpack("<I", self.take(4))[0]

    def row(self, width: int) -> list[int]:
        row = [self.u32() for _ in range(width)]
        need(all(v < Q for v in row), "noncanonical XDM04 wire row")
        return row


def _hash(text: str) -> bytes:
    need(type(text) is str and len(text) == 64, "invalid hex digest")
    try:
        out = bytes.fromhex(text)
    except ValueError as exc:
        raise AuditError("invalid hex digest") from exc
    need(len(out) == 32, "invalid digest width")
    return out


def _profile(fixture: dict[str, Any]) -> tuple[int, int, list[int], list[int]]:
    k = fixture["largest_log_size"]
    heights = fixture["height_count"]
    cols = fixture["columns"]
    raw = fixture["raw_queries"]
    need(type(k) is int and type(heights) is int and 2 <= heights <= 8 and
         heights + 2 <= k <= 22, "invalid XDM04 profile geometry")
    need(type(cols) is list and len(cols) == heights and
         all(type(c) is int and 1 <= c <= 64 for c in cols), "invalid XDM04 columns")
    need(type(raw) is list and 1 <= len(raw) <= 1 << 14 and
         all(type(x) is int and 0 <= x < 1 << k for x in raw), "invalid raw queries")
    per_query = 4 + 8 * sum(cols)
    need(len(raw) * per_query <= 64 * 1024 * 1024 - 128, "XDM04 profile wire bound")
    return k, heights, cols, raw


def _committed_tree(fixture: dict[str, Any], k: int, heights: int,
                    cols: list[int], max_nodes: int) -> list[list[bytes]]:
    source = fixture["source_columns"]
    need(type(source) is list and len(source) == heights, "source height shape")
    need((1 << (k + 1)) - 1 <= max_nodes, "full-tree audit resource cap")
    for height, columns in enumerate(source):
        need(type(columns) is list and len(columns) == cols[height], "source column count")
        for column in columns:
            need(type(column) is list and len(column) == 1 << (k - height),
                 "source column length")
            need(all(type(v) is int and 0 <= v < Q for v in column),
                 "noncanonical source column")
    layers: list[list[bytes]] = [[] for _ in range(k + 1)]
    layers[k] = [leaf([column[index] for column in source[0]])
                 for index in range(1 << k)]
    for level in range(k - 1, -1, -1):
        height = k - level
        layer = []
        for index in range(1 << level):
            left_index, right_index = children(level, index)
            left, right = layers[level + 1][left_index], layers[level + 1][right_index]
            node = (inserted(left, right, [column[index] for column in source[height]])
                    if height < heights else upper(left, right))
            layer.append(node)
        layers[level] = layer
    need(layers[0][0] == _hash(fixture["root"]), "committed source root mismatch")
    return layers


def check_fixture(fixture: dict[str, Any], *, max_nodes: int = 1 << 18) -> dict[str, int]:
    """Check native wire/capture against independently framed committed rows."""
    k, heights, cols, raw = _profile(fixture)
    layers = _committed_tree(fixture, k, heights, cols, max_nodes)
    root = layers[0][0]
    all_positions = []
    for level in range(1, k + 1):
        for index in range(1 << level):
            up = parent(level, index)
            all_positions.append({
                "level": level, "index": index, "parent": up,
                "sibling": sibling(level, index),
                "children": list(children(level - 1, up)),
                "path_position": path_position(level, index),
            })
    need(fixture["topology"] == all_positions,
         "native transposed topology/index table mismatch")
    try:
        wire = bytes.fromhex(fixture["wire"])
    except (TypeError, ValueError) as exc:
        raise AuditError("invalid wire hex") from exc
    need(len(wire) <= 64 * 1024 * 1024, "XDM04 wire too large")
    cursor = Cursor(wire)
    need(cursor.take(8) == MAGIC and cursor.u16() == 4 and cursor.u16() == 0,
         "XDM04 magic/version/reserved")
    need(cursor.u32() == len(wire) and cursor.u32() == k and
         cursor.u16() == heights and cursor.u16() == 0 and
         cursor.u32() == len(raw), "XDM04 header geometry")
    need([cursor.u16() for _ in range(heights)] == cols, "XDM04 header column widths")
    need(cursor.take(32) == root, "XDM04 header root")
    rows: dict[tuple[int, int, int], list[int]] = {}
    first: dict[tuple[int, int], list[int]] = {}
    for query, raw_index in enumerate(raw):
        need(cursor.u32() == raw_index, "XDM04 raw query order")
        for height in range(heights):
            base = pair_base(raw_index, height)
            for j in range(2):
                row = cursor.row(cols[height])
                index = base + j
                need(row == [column[index] for column in fixture["source_columns"][height]],
                     "XDM04 opened row differs from committed source")
                address = (height, index)
                need(address not in first or first[address] == row,
                     "duplicate projected row mismatch")
                first[address] = row
                rows[height, query, j] = row
    witness_count = cursor.u32()
    maximum = len(raw) * (4 * (heights - 1) + 2 * k)
    need(witness_count <= maximum and len(wire) - cursor.at == 32 * witness_count,
         "XDM04 witness count/length")
    nodes: dict[tuple[int, int], bytes] = {}

    def put(level: int, index: int, value: bytes) -> None:
        address = (level, index)
        need(address not in nodes or nodes[address] == value, "conflicting projected node")
        nodes[address] = value
        need(layers[level][index] == value, "sparse node differs from committed tree")

    used = 0

    def child(level: int, index: int) -> bytes:
        nonlocal used
        address = (level, index)
        if address not in nodes:
            need(used < witness_count, "XDM04 witness exhausted")
            put(level, index, cursor.take(32))
            used += 1
        return nodes[address]

    for query, raw_index in enumerate(raw):
        base = pair_base(raw_index, 0)
        for j in range(2):
            put(k, base + j, leaf(rows[0, query, j]))
    for height in range(1, heights):
        level = k - height
        for query, raw_index in enumerate(raw):
            base = pair_base(raw_index, height)
            for j in range(2):
                index = base + j
                left_index, right_index = children(level, index)
                put(level, index, inserted(child(level + 1, left_index),
                                            child(level + 1, right_index),
                                            rows[height, query, j]))
    active = [pair_base(raw_index, heights - 1) + j for raw_index in raw for j in range(2)]
    for level in range(k - heights + 1, 0, -1):
        next_active = []
        for index in sorted(set(active)):
            need((level, index) in nodes, "missing active XDM04 node")
            child(level, sibling(level, index))
            up = parent(level, index)
            left_index, right_index = children(level - 1, up)
            put(level - 1, up, upper(nodes[level, left_index], nodes[level, right_index]))
            next_active.append(up)
        active = next_active
    need(used == witness_count and cursor.at == len(wire) and nodes[0, 0] == root,
         "XDM04 witness exhaustion/root")

    expected_openings = fixture["openings"]
    need(type(expected_openings) is list and len(expected_openings) == len(raw) * heights * 2,
         "native capture opening count")
    for query, raw_index in enumerate(raw):
        for height in range(heights):
            level = k - height
            for j in range(2):
                index = pair_base(raw_index, height) + j
                first_node = nodes[level, index]
                steps: list[dict[str, Any]] = []
                current, at_level, at_index = first_node, level, index
                binary = path_position(level, index)
                position = binary
                for _ in range(level):
                    other = nodes[at_level, sibling(at_level, at_index)]
                    up_index = parent(at_level, at_index)
                    parent_height = k - (at_level - 1)
                    inserted_row = (first[parent_height, up_index]
                                    if 0 < parent_height < heights else None)
                    steps.append({"sibling": other.hex(), "inserted_row": inserted_row})
                    left, right = (current, other) if position & 1 == 0 else (other, current)
                    current = (inserted(left, right, inserted_row)
                               if inserted_row is not None else upper(left, right))
                    at_level -= 1
                    at_index = up_index
                    position >>= 1
                    need(current == nodes[at_level, at_index], "capture path node mismatch")
                need(current == root and at_index == 0, "capture path root/index")
                certificate = {
                    "height": height, "query": query, "j": j,
                    "native_level": level, "native_index": index,
                    "path_position": binary, "row": rows[height, query, j],
                    "start": first_node.hex(), "steps": steps,
                }
                actual = expected_openings[(query * heights + height) * 2 + j]
                need(actual == certificate, "native capture differs from independent certificate")
    return {"queries": len(raw), "heights": heights,
            "openings": len(expected_openings), "witness_hashes": witness_count}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    parser.add_argument("--max-nodes", type=int, default=1 << 18)
    args = parser.parse_args()
    try:
        result = check_fixture(json.loads(args.fixture.read_text()), max_nodes=args.max_nodes)
    except (AuditError, KeyError, IndexError, TypeError, json.JSONDecodeError) as exc:
        parser.exit(1, f"XDM04 framing audit rejected: {exc}\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
