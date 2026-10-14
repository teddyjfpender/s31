"""Replay the admitted structural M31 input allocator and packing gates.

The source profile has at most four M31 lanes per input. Public inputs are
scalar M31 guesses packed by ``simd.pack``; private inputs are one packed QM31
guess. This checks the exact address allocation and grouped gate prefixes for
that input phase. It does not inspect later public-output conversion gates.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PINNED_SOURCES = {
    "src/frontends/s31/language/relation_compiler.zig":
        "105d023fa4566c81bf8e3b2468b5a9d1e8260c2903e2ae1a04b0facc9adcc8f7",
    "deps/stwo-zig/src/frontends/circuit/builder/simd.zig":
        "4a0f480064056a7c7a87110666fce4d93a3d147d72dd7e6be8de184b75d78220",
    "deps/stwo-zig/src/frontends/circuit/builder/wrappers.zig":
        "be9de32d5f8c85dc3b3b20d0d867049c3d39f04af56b454dacd4dbbf3d6a778e",
    "deps/stwo-zig/src/frontends/circuit/builder/context.zig":
        "efe7f2bd64402ebd3983d025fbaf6301ae2004e6739bf04f753db3d0191142ef",
    "deps/stwo-zig/src/frontends/circuit/common/component_list.zig":
        "d2f1e8facad581464f365958fb8e9fb9270fb28c09363b8361898df4136ceb2b",
}

I = 1 << 32
U = 1 << 64
IU = 1 << 96
FIRST_INPUT_VAR = 11  # zero, one, u, then eight reserved public output words


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("native input packing: " + reason)


def check_input_packing(graph: dict, raw: dict[str, bytes], inputs: list[dict]) -> dict[str, int]:
    """Check exact input-phase allocation, packing gates and scalar yields."""
    for path, wanted in PINNED_SOURCES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted,
                "builder source changed; review input replay: " + path)

    specs = json.loads(raw["certificate"])["ssa"]["inputs"]
    require(len(specs) == len(inputs), "source input count differs")
    require(graph["output"] == list(range(2, FIRST_INPUT_VAR)),
            "reserved public output address roster differs")
    constants = dict(zip(graph["constant_keys"],
                         (var["idx"] for var in graph["constant_vars"]), strict=True))
    require(constants.get(0) == 0 and constants.get(1) == 1 and constants.get(U) == 2,
            "reserved constant address roster differs")

    cursor = FIRST_INPUT_VAR
    arithmetic_cursor = 0
    basis: dict[int, int] = {0: 1, 2: 2}
    early_constants: set[int] = set()
    expected_add: list[dict] = []
    expected_mul: list[dict] = []
    public_raw: list[int] = []
    values = graph["values"]
    spans = graph["node_spans"]
    wires = graph["node_wires"]

    for id_, (item, spec) in enumerate(zip(inputs, specs, strict=True)):
        require(item["id"] == spec["id"] == id_ and item["name"] == spec["name"],
                "input identity differs from accepted source")
        words = item["words"]
        require(1 <= len(words) <= 4,
                "input outside structural M31 lane profile")
        canonical_id = graph["source_map"][id_]["id"]
        require(canonical_id == id_ and canonical_id < len(spans),
                "input canonical order differs")
        span = spans[canonical_id]
        require(span["qm31_start"] == arithmetic_cursor and
                span["eq_start"] == span["eq_end"] == 0,
                "input span starts at wrong gate cursor")

        if spec["visibility"] == "private":
            require(cursor < graph["n_vars"] and
                    values[cursor] == words + [0] * (4 - len(words)) and
                    wires[canonical_id]["wires"] == [cursor],
                    "private packed guess address or value differs")
            cursor += 1
        else:
            require(spec["visibility"] == "public", "unknown input visibility")
            raw_addresses = list(range(cursor, cursor + len(words)))
            for at, word in zip(raw_addresses, words, strict=True):
                require(at < graph["n_vars"] and values[at] == [word, 0, 0, 0],
                        "public scalar guess address or value differs")
            public_raw.extend(raw_addresses)
            cursor += len(words)

            # simd.pack interns all four unit vectors, even for one lane.
            for coord, key in ((1, I), (3, IU)):
                if coord not in basis:
                    require(constants.get(key) == cursor,
                            "public packing basis constant address differs")
                    basis[coord] = cursor
                    early_constants.add(key)
                    cursor += 1

            acc = raw_addresses[0]
            for coord in range(1, len(words)):
                term = cursor
                cursor += 1
                packed = cursor
                cursor += 1
                expected_mul.append({"in0": basis[coord], "in1": raw_addresses[coord],
                                     "out": term})
                expected_add.append({"in0": acc, "in1": term, "out": packed})
                acc = packed
            require(wires[canonical_id]["wires"] == [acc],
                    "public packed input address differs")
            arithmetic_cursor += 2 * (len(words) - 1)

        require(span["qm31_end"] == arithmetic_cursor,
                "input span contains extra or missing gates")

    require(cursor <= graph["n_vars"], "input allocation exceeds variable table")
    require(graph["add"][:len(expected_add)] == expected_add and
            graph["mul"][:len(expected_mul)] == expected_mul,
            "public input packing gate order or address differs")
    require(all(key in early_constants for key, at in constants.items()
                if FIRST_INPUT_VAR <= at < cursor),
            "unaccounted interned constant in input allocation")
    yields = [{"in0": at, "in1": 1, "out": at} for at in public_raw]
    if yields:
        require(graph["pointwise_mul"][-len(yields):] == yields,
                "public scalar guess yield address differs")
    return {"input_variables": cursor - FIRST_INPUT_VAR,
            "input_packing_gates": arithmetic_cursor}
