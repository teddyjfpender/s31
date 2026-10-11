"""Independent reconstruction of the bounded mixed mask-point digest.

The installed AIR bundle and the closed pair/many constructor mask layouts
are inputs to this audit. The JSON manifest is diagnostic, not a verifier key.
"""

from __future__ import annotations

import hashlib
import struct
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[6]
sys.path.insert(0, str(ROOT / "scripts"))
from export_s31_direct_gate_bytecode_arithmetic import (  # noqa: E402
    BUNDLE, decoded_program, gate_program,
)

P = (1 << 31) - 1
GENERATOR = (2, 1_268_011_823)
CENTER = (0, 1)  # secureFieldPointFromRandomSeed(QM31.one())


def circle_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return ((a[0] * b[0] - a[1] * b[1]) % P,
            (a[0] * b[1] + a[1] * b[0]) % P)


def circle_step(log_size: int) -> tuple[int, int]:
    if not 1 <= log_size <= 30:
        raise ValueError("unsupported mixed composition log size")
    step = GENERATOR
    for _ in range(31 - log_size):
        step = circle_add(step, step)
    return step


def gate_offsets() -> tuple[list[list[int]], list[list[int]]]:
    """Read first-use offset order from the checked official Gate bytecode."""
    base, _, _ = decoded_program(gate_program(BUNDLE.read_bytes()))
    trees = ([[] for _ in range(12)], [[] for _ in range(8)])
    for op, tree, _dst, column, _b, offset in base:
        if op != 0 or tree not in (1, 2):
            continue
        masks = trees[tree - 1][column]
        if offset not in masks:
            masks.append(offset)
    if any(not offsets or len(offsets) > 2 or
           any(offset not in (-1, 0) for offset in offsets)
           for tree in trees for offsets in tree):
        raise ValueError("unsupported Gate mask offsets")
    return trees


def component_masks(key: str, circuit: tuple[list[list[int]], list[list[int]]]
                    ) -> tuple[list[list[int]], list[list[int]]]:
    if key == "bundled_circuit":
        return circuit
    if key in ("pair_chip", "many_chip"):
        return ([[0] for _ in range(9)],
                [[0] for _ in range(4)] + [[-1, 0] for _ in range(4)])
    if key in ("pair_bridge", "many_bridge"):
        return ([[0, 1] for _ in range(8)],
                [[0] for _ in range(16)] + [[-1, 0] for _ in range(4)])
    raise ValueError("unregistered mixed mask constructor")


def recompute(manifest: dict) -> str:
    """Hash the exact native u32/log/point stream for trees 0, 1 and 2."""
    calls = manifest["call_count"]
    slots = manifest["slots"]
    if not 1 <= calls <= 8 or len(slots) != 1 + 2 * calls:
        raise ValueError("invalid bounded mixed mask roster")
    circuit = gate_offsets()
    trees: list[list[tuple[int, list[int]]]] = [[], [], []]
    trees[0] = [(slots[0]["trace_log_size"], [0]) for _ in range(8)]
    for index, slot in enumerate(slots):
        expected = ("bundled_circuit" if index == 0 else
                    ("pair" if (index - 1) // 2 < 2 else "many") +
                    ("_chip" if index % 2 else "_bridge"))
        if slot["registry_key"] != expected or slot["source_kind"] != expected:
            raise ValueError("mixed mask component order differs")
        main, interaction = component_masks(expected, circuit)
        if (slot["main_columns"] != len(main) or
                slot["interaction_columns"] != len(interaction)):
            raise ValueError("mixed mask component width differs")
        log_size = slot["trace_log_size"]
        trees[1].extend((log_size, mask) for mask in main)
        trees[2].extend((log_size, mask) for mask in interaction)
    if [len(tree) for tree in trees] != manifest["tree_columns"][:3]:
        raise ValueError("mixed mask tree width differs")

    step = circle_step(manifest["composition_log_size"])
    positions = {0: CENTER, 1: circle_add(CENTER, step),
                 -1: circle_add(CENTER, (step[0], (-step[1]) % P))}
    h = hashlib.sha256(b"STWO-MIXED-MASK-POINTS-V1\0")
    for tree_id, columns in enumerate(trees):
        h.update(struct.pack("<II", tree_id, len(columns)))
        for log_size, offsets in columns:
            h.update(struct.pack("<II", log_size, len(offsets)))
            for offset in offsets:
                x, y = positions[offset]
                h.update(struct.pack("<8I", x, 0, 0, 0, y, 0, 0, 0))
    return h.hexdigest()
