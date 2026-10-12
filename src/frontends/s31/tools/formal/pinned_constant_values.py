"""Emit a compact Lean address-value table from the pinned square4 base trace.

Run after the existing native square4 physical export is regenerated. This
script checks shape/canonicality/unique producers before writing the table.
The Lean constant-island checker independently re-evaluates every included
constant arithmetic row using the emitted values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[5]
DEFAULT_INPUT = ROOT / "formal/s31/fixtures/square4-native-physical.json"
OUTPUT = ROOT / (
    "formal/s31/S31/Gadgets/Functional/Correspondence/"
    "PinnedSquare4ConstantValues.lean"
)
P = 2**31 - 1


def render(source: Path) -> str:
    raw = source.read_bytes()
    physical = json.loads(raw)
    if physical.get("schema") != "s31-direct-gate-square4-physical-v1":
        raise ValueError("unexpected square4 physical schema")
    fixed, main = physical["fixed_columns"], physical["main_columns"]
    if len(fixed) != 8 or len(main) != 12 or any(
        len(column) != 512 for column in [*fixed, *main]
    ):
        raise ValueError("square4 physical columns must be 8+12 by 512")
    if any(type(word) is not int or not 0 <= word < P
           for column in [*fixed, *main] for word in column):
        raise ValueError("noncanonical square4 physical word")
    outputs = fixed[6]
    if sorted(outputs) != list(range(512)):
        raise ValueError("square4 output addresses are not exactly 0..511")
    values: list[tuple[int, int, int, int] | None] = [None] * 512
    for row, address in enumerate(outputs):
        values[address] = tuple(main[column][row] for column in range(8, 12))
    if any(value is None for value in values):
        raise AssertionError("missing address after permutation check")
    lines = [
        "import S31.Gadgets.Packed",
        "",
        "/-!",
        "Native square4 base values, indexed by produced Gate address.",
        "Generated from the pinned physical export; the Lean constant-island",
        "checker independently validates its local arithmetic and seed pins.",
        "This data alone is not a PCS-authenticated opening.",
        "-/",
        "",
        "namespace S31.Functional.Correspondence.PinnedSquare4ConstantValues",
        "",
        "open S31.Gadgets.Packed",
        "",
        "set_option maxRecDepth 8192",
        "",
        f"-- Source physical SHA-256: {hashlib.sha256(raw).hexdigest()}",
        "def nativeValues : List Quad := [",
    ]
    for value in values:
        assert value is not None
        lines.append("  ⟨" + ", ".join(str(word) for word in value) + "⟩,")
    lines.extend([
        "]",
        "",
        "theorem native_values_length : nativeValues.length = 512 := by decide",
        "",
        "end S31.Functional.Correspondence.PinnedSquare4ConstantValues",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=DEFAULT_INPUT)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = render(args.source)
    if args.write:
        OUTPUT.write_text(text)
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
    elif not OUTPUT.exists() or OUTPUT.read_text() != text:
        raise SystemExit("pinned square4 value table differs from native physical export")
    else:
        print("checked pinned square4 value table")


if __name__ == "__main__":
    main()
