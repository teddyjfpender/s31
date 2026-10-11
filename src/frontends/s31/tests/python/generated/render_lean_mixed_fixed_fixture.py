#!/usr/bin/env python3
"""Check native N1/N8 fixed columns against a hand-derived row schedule.

The Zig exporter reads production preprocessed columns. This script computes
the selected source path independently, compares every eight-cell tuple, and
emits a Lean fixture. The fixed root is a pinned native regression, not a Lean
proof of commitment authentication.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
OUTPUT = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/GeneratedMixedFixedRows.lean"
SOURCE = {
    1: "8c5296ef964e3be770e442cd28b66eed3051e210bdd6a97e265a4cd2c5962f75",
    8: "08b5c20367e910261a194658bc3753038037fb85bc8f16dbc7f9191c7d1f45ff",
}
ROOTS = {
    1: "761dd5a42142ab2e8327ac0ca7ad31e1375b4f27c8e752eff766d7feea37cf00",
    8: "68d7419f5be9e6e508ba2fafe1d8b34f4289cd2294708c332f4d646c4debe4b8",
}
ROWS_SHA256 = {
    1: "3629e43e13b0986ee2d81f362aefe372f572d2cb89870b2fcf2f1f6a81c92180",
    8: "6ffc7b99c4a6d49325a4706814febb831ea49357b17fd6b3893fef740d905709",
}
P = 2**31 - 1


def require(condition: bool, *detail: object) -> None:
    if not condition:
        raise ValueError("mixed fixed-row correspondence mismatch: " + repr(detail))


def expected_rows(count: int) -> dict[int, tuple[int, ...]]:
    """Compiler-independent N-call source/pack/public address schedule."""
    require(count in (1, 8), "count", count)
    add_count = 468 - 7 * count
    mul_count = 30 + 3 * count
    point_start = add_count + 1 + mul_count
    mul_start = add_count + 1
    require(point_start + 13 + 4 * count == 512, "row geometry", count)
    selected: dict[int, tuple[int, ...]] = {}

    def add(row: int, op: int, a: int, b: int, out: int, uses: int) -> None:
        require(0 <= row < 512 and 0 <= op < 4, "row/op", count, row, op)
        fields = tuple(int(i == op) for i in range(4)) + (a, b, out, uses)
        require(all(0 <= item < P for item in fields), "noncanonical", count, row)
        require(row not in selected, "duplicate selected row", count, row)
        selected[row] = fields

    def scalar(state: int, lane: int) -> int:
        return (11 + lane) if state == 0 else (23 + 10 * (state - 1) + lane)

    def packed(state: int) -> int:
        return 22 + 10 * state

    # Every four-word state is packed with three basis multiplications and
    # three left-associated additions. Interior packed outputs are dead.
    for state in range(count + 1):
        base = packed(state)
        terms = (base - 5, base - 3, base - 1)
        partials = (base - 4, base - 2, base)
        for part, basis in enumerate((15, 2, 16)):
            add(mul_start + 3 * state + part, 2, basis,
                scalar(state, part + 1), terms[part], 1)
            left = scalar(state, 0) if part == 0 else partials[part - 1]
            uses = 1 if part < 2 else (2 if state in (0, count) else 0)
            add(3 * state + part, 0, left, terms[part], partials[part], uses)

    last, total, product = packed(count), packed(count) + 1, packed(count) + 2
    add(3 * (count + 1), 0, packed(0), last, total, 4)
    add(point_start, 3, packed(0), last, product, 4)

    mask_offsets = (3, 4, 7, 10, 13, 14, 16, 18)
    copy_offsets = (3, 6, 9, 12, 13, 15, 17, 19)
    units = (1, 15, 2, 16)
    for slot in range(8):
        source = total if slot < 4 else product
        add(point_start + 1 + slot, 3, source, units[slot % 4],
            last + mask_offsets[slot], 1)
        add(3 * (count + 1) + 1 + slot, 0,
            last + copy_offsets[slot], 0, 3 + slot, 1)

    inverse_slots = (1, 2, 3, 5, 6, 7)
    inverse_inputs = (5, 8, 11, 5, 8, 11)
    inverse_outputs = (6, 9, 12, 15, 17, 19)
    for index, slot in enumerate(inverse_slots):
        add(mul_start + 3 * (count + 1) + index, 2,
            last + mask_offsets[slot], last + inverse_inputs[index],
            last + inverse_outputs[index], 1)

    # Native finalization verifies each guessed scalar is base-field-valued.
    for state in range(count + 1):
        for lane in range(4):
            address = scalar(state, lane)
            add(point_start + 9 + 4 * state + lane, 3,
                address, 1, address, 3 if state in (0, count) else 4)
    return selected


def decode_native_json(raw: str) -> dict:
    def unique_pairs(pairs: list[tuple[str, object]]) -> dict:
        decoded = {}
        for key, value in pairs:
            require(key not in decoded, "duplicate JSON key", key)
            decoded[key] = value
        return decoded

    value = json.loads(raw, object_pairs_hook=unique_pairs)
    require(type(value) is dict, "native JSON top-level object")
    return value


def read_native(path: Path | None) -> dict:
    if path is not None:
        return decode_native_json(path.read_text())
    run = subprocess.run(
        ["zig", "build", "--build-file", "src/frontends/s31/build.zig",
         "export-mixed-fixed-rows", "-Doptimize=ReleaseFast", "-j1"],
        cwd=ROOT, check=True, capture_output=True, text=True, timeout=300,
    )
    return decode_native_json(run.stdout)


def validated_cases(native: dict) -> dict[int, list[list[int]]]:
    require(native["schema"] == "s31-mixed-fixed-native-v1", "schema")
    cases = {case["count"]: case for case in native["cases"]}
    require(set(cases) == {1, 8} and len(native["cases"]) == 2, "cases")
    result = {}
    for count in (1, 8):
        case = cases[count]
        require(case["source_sha256"] == SOURCE[count], "source", count)
        require(case["fixed_root"] == ROOTS[count], "fixed root", count)
        rows = case["rows"]
        require(len(rows) == 512 and all(len(row) == 8 for row in rows), "shape", count)
        require(all(all(type(value) is int and 0 <= value < P for value in row)
                    for row in rows), "canonical cells", count)
        digest = hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()
        require(digest == ROWS_SHA256[count], "complete row digest", count, digest)
        add_count = 468 - 7 * count
        point_start = add_count + 1 + 30 + 3 * count
        require(all(row[:4] == [int(col == (0 if i < add_count else
                                             1 if i == add_count else
                                             2 if i < point_start else 3))
                                       for col in range(4)]
                    for i, row in enumerate(rows)), "opcode partition", count)
        for index, expected in expected_rows(count).items():
            require(tuple(rows[index]) == expected,
                    "selected row", count, index, rows[index], expected)
        result[count] = rows
    return result


def render(native: dict) -> str:
    rows_by_count = validated_cases(native)
    lines = [
        "import S31.Gadgets.Functional.SSAGeneralDecodedTraceBridge",
        "",
        "/-! Native full fixed-column exports for the source-pinned mixed N1/N8 family.",
        "The Python generator independently checks the selected pack, public",
        "unpack/copy, and scalar bridge schedule against these 512-row exports.",
        "This is source-pinned selected-row correspondence against native",
        "exports. It does not authenticate",
        "a prover trace or reduce verifier acceptance to exact Gate balance. -/",
        "",
        "namespace S31.Functional.Correspondence.GeneratedMixedFixedRows",
        "",
        "open S31.Gadgets.Packed",
        "open S31.Gadgets.Air.DecodedDirectGateTrace",
        "open S31.Functional.SSAAirColumnCells",
        "open S31.Functional.SSANativePolynomialRows",
        "open S31.Functional.SSAGeneralDecodedTraceBridge",
        "",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 2000000",
        "",
    ]
    for count in (1, 8):
        rows = rows_by_count[count]
        schedule = expected_rows(count)
        digest = hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()
        lines += [
            f"namespace N{count}",
            f"/-- Native source SHA-256: {SOURCE[count]}; fixed root: {ROOTS[count]}.",
            f"Canonical JSON row digest: {digest}. -/",
            "def fixedRows : List (List Nat) := [",
            ",\n".join("  [" + ", ".join(map(str, row)) + "]" for row in rows),
            "]",
            "",
            "theorem fixed_rows_length : fixedRows.length = 512 := by decide",
            "theorem fixed_row_width : ∀ i : Fin 512,",
            "    (fixedRows[i.val]!).length = 8 := by decide",
            "",
            f"def expectedOpcode (row : Nat) : Nat :=",
            f"  if row < {468 - 7 * count} then 0 else",
            f"  if row = {468 - 7 * count} then 1 else",
            f"  if row < {468 - 7 * count + 1 + 30 + 3 * count} then 2 else 3",
            "",
            "theorem fixed_opcode_partition : ∀ i : Fin 512,",
            "    (fixedRows[i.val]!).take 4 =",
            "      (List.range 4).map (fun c =>",
            "        if c = expectedOpcode i.val then 1 else 0) := by decide",
            "",
            "def selectedCells : List ColumnCell := [",
            ",\n".join(
                "  { traceRow := %d, addFlag := %d, subFlag := %d, mulFlag := %d, "
                "pointwiseMulFlag := %d, in0 := %d, in1 := %d, out := %d, mults := %d }"
                % ((index,) + values)
                for index, values in sorted(schedule.items())),
            "]",
            "",
            "theorem selected_cells_bounded : ∀ cell ∈ selectedCells, cell.traceRow < 512 := by decide",
            "theorem all_fixed_cells_canonical : ∀ i : Fin 512, ∀ c : Fin 8,",
            "    (fixedRows[i.val]!)[c.val]! < 2147483647 := by decide",
            "theorem selected_rows_match : ∀ cell ∈ selectedCells,",
            "    fixedRows[cell.traceRow]! =",
            "      [cell.addFlag, cell.subFlag, cell.mulFlag, cell.pointwiseMulFlag,",
            "        cell.in0, cell.in1, cell.out, cell.mults] := by decide",
            "",
            "def fixedAt (i : Fin 512) (c : Fin 8) : F :=",
            "  (fixedRows[i.val]!)[c.val]!",
            "",
            "theorem fixedAt_exact (i : Fin 512) (c : Fin 8) :",
            "    (fixedAt i c).val = (fixedRows[i.val]!)[c.val]! := by",
            "  change ((fixedRows[i.val]!)[c.val]! % 2147483647) =",
            "    (fixedRows[i.val]!)[c.val]!",
            "  exact Nat.mod_eq_of_lt (all_fixed_cells_canonical i c)",
            "",
            "/-- Every hand-derived selected cell matches the pinned native",
            "fixed columns in any decoded trace carrying that export. -/",
            "theorem selected_fixed_matches (trace : Trace 9)",
            "    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8, trace.fixed i c = fixedAt i c) :",
            "    ∀ cell ∈ selectedCells, fixedMatches trace cell := by",
            "  intro cell hcell",
            "  let i : Fin 512 := ⟨cell.traceRow, selected_cells_bounded cell hcell⟩",
            "  have hrow := selected_rows_match cell hcell",
            "  have hval (c : Fin 8) : (trace.fixed i c).val =",
            "      ([cell.addFlag, cell.subFlag, cell.mulFlag, cell.pointwiseMulFlag,",
            "        cell.in0, cell.in1, cell.out, cell.mults][c.val]!) := by",
            "    rw [hfixed, fixedAt_exact]",
            "    simp [i, hrow]",
            "  refine ⟨i, rfl, ?_, ?_, ?_, ?_, ?_⟩",
            "  · simp [row, hfixed, fixedAt, i, hrow, cellFlags]",
            "  · simpa [row] using hval ⟨4, by decide⟩",
            "  · simpa [row] using hval ⟨5, by decide⟩",
            "  · simpa [row] using hval ⟨6, by decide⟩",
            "  · simpa [row] using hval ⟨7, by decide⟩",
            "",
            f"end N{count}",
            "",
        ]
    lines += ["end S31.Functional.Correspondence.GeneratedMixedFixedRows", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native-json", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    generated = render(read_native(args.native_json))
    if args.write:
        OUTPUT.write_text(generated)
    elif OUTPUT.read_text() != generated:
        raise SystemExit(f"stale generated Lean fixture: {OUTPUT}")
    print(f"checked {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
