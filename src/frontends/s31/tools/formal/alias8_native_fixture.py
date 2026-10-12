"""Generate the case07 Lean constant certificate from checked native diagnostics.

The source-bound four-case checker first validates all 512 fixed/main rows,
the sealed fixed root, source/public projection, arithmetic, and exact Gate
address/value ledger. Lean then independently checks the emitted constant
cells and values. The diagnostic export is not a PCS-authenticated opening.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[5]
ACCEPTANCE = ROOT / "src/frontends/s31/tests/acceptance/compiler_correspondence"
sys.path.insert(0, str(ACCEPTANCE))
import full_native_roster as roster  # noqa: E402

FIXTURE = ACCEPTANCE / "fixtures/case07-full-native-roster.json"
OUTPUT = ROOT / (
    "formal/s31/S31/Gadgets/Functional/Correspondence/"
    "GeneratedAlias8NativeFixture.lean"
)
PINNED_FIXTURE_SHA256 = "64328f7ea1cbd817c3a719489791aaedbc7b17829f2d241ede44a2f354ead234"
NAMESPACE = "S31.Functional.Correspondence.GeneratedAlias8NativeFixture"


def direct_spelling(sample) -> str:
    names = ["x"] + [f"p{i}" for i in range(1, sample.gate_count + 1)]
    body = [f"let p{i} = {names[left]} {'+' if op == '+' else '.*'} {names[right]};"
            for i, (op, left, right) in enumerate(sample.steps, 1)]
    return ("circuit mutation_7(public x: [m31; 4]) -> public [m31; 4] "
            + "{ " + " ".join(body) + f" {names[sample.return_id]} }}")


def render() -> str:
    raw = FIXTURE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != PINNED_FIXTURE_SHA256:
        raise ValueError("case07 diagnostic fixture bytes changed")
    data = json.loads(raw)
    sample = next(sample for sample, prefix in roster.selected_samples()
                  if prefix == "case07")
    pinned = roster.pinned_cases()[sample.label]
    roster.check_case(data, sample, pinned)
    fixed = data["physical"]["fixed_columns"]
    main = data["physical"]["main_columns"]
    n = sample.gate_count
    n_add = sum(op == "+" for op, _, _ in sample.steps)
    add_rows = 476 - (n - n_add)
    constant_rows = [*range(11 + n_add, add_rows), add_rows,
                     *range(add_rows + 7, add_rows + 28)]
    if len(constant_rows) != 479:
        raise ValueError("case07 constant band is not 479 rows")
    values: list[tuple[int, int, int, int] | None] = [None] * 512
    for row, address in enumerate(fixed[6]):
        if values[address] is not None:
            raise ValueError("duplicate output address")
        values[address] = tuple(main[column][row] for column in range(8, 12))
    if any(value is None for value in values):
        raise ValueError("missing output address")
    direct = direct_spelling(sample)
    alias_relation, _ = roster.parse_source(sample.source.encode())
    direct_relation, _ = roster.parse_source(direct.encode())
    if direct_relation != alias_relation:
        raise ValueError("producer-only spelling changes the admitted relation")
    source = sample.source.encode()
    if hashlib.sha256(source).hexdigest() != data["source_sha256"]:
        raise ValueError("case07 source digest differs")
    lines = [
        "import S31.Gadgets.Functional.Correspondence.NativeConstantIslandCertificate",
        "",
        "/-!",
        "Case07 literal cells and one coherent value per Gate address, extracted",
        "from the checked-in full native diagnostic. The generating checker",
        "validates the whole 512-row export against source, schedule and sealed",
        "fixed root. These literals are unauthenticated by PCS openings.",
        "-/",
        "",
        f"namespace {NAMESPACE}",
        "",
        "open S31.Gadgets.Packed",
        "open S31.Functional.SSAAirColumnCells",
        "",
        "set_option maxRecDepth 16384",
        "",
        f"-- Case07 diagnostic fixture SHA-256: {digest}",
        f"-- Case07 source SHA-256: {data['source_sha256']}",
        f"-- Native sealed fixed root: {data['sealed_key_root']}",
        "def constantCells : List ColumnCell := [",
    ]
    fields = ("traceRow", "addFlag", "subFlag", "mulFlag", "pointwiseMulFlag",
              "in0", "in1", "out", "mults")
    for row in constant_rows:
        words = (row, *(fixed[column][row] for column in range(8)))
        lines.append("  { " + ", ".join(f"{key} := {value}" for key, value in zip(fields, words, strict=True)) + " },")
    lines += ["]", "", "def nativeValues : List Quad := ["]
    for value in values:
        assert value is not None
        lines.append("  ⟨" + ", ".join(map(str, value)) + "⟩,")
    lines += [
        "]", "", "def directBytes : List Nat := [",
    ]
    encoded = list(direct.encode())
    for offset in range(0, len(encoded), 20):
        lines.append("  " + ", ".join(map(str, encoded[offset:offset + 20])) + ",")
    lines += [
        "]", "", "theorem constant_cells_length : constantCells.length = 479 := by decide",
        "theorem native_values_length : nativeValues.length = 512 := by decide",
        "", f"end {NAMESPACE}", "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = render()
    if args.write:
        OUTPUT.write_text(content)
        print(f"wrote {OUTPUT.relative_to(ROOT)}")
    elif not OUTPUT.exists() or OUTPUT.read_text() != content:
        raise SystemExit("case07 Lean fixture differs from checked native diagnostic")
    else:
        print("checked case07 Lean fixture")


if __name__ == "__main__":
    main()
