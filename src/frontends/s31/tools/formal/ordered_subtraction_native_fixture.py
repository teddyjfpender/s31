"""Pin native fixed source rows for the ordered-subtraction release example.

The expected rows come from the independent direct-Gate schedule. A live run
builds the actual package, checks its sealed topology and key, and compares
every selected native fixed cell before writing the small reviewed snapshot.
The Lean fixture checks this snapshot against its own parsed source DAG.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
S31 = ROOT / "src/frontends/s31"
SOURCE = S31 / "examples/functional/release_sub4/manual.s31"
FUNCTIONAL_SOURCE = S31 / "examples/functional/release_sub4/functional.s31"
SNAPSHOT = ROOT / "formal/s31/fixtures/correspondence/ordered_subtraction_native.json"
LEAN = (ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/"
        "GeneratedOrderedSubtractionNativeRows.lean")
EXPORTER = S31 / "runtime/mvp_runtime.zig"
LOWERING = S31 / "language/relation_compiler.zig"
P = (1 << 31) - 1
FIELD_NAMES = ("traceRow", "addFlag", "subFlag", "mulFlag",
               "pointwiseMulFlag", "in0", "in1", "out", "mults")
AIR_FIELDS = ("canonical_ir_sha256", "profile", "chip", "raw", "padded",
              "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
              "input_packing", "public_binding", "finalization", "fri")

sys.path.insert(0, str(S31 / "python"))
import s31  # noqa: E402
from package.context import compiler_fingerprint  # noqa: E402
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, canonical_ir_bytes, check_package, parse_source,
)
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_identity() -> tuple[dict, list[list[int]]]:
    source_bytes = SOURCE.read_bytes()
    relation, syntax = parse_source(source_bytes)
    if compile_text(source_bytes.decode("ascii"))[0] != relation:
        raise AssertionError("production compiler and independent parser differ")
    functional_bytes = FUNCTIONAL_SOURCE.read_bytes()
    functional_relation, functional_syntax = parse_source(functional_bytes)
    if (functional_relation != relation or functional_syntax != syntax or
            compile_text(functional_bytes.decode("ascii"))[0] != relation):
        raise AssertionError("functional helper changed the direct relation")
    normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    gates, _, padded, emitted = exact_direct_gate_schedule(syntax)
    if padded != 512 or len(emitted) != 3 or [item["op"] for item in emitted] != [
            "add", "sub", "sub"]:
        raise AssertionError("ordered subtraction source schedule changed")
    uses = [0] * 4
    for instruction in syntax["instructions"]:
        uses[instruction["lhs"]] += 1
        uses[instruction["rhs"]] += 1
    uses[syntax["output"]] += 4
    counts = {kind: len(rows) for kind, rows in gates.items()}
    if counts != {"add": 474, "sub": 3, "mul": 27, "pointwise_mul": 8}:
        raise AssertionError("native group size is outside the reviewed profile")
    seen = {"add": 0, "sub": 0, "mul": 0}
    expected = []
    for instruction, gate in zip(syntax["instructions"], emitted, strict=True):
        op = instruction["op"]
        family = {"add": "add", "sub": "sub", "mul": "pointwise_mul"}[op]
        start = {"add": 3, "sub": counts["add"],
                 "mul": counts["add"] + counts["sub"] + counts["mul"]}[op]
        row = start + seen[op]
        seen[op] += 1
        actual_gate = {name: gate[name] for name in ("in0", "in1", "out")}
        slot = 3 + seen[op] - 1 if op == "add" else seen[op] - 1
        if gates[family][slot] != actual_gate or gate["id"] != instruction["id"]:
            raise AssertionError("independent gate list disagrees with source order")
        expected.append([row, int(op == "add"), int(op == "sub"), 0,
                         int(op == "mul"), gate["in0"], gate["in1"],
                         gate["out"], uses[instruction["id"]]])
    if (expected != [[3, 1, 0, 0, 0, 22, 22, 23, 1],
                     [474, 0, 1, 0, 0, 22, 23, 24, 1],
                     [475, 0, 1, 0, 0, 24, 22, 25, 4]]):
        raise AssertionError("ordered source rows differ from the reviewed cells")
    gitlink = subprocess.run(
        ["git", "rev-parse", "HEAD:deps/stwo-zig"], cwd=ROOT,
        capture_output=True, text=True, check=True).stdout.strip()
    identity = {
        "schema": "s31-ordered-subtraction-native-rows-v1",
        "source_sha256": sha(source_bytes),
        "functional_source_sha256": sha(functional_bytes),
        "normalized_sha256": sha(normalized),
        "canonical_ir_sha256": sha(canonical_ir_bytes(syntax)),
        "compiler_sha256": compiler_fingerprint(),
        "engine_gitlink": gitlink,
        "exporter_source_sha256": sha(EXPORTER.read_bytes()),
        "lowering_source_sha256": sha(LOWERING.read_bytes()),
        "group_counts": counts,
        "expected_source_rows": expected,
    }
    return identity, expected


def inspect_package(package: Path) -> dict:
    identity, expected = source_identity()
    check_package(package)
    manifest = json.loads((package / "manifest.json").read_bytes())
    key = json.loads((package / "verification-key.json").read_bytes())
    if (manifest.get("source_text_sha256") != identity["source_sha256"] or
            manifest.get("program_sha256") != identity["normalized_sha256"] or
            manifest.get("canonical_ir_sha256") != identity["canonical_ir_sha256"] or
            manifest.get("compiler_sha256") != identity["compiler_sha256"]):
        raise AssertionError("package is not bound to this source and compiler")
    prover = package / "bin/s31-release_sub4-prover"
    exported = json.loads(s31.invoke(str(prover), "inspect-topology"))
    packaged = json.loads((package / "gate-topology.json").read_bytes())
    if exported != packaged or exported.get("preprocessed_root") != key.get("preprocessed_root"):
        raise AssertionError("fresh topology differs from sealed package or key")
    columns = exported["columns"]
    if ([column.get("id") for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(column.get("values", [])) != 512 for column in columns)):
        raise AssertionError("native fixed-column shape changed")
    values = [word for column in columns for word in column["values"]]
    if any(type(word) is not int or not 0 <= word < P for word in values):
        raise AssertionError("noncanonical native fixed-column word")
    observed = [[row[0], *(column["values"][row[0]] for column in columns)]
                for row in expected]
    if observed != expected:
        raise AssertionError("native source fixed cells differ from source schedule")
    return {**identity,
            "native_source_rows": observed,
            "preprocessed_root": exported["preprocessed_root"],
            "exporter_binary_sha256": sha(prover.read_bytes()),
            "all_fixed_columns_sha256": sha(b"".join(
                struct.pack("<I", value) for value in values))}


def check_functional_package(manual_package: Path, functional_package: Path,
                             snapshot: dict) -> None:
    """A fresh static helper call must leave the native AIR unchanged."""
    check_package(functional_package)
    manifest = json.loads((functional_package / "manifest.json").read_bytes())
    key = json.loads((functional_package / "verification-key.json").read_bytes())
    if (manifest.get("source_text_sha256") != snapshot["functional_source_sha256"] or
            manifest.get("program_sha256") != snapshot["normalized_sha256"] or
            manifest.get("canonical_ir_sha256") != snapshot["canonical_ir_sha256"] or
            manifest.get("compiler_sha256") != snapshot["compiler_sha256"] or
            key.get("preprocessed_root") != snapshot["preprocessed_root"]):
        raise AssertionError("functional package changed the source-bound native key")
    manual_topology = json.loads((manual_package / "gate-topology.json").read_bytes())
    functional_topology = json.loads((functional_package / "gate-topology.json").read_bytes())
    prover = functional_package / "bin/s31-release_sub4-prover"
    if (json.loads(s31.invoke(str(prover), "inspect-topology")) != functional_topology or
            functional_topology.get("columns") != manual_topology.get("columns") or
            functional_topology.get("preprocessed_root") != snapshot["preprocessed_root"]):
        raise AssertionError("functional helper changed native fixed columns")
    manual_cost = json.loads((manual_package / "cost-report.json").read_bytes())
    functional_cost = json.loads((functional_package / "cost-report.json").read_bytes())
    if any(manual_cost.get(field) != functional_cost.get(field) for field in AIR_FIELDS):
        raise AssertionError("functional helper changed native AIR geometry")


def validate_snapshot(snapshot: dict) -> None:
    identity, expected = source_identity()
    for key, value in identity.items():
        if snapshot.get(key) != value:
            raise AssertionError(f"ordered subtraction snapshot {key} differs")
    if snapshot.get("native_source_rows") != expected:
        raise AssertionError("ordered subtraction native source cells differ")
    for key in ("preprocessed_root", "exporter_binary_sha256",
                "all_fixed_columns_sha256"):
        value = snapshot.get(key)
        if (not isinstance(value, str) or len(value) != 64 or
                any(digit not in "0123456789abcdef" for digit in value)):
            raise AssertionError(f"invalid ordered subtraction {key}")


def _cell_literal(row: list[int]) -> str:
    return "{ " + ", ".join(f"{name} := {value}" for name, value in
                           zip(FIELD_NAMES, row, strict=True)) + " }"


def render(snapshot: dict | None = None) -> str:
    if snapshot is None:
        snapshot = json.loads(SNAPSHOT.read_bytes())
    validate_snapshot(snapshot)
    native = ",\n  ".join(_cell_literal(row) for row in snapshot["native_source_rows"])
    changed = [row.copy() for row in snapshot["native_source_rows"]]
    changed[1][2] = 0  # erase the first subtraction selector
    mutant = ",\n  ".join(_cell_literal(row) for row in changed)
    return f'''import S31.Gadgets.Functional.Correspondence.OrderedSubtractionNativeRows

/-! Generated from the sealed native `release_sub4` topology by
`ordered_subtraction_native_fixture.py`. Selected fixed cells are compared
with the independent source schedule. A fresh native run also compares the
functional helper package's complete fixed columns and AIR geometry. The
fixed-column hash and key root are recorded below. This exported-artifact
check does not authenticate arbitrary proof openings. Do not edit directly. -/

namespace S31.Functional.Correspondence.GeneratedOrderedSubtractionNativeRows

open S31.Functional.SSAAirColumnCells
open S31.Functional.Correspondence.OrderedSubtractionNativeRows
open S31.Functional.Correspondence.GeneratedOrderedSubtractionRelease

-- Native preprocessed root: {snapshot['preprocessed_root']}
-- Full fixed-column SHA-256: {snapshot['all_fixed_columns_sha256']}
-- Native exporter binary SHA-256: {snapshot['exporter_binary_sha256']}

def nativeCells : List ColumnCell := [
  {native}
]

def changedSubSelectorCells : List ColumnCell := [
  {mutant}
]

theorem native_cells_match_source :
    nativeCells = expectedCells expectedParsed := by decide

theorem native_partition_is_512 :
    addRows expectedParsed + (1 + countOp expectedParsed.instructions .sub) +
      27 + (8 + countOp expectedParsed.instructions .mul) = 512 := by
  exact partition_count expectedParsed (by decide)

theorem changed_sub_selector_rejected :
    changedSubSelectorCells ≠ expectedCells expectedParsed := by decide

end S31.Functional.Correspondence.GeneratedOrderedSubtractionNativeRows
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build and inspect native package")
    parser.add_argument("--package", type=Path, help="inspect an existing package")
    parser.add_argument("--functional-package", type=Path,
                        help="compare an existing functional helper package")
    parser.add_argument("--write", action="store_true", help="write reviewed snapshot and Lean fixture")
    args = parser.parse_args()
    if args.write and not (args.native or args.package):
        parser.error("--write requires --native or --package")
    if args.native and args.package:
        parser.error("choose --native or --package")
    if args.functional_package and not args.package:
        parser.error("--functional-package requires --package")
    if args.write and args.package and not args.functional_package:
        parser.error("--write requires both packages or --native")
    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-ordered-sub-native-") as directory:
            package = s31.build(SOURCE, Path(directory) / "package", "direct-gate")
            snapshot = inspect_package(package)
            functional_package = s31.build(
                FUNCTIONAL_SOURCE, Path(directory) / "functional-package", "direct-gate")
            check_functional_package(package, functional_package, snapshot)
    elif args.package:
        package = args.package.resolve()
        snapshot = inspect_package(package)
        if args.functional_package:
            check_functional_package(package, args.functional_package.resolve(), snapshot)
    else:
        snapshot = json.loads(SNAPSHOT.read_bytes())
    if args.write:
        lean = render(snapshot)
        encoded = (json.dumps(snapshot, indent=2, sort_keys=True) + "\n").encode()
        SNAPSHOT.parent.mkdir(parents=True, exist_ok=True)
        SNAPSHOT.write_bytes(encoded)
        LEAN.write_text(lean)
        print(f"wrote {SNAPSHOT.relative_to(ROOT)} and {LEAN.relative_to(ROOT)}")
    else:
        committed = json.loads(SNAPSHOT.read_bytes())
        validate_snapshot(committed)
        # The executable contains OS-specific machine code. Compare every
        # semantic/source/fixed-root field across a fresh build, and retain
        # the recorded local binary hash only as provenance in the fixture.
        portable = lambda item: {key: value for key, value in item.items()
                                 if key != "exporter_binary_sha256"}
        if portable(snapshot) != portable(committed):
            raise AssertionError("fresh native ordered-subtraction cells or roots differ")
        lean = render(committed)
        encoded = (json.dumps(committed, indent=2, sort_keys=True) + "\n").encode()
        if SNAPSHOT.read_bytes() != encoded or LEAN.read_text() != lean:
            raise AssertionError("ordered subtraction native fixture is stale")
        print("checked ordered subtraction native source rows")


if __name__ == "__main__":
    main()
