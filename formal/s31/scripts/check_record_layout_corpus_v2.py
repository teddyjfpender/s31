#!/usr/bin/env python3
"""Pin 13 compiled ABI type trees to Lean's checked nested-layout walk.

The generated Lean cases check raw record/tuple tags, widths, and exact
declaration-order rooted paths. Existing native parser corpus checks the same
13 source programs separately; this script does not build Zig or authenticate
a native proof.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
S31 = ROOT / "src/frontends/s31"
CORPUS = S31 / "tests/acceptance/record_abi"
LEAN = ROOT / "formal/s31/S31/Gadgets/Functional/GeneratedRecordLayoutCorpusV2.lean"
sys.path.insert(0, str(CORPUS))
sys.path.insert(0, str(S31 / "python"))

from general_statement_refinement_v2 import sources  # noqa: E402
from lean_native_bridge_v2 import path_parts, walk  # noqa: E402
from text_frontend import compile_text  # noqa: E402

EXPECTED_SOURCE_SHA256 = "a5e2883c146957858828404f47afec1251a4c8b99929c0ed310bb56a04a2305c"


def choose(values: list[str]) -> str:
    if not values:
        raise ValueError("native ABI does not admit an empty node")
    if len(values) == 1:
        return f"(fun _ => ({values[0]}))"
    result = values[-1]
    for index in range(len(values) - 2, -1, -1):
        result = f"if index.val = {index} then ({values[index]}) else ({result})"
    return f"(fun index => {result})"


def tree_lean(tree: dict) -> str:
    if set(tree) == {"kind", "length"}:
        kind, width = tree["kind"], tree["length"]
        if kind not in {"m31", "bit"} or type(width) is not int:
            raise ValueError("unsupported leaf in compiled v2 ABI")
        return f"(.leaf .{kind} {width})"
    if set(tree) == {"record", "fields"}:
        fields = tree["fields"]
        names = [json.dumps(field["name"], ensure_ascii=True) for field in fields]
        children = [tree_lean(field["type"]) for field in fields]
        return f"(.record {len(fields)} {choose(names)} {choose(children)})"
    if set(tree) == {"tuple"}:
        children = [tree_lean(child) for child in tree["tuple"]]
        return f"(.tuple {len(children)} {choose(children)})"
    raise ValueError("unsupported compiled ABI tree shape")


def path_lean(path: tuple[tuple[str, str | int], ...]) -> str:
    parts = []
    for tag, value in path:
        encoded = json.dumps(value, ensure_ascii=True) if isinstance(value, str) else str(value)
        parts.append(f".{tag} {encoded}")
    return "[" + ", ".join(parts) + "]"


def list_lean(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


def checked_leaves(root: dict, label: str) -> list[tuple[tuple, str, int]]:
    expected = walk(root["type"], (("root", root["name"]),))
    actual = [(path_parts(leaf["path"]), leaf["kind"], leaf["length"])
              for leaf in root["leaves"]]
    if expected != actual:
        raise ValueError(f"{label}/{root['name']}: compiled leaves differ from independent tree walk")
    return expected


def negative_projection_checks(programs: list[tuple[str, str]]) -> int:
    """Ensure the independent descriptor comparison notices four local edits."""
    _, source_text = next(case for case in programs if case[0] == "tuple_2_2")
    relation, _ = compile_text(source_text)
    root = relation["public_abi"]["inputs"][0]
    variants = []
    changed = copy.deepcopy(root)
    changed["leaves"][0]["path"][-1]["tuple"] = 1
    variants.append(changed)
    changed = copy.deepcopy(root)
    changed["leaves"][0]["length"] += 1
    variants.append(changed)
    changed = copy.deepcopy(root)
    changed["leaves"][0]["kind"] = "bit"
    variants.append(changed)
    changed = copy.deepcopy(root)
    changed["leaves"].pop()
    variants.append(changed)
    for index, variant in enumerate(variants):
        try:
            checked_leaves(variant, f"mutant_{index}")
        except ValueError:
            continue
        raise AssertionError(f"independent layout projection accepted mutant {index}")
    return len(variants)


def render() -> tuple[str, dict[str, object]]:
    programs = sources()
    source_sha256 = hashlib.sha256("".join(text for _, text in programs).encode()).hexdigest()
    if source_sha256 != EXPECTED_SOURCE_SHA256:
        raise ValueError("the 13-layout source corpus changed; review the new source first")
    lines = [
        "import S31.Gadgets.Functional.RecordLayoutValidationV2",
        "",
        "/-! Generated from the 13-layout ABI source corpus. Default script mode checks",
        "exact bytes; --write explicitly regenerates after review. These cases check",
        "compiler-emitted type trees and leaves against the Lean raw layout walk.",
        "They do not model general JSON parsing or native proof authentication. -/",
        f"-- Source corpus SHA-256: {source_sha256}",
        "namespace S31.Functional.GeneratedRecordLayoutCorpusV2",
        "open RecordAbiV2 RecordLayoutValidationV2",
        "",
    ]
    root_count = 0
    for case_index, (label, source_text) in enumerate(programs):
        relation, _ = compile_text(source_text)
        abi = relation["public_abi"]
        roots = abi["inputs"] + [abi["result"]]
        for root_index, root in enumerate(roots):
            name = f"case{case_index}_{label}_root{root_index}"
            root_name = root["name"]
            expected = checked_leaves(root, label)
            tree = tree_lean(root["type"])
            quoted_root = json.dumps(root_name, ensure_ascii=True)
            paths = list_lean([path_lean(path) for path, _, _ in expected])
            widths = list_lean([str(width) for _, _, width in expected])
            lines += [
                f"-- {label}, root {root_name}: {len(expected)} declaration-order leaves.",
                f"def {name} : RawLayout := {tree}",
                f"theorem {name}_checked : checkNativeRoot {name} = true := by decide",
                f"theorem {name}_paths :",
                f"    ((orderedRootLeaves {quoted_root} (erase {name})",
                f"      (leafWidthAt {name})).map Prod.fst) = {paths} := by decide",
                f"theorem {name}_widths :",
                f"    ((orderedRootLeaves {quoted_root} (erase {name})",
                f"      (leafWidthAt {name})).map Prod.snd) = {widths} := by decide",
                "",
            ]
            root_count += 1
    lines += [
        "-- Adversarial raw trees exercise the executable validation premise.",
        "def duplicateFields : RawLayout :=",
        '  .record 2 (fun _ => "same") (fun _ => .leaf .m31 1)',
        "theorem duplicateFields_rejected : checkRoot duplicateFields = false := by decide",
        "def oversizedM31 : RawLayout := .leaf .m31 9",
        "theorem oversizedM31_rejected : checkRoot oversizedM31 = false := by decide",
        "def oversizedBit : RawLayout := .leaf .bit 2",
        "theorem oversizedBit_rejected : checkRoot oversizedBit = false := by decide",
        "def emptyTuple : RawLayout := .tuple 0 (fun _ => .leaf .m31 1)",
        "theorem emptyTuple_rejected : checkRoot emptyTuple = false := by decide",
        "def tupleRoot : RawLayout := .tuple 1 (fun _ => .leaf .m31 1)",
        "theorem tupleRoot_rejected : checkNativeRoot tupleRoot = false := by decide",
        "def emptyRecord : RawLayout :=",
        '  .record 0 (fun _ => "unreachable") (fun _ => .leaf .m31 1)',
        "theorem emptyRecord_rejected : checkRoot emptyRecord = false := by decide",
        "def tooWideNode : RawLayout := .tuple 65 (fun _ => .leaf .m31 1)",
        "theorem tooWideNode_rejected : checkRoot tooWideNode = false := by decide",
        "def tooDeep : Nat → RawLayout",
        "  | 0 => .leaf .m31 1",
        "  | n + 1 => .tuple 1 (fun _ => tooDeep n)",
        "theorem tooDeep_rejected : checkRoot (tooDeep 33) = false := by decide",
        "",
        "end S31.Functional.GeneratedRecordLayoutCorpusV2",
        "",
    ]
    return "\n".join(lines), {
        "schema": "s31-record-layout-validation-corpus-v2",
        "source_sha256": source_sha256,
        "programs": len(programs),
        "checked_roots": root_count,
        "adversarial_layouts": 8,
        "rejected_descriptor_mutations": negative_projection_checks(programs),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate checked-in Lean corpus")
    args = parser.parse_args()
    rendered, report = render()
    if args.write:
        LEAN.write_text(rendered)
    elif not LEAN.is_file() or LEAN.read_text() != rendered:
        raise ValueError("compiled ABI trees differ from pinned Lean corpus; review before --write")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
