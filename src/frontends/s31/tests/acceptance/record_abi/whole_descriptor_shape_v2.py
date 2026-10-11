#!/usr/bin/env python3
"""Source-derived whole-descriptor shape differential against native Zig.

The independent model mirrors the *shape fragment* of Lean's
RecordDescriptorValidationV2.checkDescriptor. It deliberately does not inspect
serialized leaf paths, wires, JSON spelling, or the relation. Gap controls
demonstrate that those extra native obligations remain separate.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

from general_statement_refinement_v2 import sources
from nested_alias_v2 import S31, SOURCE, canonical

import sys
sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import validate_binding  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402

EXPECTED_CORPUS_SHA256 = "a1f2fef313d2e3f81f69a854b0978a07065f098c71ba0adc4e711e1c637c827c"


def layout(tree: object, depth: int, nominals: dict[str, tuple]) -> tuple[int, bool, tuple]:
    """Return leaf count, presence of a bit, and an arity-delimited type code."""
    if depth > 32 or type(tree) is not dict:
        raise ValueError("depth or node")
    if set(tree) == {"kind", "length"}:
        kind, width = tree["kind"], tree["length"]
        if (type(width) is not int or
                not ((kind == "m31" and 1 <= width <= 8) or
                     (kind == "bit" and width == 1))):
            raise ValueError("leaf kind or width")
        return 1, kind == "bit", ("leaf", kind, width)
    if set(tree) == {"tuple"}:
        children = tree["tuple"]
        if type(children) is not list or not 1 <= len(children) <= 64:
            raise ValueError("tuple arity")
        checked = [layout(child, depth + 1, nominals) for child in children]
        return (sum(item[0] for item in checked), any(item[1] for item in checked),
                ("tuple", len(children), tuple(item[2] for item in checked)))
    if set(tree) != {"record", "fields"}:
        raise ValueError("record tag")
    name, fields = tree["record"], tree["fields"]
    if type(name) is not str or type(fields) is not list or not 1 <= len(fields) <= 64:
        raise ValueError("record arity")
    names = []
    checked = []
    for item in fields:
        if type(item) is not dict or set(item) != {"name", "type"} or type(item["name"]) is not str:
            raise ValueError("field")
        names.append(item["name"])
        checked.append(layout(item["type"], depth + 1, nominals))
    if len(set(names)) != len(names):
        raise ValueError("duplicate sibling fields")
    code = ("record", name, len(fields), tuple((field, child[2])
                                               for field, child in zip(names, checked)))
    if name in nominals and nominals[name] != code:
        raise ValueError("nominal type disagreement")
    nominals[name] = code
    return sum(item[0] for item in checked), any(item[1] for item in checked), code


def shape_accepts(binding: object) -> bool:
    """The executable Lean descriptor check, excluding its parsed-tree premise."""
    try:
        inputs, result = binding["inputs"], binding["result"]
        if type(inputs) is not list or type(result) is not dict:
            return False
        nominals: dict[str, tuple] = {}
        names = []
        count = 0
        has_record_root = False
        for root in inputs:
            tree = root["type"]
            if type(tree) is not dict or "tuple" in tree or root["visibility"] not in ("public", "private"):
                return False
            count_root, has_bit, _ = layout(tree, 0, nominals)
            if count_root > 1024 or (root["visibility"] == "private" and has_bit):
                return False
            count += count_root
            names.append(root["name"])
            has_record_root |= "record" in tree
        result_tree = result["type"]
        if type(result_tree) is not dict or "tuple" in result_tree:
            return False
        result_count, _, _ = layout(result_tree, 0, nominals)
        count += result_count
        has_record_root |= "record" in result_tree
        return (len(set(names)) == len(names) and result["name"] == "result" and
                "result" not in names and count <= 1024 and has_record_root)
    except (KeyError, TypeError, ValueError):
        return False


@dataclass(frozen=True)
class Case:
    label: str
    source: dict
    shape_valid: bool
    native_valid: bool


def _compiled(label: str, text: str) -> Case:
    source, _ = compile_text(text)
    return Case(label, source, True, True)


def _changed(base: dict, label: str, mutate, *, shape_valid: bool,
             native_valid: bool = False) -> Case:
    source = copy.deepcopy(base)
    mutate(source)
    return Case(label, source, shape_valid, native_valid)


def _budget_source(inputs: int) -> dict:
    source, _ = compile_text("struct R { x: [m31; 1] }\n"
                             "circuit f(private a: [m31; 1]) -> public R { R { x: a } }\n")
    first_root = source["public_abi"]["inputs"][0]
    first_input = source["inputs"][0]
    for index in range(1, inputs):
        wire = f"p_{index:04d}"
        root = copy.deepcopy(first_root)
        root["name"] = wire
        root["leaves"][0]["path"] = [{"root": wire}]
        root["leaves"][0]["wire"] = wire
        source["public_abi"]["inputs"].append(root)
        item = copy.deepcopy(first_input)
        item["name"] = wire
        source["inputs"].append(item)
    return source


def cases() -> list[Case]:
    result = [_compiled(label, text) for label, text in sources()]
    nested = _compiled("nested_alias", SOURCE)
    result.append(nested)
    base = nested.source

    def change_nominal(source: dict) -> None:
        child = source["public_abi"]["result"]["type"]["fields"][0]["type"]["tuple"][0]
        child["fields"][0]["name"] = "different"
        source["public_abi"]["result"]["leaves"][0]["path"][-1] = {"field": "different"}

    def change_private_bit(source: dict) -> None:
        root = source["public_abi"]["inputs"][1]
        root["type"]["fields"][0]["type"]["kind"] = "bit"
        root["leaves"][0]["kind"] = "bit"

    def duplicate_root(source: dict) -> None:
        root = source["public_abi"]["inputs"][1]
        root["name"] = "req"
        root["leaves"][0]["path"][0] = {"root": "req"}

    def result_collision(source: dict) -> None:
        root = source["public_abi"]["inputs"][0]
        root["name"] = "result"
        for leaf in root["leaves"]:
            leaf["path"][0] = {"root": "result"}

    def wrong_result_name(source: dict) -> None:
        root = source["public_abi"]["result"]
        root["name"] = "other"
        for leaf in root["leaves"]:
            leaf["path"][0] = {"root": "other"}

    def tuple_root(source: dict) -> None:
        root = source["public_abi"]["result"]
        root["type"] = {"tuple": [root["type"]]}
        for leaf in root["leaves"]:
            leaf["path"].insert(1, {"tuple": 0})

    def depth_33(source: dict) -> None:
        root = source["public_abi"]["inputs"][1]
        child = root["type"]["fields"][0]
        tree = child["type"]
        for _ in range(33):
            tree = {"tuple": [tree]}
        child["type"] = tree
        root["leaves"][0]["path"][2:2] = [{"tuple": 0}] * 33

    shape_negatives = [
        ("nominal_mismatch", change_nominal),
        ("private_bit", change_private_bit),
        ("duplicate_input_root", duplicate_root),
        ("result_root_collision", result_collision),
        ("wrong_result_name", wrong_result_name),
        ("tuple_root", tuple_root),
        ("depth_33", depth_33),
        ("empty_record", lambda source: source["public_abi"]["inputs"][0]["type"].__setitem__("fields", [])),
        ("empty_tuple", lambda source: source["public_abi"]["inputs"][0]["type"]["fields"][0]["type"].__setitem__("tuple", [])),
        ("duplicate_sibling_field", lambda source: source["public_abi"]["inputs"][0]["type"]["fields"][1].__setitem__("name", "pair")),
        ("m31_width_9", lambda source: source["public_abi"]["inputs"][0]["type"]["fields"][0]["type"]["tuple"][0].__setitem__("length", 9)),
        ("bit_width_2", lambda source: source["public_abi"]["inputs"][0]["type"]["fields"][0]["type"]["tuple"][0].update({"kind": "bit", "length": 2})),
    ]
    result.extend(_changed(base, label, mutate, shape_valid=False)
                  for label, mutate in shape_negatives)
    simple = _budget_source(1)
    def remove_boundary(source: dict) -> None:
        root = source["public_abi"]["result"]
        root["type"] = {"kind": "m31", "length": 1}
        root["leaves"][0]["path"] = [{"root": "result"}]
    result.append(_changed(simple, "no_record_boundary", remove_boundary, shape_valid=False))
    boundary = _budget_source(1023)
    result.append(Case("exactly_1024_leaves", boundary, True, True))
    result.append(Case("over_1024_leaves", _budget_source(1024), False, False))

    # These are intentional refinement gaps: the Lean shape model accepts
    # their type trees, while native checks path/wire/identifier obligations.
    result.extend([
        _changed(base, "bad_leaf_path_gap", lambda source: source["public_abi"]["inputs"][0]["leaves"][0]["path"][-1].__setitem__("tuple", 7), shape_valid=True),
        _changed(base, "bad_wire_gap", lambda source: source["public_abi"]["inputs"][0]["leaves"][0].__setitem__("wire", "wrong_wire"), shape_valid=True),
        _changed(base, "bad_identifier_gap", lambda source: source["public_abi"]["result"]["type"].__setitem__("record", "Bad!"), shape_valid=True),
    ])
    return result


def checked_cases() -> tuple[list[Case], bytes, str]:
    corpus = cases()
    if len({case.label for case in corpus}) != len(corpus):
        raise AssertionError("duplicate case label")
    for case in corpus:
        shape = shape_accepts(case.source["public_abi"])
        if shape != case.shape_valid:
            raise AssertionError(f"shape model disagrees with expected {case.label}: {shape}")
        # The Python relation oracle validates the erased v1 relation; the
        # public ABI is a separate v2 envelope in this reference API.
        relation = {**case.source, "version": 1}
        binding = relation.pop("public_abi")
        try:
            validate_binding(relation, binding)
        except AbiError:
            python_valid = False
        else:
            python_valid = True
        if python_valid != case.native_valid:
            raise AssertionError(f"Python full validator disagrees with expected {case.label}: {python_valid}")
    encoded = canonical({"schema": "s31-record-descriptor-native-corpus-v2",
                         "cases": [{"label": case.label,
                                    "source": canonical(case.source).decode("ascii"),
                                    "expected_valid": case.native_valid}
                                   for case in corpus]})
    digest = hashlib.sha256(encoded).hexdigest()
    if digest != EXPECTED_CORPUS_SHA256:
        raise AssertionError(f"descriptor corpus bytes changed: {digest}; review and repin")
    return corpus, encoded, digest


def _lean_layout(tree: dict) -> str:
    if "kind" in tree:
        return f"NamedLayout.leaf .{tree['kind']} {tree['length']}"
    if "tuple" in tree:
        children = tree["tuple"]
        values = ", ".join(_lean_layout(child) for child in children)
        return (f"NamedLayout.tuple {len(children)} "
                f"(fun i => ([{values}] : List NamedLayout).get i)")
    fields = tree["fields"]
    names = ", ".join(json.dumps(field["name"]) for field in fields)
    values = ", ".join(_lean_layout(field["type"]) for field in fields)
    return (f"NamedLayout.record {json.dumps(tree['record'])} {len(fields)} "
            f"(fun i => ([{names}] : List String).get i) "
            f"(fun i => ([{values}] : List NamedLayout).get i)")


def _lean_descriptor(binding: dict) -> str:
    inputs = ",\n      ".join(
        "{ name := " + json.dumps(root["name"]) + ", visibility := ." +
        ("pub" if root["visibility"] == "public" else "priv") +
        ", layout := " + _lean_layout(root["type"]) + " }"
        for root in binding["inputs"])
    result = binding["result"]
    return ("{ inputs := [" + inputs + "]\n"
            "    result := { name := " + json.dumps(result["name"]) +
            ", layout := " + _lean_layout(result["type"]) + " } }")


def lean_checks(corpus: list[Case]) -> int:
    """Kernel-check concrete descriptor claims, excluding the huge synthetic bound."""
    formal = S31.parents[2] / "formal/s31"
    checked = [case for case in corpus if case.label not in
               {"exactly_1024_leaves", "over_1024_leaves"}]
    lines = ["import S31.Gadgets.Functional.RecordDescriptorValidationV2",
             "open S31.Functional.RecordDescriptorValidationV2", ""]
    for index, case in enumerate(checked):
        lines.extend((f"-- {case.label}",
                      f"def descriptorCase{index} : Descriptor :=",
                      "  " + _lean_descriptor(case.source["public_abi"]),
                      f"theorem descriptorCase{index}_checked :",
                      f"    checkDescriptor descriptorCase{index} = " +
                      ("true" if case.shape_valid else "false") + " := by decide", ""))
    with tempfile.TemporaryDirectory(prefix="s31-record-descriptor-lean-") as temp:
        path = Path(temp) / "DescriptorCases.lean"
        path.write_text("\n".join(lines))
        run = subprocess.run(("lake", "env", "lean", str(path)), cwd=formal,
                             capture_output=True, text=True, timeout=120)
        if run.returncode:
            raise AssertionError("Lean descriptor fixture failed:\n" +
                                 (run.stdout + run.stderr)[:3000])
    return len(checked)


def native_checks(encoded: bytes, expected_accepted: int, expected_rejected: int) -> dict:
    with tempfile.TemporaryDirectory(prefix="s31-record-descriptor-") as temp:
        path = Path(temp) / "corpus.json"
        path.write_bytes(encoded)
        command = ["zig", "build", "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast",
                   "-j1", "--", str(path)]
        run = subprocess.run(command, cwd=S31, capture_output=True, text=True, timeout=180)
        if run.returncode:
            raise AssertionError(f"native descriptor corpus failed:\n{run.stdout}\n{run.stderr}")
        output = json.loads(run.stdout.strip().splitlines()[-1])
        if output != {"accepted": expected_accepted, "rejected": expected_rejected}:
            raise AssertionError(f"native counts differ: {output}")
        return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static", action="store_true", help="skip the Zig parser run")
    parser.add_argument("--lean", action="store_true", help="also kernel-check generated Lean case theorems")
    args = parser.parse_args()
    corpus, encoded, digest = checked_cases()
    accepted = sum(case.native_valid for case in corpus)
    rejected = len(corpus) - accepted
    result = {"schema": "s31-whole-record-descriptor-shape-differential-v2",
              "corpus_sha256": digest, "source_derived_programs": len(sources()) + 1,
              "synthetic_leaf_boundary_cases": 2,
              "shape_negative_cases": sum(not case.shape_valid for case in corpus),
              "intentional_shape_refinement_gaps": sum(case.shape_valid and not case.native_valid for case in corpus),
              "python_full_validator": {"accepted": accepted, "rejected": rejected}}
    if not args.static:
        result["native_record_validator"] = native_checks(encoded, accepted, rejected)
    if args.lean:
        result["lean_kernel_checked_cases"] = lean_checks(corpus)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
