#!/usr/bin/env python3
"""Check one compiled v2 record statement against a concrete Lean contract.

The independent walk below follows the native validator's declared-order
record/tuple traversal and wire projection. It deliberately does not call the
Python ABI statement decoder to compute expected paths or proof words.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

from nested_alias_v2 import S31, static_checks

LEAN = S31.parents[2] / "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
START = "-- BEGIN GENERATED NATIVE ALIAS V2 CONTRACT"
END = "-- END GENERATED NATIVE ALIAS V2 CONTRACT"


class ContractError(ValueError):
    pass


def walk(tree: dict, path: tuple[tuple[str, str | int], ...]) -> list[tuple[tuple, str, int]]:
    """Model the native typeTree visit order without reading ABI leaf paths."""
    if "kind" in tree:
        return [(path, tree["kind"], tree["length"])]
    if "record" in tree:
        return [leaf for field in tree["fields"]
                for leaf in walk(field["type"], path + (("field", field["name"]),))]
    return [leaf for index, child in enumerate(tree["tuple"])
            for leaf in walk(child, path + (("tuple", index),))]


def path_parts(value: object) -> tuple[tuple[str, str | int], ...]:
    if type(value) is not list:
        raise ContractError("leaf path must be an array")
    parts = []
    for segment in value:
        if type(segment) is not dict or len(segment) != 1:
            raise ContractError("path segment must have exactly one tag")
        tag, item = next(iter(segment.items()))
        if (tag in ("root", "field") and type(item) is str) or (tag == "tuple" and type(item) is int):
            parts.append((tag, item))
        else:
            raise ContractError("path segment tag or type differs")
    return tuple(parts)


def projection(source: dict, statement: dict) -> tuple[list[tuple], list[tuple], list[int], list[int]]:
    """Project declared leaf claims to distinct public relation wires."""
    boundary = source["public_abi"]
    expected: list[tuple[tuple, str, int, str, bool]] = []
    input_paths: list[tuple] = []
    result_paths: list[tuple] = []
    input_wires: list[str] = []
    for root in boundary["inputs"]:
        visited = walk(root["type"], (("root", root["name"]),))
        declared = root["leaves"]
        if len(visited) != len(declared):
            raise ContractError("input leaf count differs from type walk")
        for (path, kind, width), leaf in zip(visited, declared):
            if (path_parts(leaf["path"]) != path or leaf["kind"] != kind or
                    leaf["length"] != width):
                raise ContractError("input descriptor differs from type walk")
            input_wires.append(leaf["wire"])
            if root["visibility"] == "public":
                input_paths.append(path)
                expected.append((path, kind, width, leaf["wire"], True))
    if input_wires != [item["name"] for item in source["inputs"]]:
        raise ContractError("input wire order differs from relation")
    root = boundary["result"]
    visited = walk(root["type"], (("root", root["name"]),))
    if len(visited) != len(root["leaves"]):
        raise ContractError("result leaf count differs from type walk")
    output_wires: list[str] = []
    for (path, kind, width), leaf in zip(visited, root["leaves"]):
        if (path_parts(leaf["path"]) != path or leaf["kind"] != kind or
                leaf["length"] != width):
            raise ContractError("result descriptor differs from type walk")
        result_paths.append(path)
        expected.append((path, kind, width, leaf["wire"], False))
        if leaf["wire"] not in output_wires:
            output_wires.append(leaf["wire"])
    if output_wires != source["public_outputs"]:
        raise ContractError("distinct result wire order differs from relation")
    claims = statement["leaves"]
    if len(claims) != len(expected):
        raise ContractError("statement leaf count differs")
    wire_values: dict[str, list[int]] = {}
    claim_words: list[int] = []
    for claim, (path, kind, width, wire, _) in zip(claims, expected):
        if type(claim) is not dict or set(claim) != {"path", "words"} or path_parts(claim["path"]) != path:
            raise ContractError("statement path differs from type walk")
        words = claim["words"]
        limit = 2 if kind == "bit" else 2**31 - 1
        if (type(words) is not list or len(words) != width or
                any(type(word) is not int or not 0 <= word < limit for word in words)):
            raise ContractError("statement leaf width or range differs")
        if wire in wire_values and wire_values[wire] != words:
            raise ContractError("aliased claims disagree")
        wire_values[wire] = words
        claim_words.extend(words)
    public_words = [word for item in source["inputs"] if item["visibility"] == "public"
                    for word in wire_values[item["name"]]]
    public_words.extend(word for wire in source["public_outputs"] for word in wire_values[wire])
    if not 1 <= len(public_words) <= 8:
        raise ContractError("native direct-Gate word budget differs")
    return input_paths, result_paths, claim_words, public_words + [0] * (8 - len(public_words))


def lean_path(path: tuple[tuple[str, str | int], ...]) -> str:
    return "[" + ", ".join(f".{tag} {json.dumps(item)}" for tag, item in path) + "]"


def lean_list(items: list) -> str:
    return "[" + ", ".join(str(item) for item in items) + "]"


def contract(source: dict, statement: dict) -> str:
    inputs, result, claims, proof = projection(source, statement)
    return "\n".join((
        START,
        "def nativeAliasInputPaths : List (List Segment) :=",
        "  [" + ", ".join(map(lean_path, inputs)) + "]",
        "def nativeAliasResultPaths : List (List Segment) :=",
        "  [" + ", ".join(map(lean_path, result)) + "]",
        f"def nativeAliasClaimWords : List Nat := {lean_list(claims)}",
        f"def nativeAliasProofWords : List Nat := {lean_list(proof)}",
        END,
    ))


def assert_rejected(source: dict, statement: dict, label: str) -> None:
    try:
        projection(source, statement)
    except ContractError:
        return
    raise AssertionError(f"independent projection accepted {label}")


def check() -> dict:
    source, _, encoded, _, _, _ = static_checks()
    statement = json.loads(encoded)
    generated = contract(source, statement)
    formal = LEAN.read_text()
    if formal.count(START) != 1 or formal.count(END) != 1:
        raise AssertionError("Lean contract markers missing or duplicated")
    start = formal.index(START)
    end = formal.index(END, start) + len(END)
    if formal[start:end] != generated:
        raise AssertionError("compiled source, statement and checked-in Lean contract diverge; use --emit")
    variants = {}
    changed = copy.deepcopy(statement)
    changed["leaves"][0], changed["leaves"][1] = changed["leaves"][1], changed["leaves"][0]
    variants["input_order"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"][4]["path"][-1] = {"tuple": 0}
    variants["tuple_index"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"][5]["words"] = [18]
    variants["split_result_alias"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"][4]["words"] = [3]
    variants["split_input_alias"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"].insert(3, {"path": [{"root": "mask"}, {"field": "delta"}], "words": [7]})
    variants["private_leaf_leak"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"][3]["words"] = [2**31 - 1]
    variants["noncanonical_m31"] = (source, changed)
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["path"][-1] = {"tuple": True}
    variants["boolean_tuple_index"] = (source, changed)
    changed_source = copy.deepcopy(source)
    changed_source["public_outputs"].reverse()
    variants["output_wire_order"] = (changed_source, statement)
    for label, (case_source, case_statement) in variants.items():
        assert_rejected(case_source, case_statement, label)
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["words"] = [4]
    changed["leaves"][4]["words"] = [4]
    if projection(source, changed)[3] != [4, 3, 5, 17, 4, 0, 0, 0]:
        raise AssertionError("consistent changed alias failed to update proof words")
    return {"schema": "s31-record-abi-lean-native-bridge-v2",
            "public_claim_leaves": len(statement["leaves"]),
            "public_proof_words": projection(source, statement)[3],
            "negative_controls": sorted(variants),
            "consistent_changed_alias_updates_proof_words": True,
            "lean_contract_matches_compiled_source": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true",
                        help="print the exact Lean contract generated from the source fixture")
    args = parser.parse_args()
    if args.emit:
        source, _, encoded, _, _, _ = static_checks()
        print(contract(source, json.loads(encoded)))
    else:
        print(json.dumps(check(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
