#!/usr/bin/env python3
"""Check typed-tree erasure against the exact source, relation, and ABI bytes.

Generated cases exercise the admitted M31 grammar. They are differential
controls, not a universal proof that the Python and Lean parsers agree.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import abi  # noqa: E402
from package.source_relation_fragment import (  # noqa: E402
    make_source_relation_certificate, parse_enrolled_source_fragment,
)
from package.structural_derivation import (  # noqa: E402
    derive_relation, make_certificate,
)
from text_frontend import compile_text  # noqa: E402

CHECKER = FORMAL / ".lake/build/bin/s31-general-linear-structural-check"
SOURCE_CHECKER = FORMAL / "S31/Audit/GeneralLinearSSAStructuralDerivationCheck.lean"


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def source(kind: str, lanes: int) -> bytes:
    signature = (f"circuit c(public x: [m31; {lanes}], "
                 f"private y: [m31; {lanes}]) -> public [m31; {lanes}] {{\n")
    if kind == "tuple":
        body = "let p = (x, y); let a = p.0; let b = p.1; let z = a - b; z"
        prefix = ""
    elif kind == "helper_tuple":
        prefix = (f"fn sub(a: [m31; {lanes}], b: [m31; {lanes}]) "
                  f"-> [m31; {lanes}] {{ a - b }}\n")
        body = "let p = (x, y); let a = p.0; let b = p.1; let z = sub(a, b); z"
    elif kind == "constant":
        prefix = ""
        body = f"let z = x + splat<{lanes}>(7_m31); assert_eq(z, y); z"
    elif kind == "helpers":
        prefix = (f"fn sub(a: [m31; {lanes}], b: [m31; {lanes}]) "
                  f"-> [m31; {lanes}] {{ a - b }}\n"
                  f"fn square(a: [m31; {lanes}]) -> [m31; {lanes}] {{ a .* a }}\n")
        body = "let a = sub(x, y); let z = square(a); assert_eq(x, x); z"
    else:
        raise AssertionError(kind)
    return (prefix + signature + "  " + body + "\n}\n").encode()


def artifacts(data: bytes) -> dict[str, bytes]:
    relation, _ = compile_text(data.decode())
    if parse_enrolled_source_fragment(data) != relation:
        raise AssertionError("independent Python source parser disagrees with compiler")
    relation_bytes = canonical(relation)
    abi_bytes = canonical(abi(relation, "direct-gate"))
    tree = make_certificate(data, relation_bytes, abi_bytes, "direct-gate")
    source_cert = make_source_relation_certificate(data, relation_bytes)
    return {"source": data, "tree": canonical(tree),
            "certificate": canonical(source_cert), "relation": relation_bytes,
            "abi": abi_bytes}


def check(work: Path, items: dict[str, bytes], accepted: bool) -> None:
    names = ("source", "tree", "certificate", "relation", "abi")
    paths = []
    for name in names:
        path = work / name
        path.write_bytes(items[name])
        paths.append(str(path))
    command = ([str(CHECKER)] if CHECKER.is_file() else
               ["lake", "env", "lean", "--run", str(SOURCE_CHECKER)])
    result = subprocess.run([*command, *paths], cwd=FORMAL, capture_output=True,
                            text=True, check=False, timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"accepted={result.returncode == 0}, expected={accepted}: "
                             f"{result.stdout} {result.stderr}")


def check_statement(work: Path, items: dict[str, bytes], assignment: bytes,
                    statement: bytes, accepted: bool) -> None:
    names = ("source", "tree", "certificate", "relation", "abi")
    paths = []
    for name in names:
        path = work / name
        path.write_bytes(items[name])
        paths.append(str(path))
    assignment_path, statement_path = work / "assignment", work / "statement"
    assignment_path.write_bytes(assignment)
    statement_path.write_bytes(statement)
    command = ([str(CHECKER)] if CHECKER.is_file() else
               ["lake", "env", "lean", "--run", str(SOURCE_CHECKER)])
    result = subprocess.run([*command, "statement", *paths,
                             str(assignment_path), str(statement_path)],
                            cwd=FORMAL, capture_output=True, text=True,
                            check=False, timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"statement accepted={result.returncode == 0}, "
                             f"expected={accepted}: {result.stdout} {result.stderr}")


def assignment_for(kind: str, lanes: int, relation: dict) -> tuple[bytes, bytes]:
    x = [7 + index for index in range(lanes)]
    y = ([value + 7 for value in x] if kind == "constant" else
         [3 + index for index in range(lanes)])
    difference = [(left - right) % (2**31 - 1) for left, right in zip(x, y)]
    output = ([value + 7 for value in x] if kind == "constant" else
              [value * value % (2**31 - 1) for value in difference]
              if kind == "helpers" else difference)
    name = relation["public_outputs"][0]
    public = {"public_inputs": {"x": x}, "public_outputs": {name: output}}
    return canonical({**public, "private_inputs": {"y": y}}), canonical(public)


def expected_native_nodes(kind: str, assignment: dict) -> list[dict]:
    """Calculate every arithmetic node from the four handwritten bodies."""
    x = assignment["public_inputs"]["x"]
    y = assignment["private_inputs"]["y"]
    if kind == "constant":
        return [{"id": 2, "words": [(value + 7) % (2**31 - 1) for value in x]}]
    difference = [(a - b) % (2**31 - 1) for a, b in zip(x, y, strict=True)]
    nodes = [{"id": 2, "words": difference}]
    if kind == "helpers":
        nodes.append({"id": 3, "words": [value * value % (2**31 - 1)
                                           for value in difference]})
    return nodes


def boundary_assignment_for(kind: str, relation: dict) -> tuple[bytes, bytes]:
    """Two-lane M31 reduction case, including wrapped subtraction/constant."""
    modulus = 2**31 - 1
    x = [modulus - 1, modulus - 2]
    y = ([(value + 7) % modulus for value in x] if kind == "constant"
         else [1, 2])
    difference = [(a - b) % modulus for a, b in zip(x, y, strict=True)]
    output = (y if kind == "constant" else
              [value * value % modulus for value in difference]
              if kind == "helpers" else difference)
    public = {"public_inputs": {"x": x},
              "public_outputs": {relation["public_outputs"][0]: output}}
    return canonical({**public, "private_inputs": {"y": y}}), canonical(public)


def check_native(work: Path, cases: list[dict]) -> None:
    corpus = {"schema": "s31-structural-m31-native-witness-corpus-v1", "cases": cases}
    path = work / "native-corpus.json"

    def run(payload: dict) -> subprocess.CompletedProcess[str]:
        path.write_bytes(canonical(payload))
        return subprocess.run([
            "zig", "build", "--build-file", str(ROOT / "src/frontends/s31/build.zig"),
            "structural-native-witness-corpus", "-j1", "--", str(path),
        ], cwd=ROOT, capture_output=True, text=True, check=False, timeout=240)

    result = run(corpus)
    if result.returncode != 0:
        raise AssertionError(f"native structural witness corpus failed: {result.stderr[-6000:]}")
    if json.loads(result.stdout) != {"checked": len(cases)}:
        raise AssertionError(f"native structural witness count differs: {result.stdout}")
    forged = copy.deepcopy(corpus)
    forged["cases"][0]["expected_nodes"][0]["words"][0] ^= 1
    result = run(forged)
    if result.returncode == 0 or "compiled node value differs" not in result.stderr:
        raise AssertionError("native source-value corruption control was not rejected")
    print(f"native structural witness: {len(cases)} cases checked; resealed node-value control rejected")


def reseal(tree: dict, original: dict[str, bytes]) -> dict[str, bytes]:
    """Recompute every untrusted relation/ABI digest after a wrong erasure."""
    relation = derive_relation(tree["program"])
    relation_bytes = canonical(relation)
    abi_bytes = canonical(abi(relation, "direct-gate"))
    tree["relation_sha256"] = hashlib.sha256(relation_bytes).hexdigest()
    tree["public_abi_sha256"] = hashlib.sha256(abi_bytes).hexdigest()
    certificate = json.loads(original["certificate"])
    certificate["relation_sha256"] = tree["relation_sha256"]
    return {**original, "tree": canonical(tree), "relation": relation_bytes,
            "abi": abi_bytes, "certificate": canonical(certificate)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true",
                        help="also check every bounded source node against native direct Gate witness wires")
    args = parser.parse_args()
    accepted = 0
    rejected = 0
    native_cases: list[dict] = []
    with tempfile.TemporaryDirectory(prefix="s31-structural-lean-") as temp:
        work = Path(temp)
        for kind in ("tuple", "helper_tuple", "constant", "helpers"):
            for lanes in (1, 2, 3):
                honest = artifacts(source(kind, lanes))
                check(work, honest, True)
                accepted += 1
                relation = json.loads(honest["relation"])
                assignment, statement = assignment_for(kind, lanes, relation)
                check_statement(work, honest, assignment, statement, True)
                accepted += 1
                if args.native:
                    decoded_assignment = json.loads(assignment)
                    expected_nodes = expected_native_nodes(kind, decoded_assignment)
                    base_case = {"label": f"{kind}-{lanes}-honest",
                                 "relation": honest["relation"].decode(),
                                 "assignment": assignment.decode(),
                                 "expected_nodes": expected_nodes, "expected_valid": True,
                                 "expected_circuit_valid": True,
                                 "expected_public_match": True}
                    native_cases.append(base_case)
                    wrong_claim = copy.deepcopy(decoded_assignment)
                    output_name = relation["public_outputs"][0]
                    wrong_claim["public_outputs"][output_name][0] = (
                        wrong_claim["public_outputs"][output_name][0] + 1) % (2**31 - 1)
                    native_cases.append({**base_case, "label": f"{kind}-{lanes}-wrong-claim",
                                         "assignment": canonical(wrong_claim).decode(),
                                         "expected_valid": False,
                                         "expected_public_match": False})
                    if lanes == 2:
                        wrong_private = copy.deepcopy(decoded_assignment)
                        wrong_private["private_inputs"]["y"][0] = (
                            wrong_private["private_inputs"]["y"][0] + 1) % (2**31 - 1)
                        native_cases.append({**base_case,
                                             "label": f"{kind}-{lanes}-wrong-private",
                                             "assignment": canonical(wrong_private).decode(),
                                             "expected_nodes": expected_native_nodes(kind, wrong_private),
                                             "expected_valid": False,
                                             "expected_circuit_valid": kind != "constant",
                                             "expected_public_match": kind == "constant"})
                        boundary_assignment, boundary_statement = boundary_assignment_for(
                            kind, relation)
                        check_statement(work, honest, boundary_assignment,
                                        boundary_statement, True)
                        accepted += 1
                        native_cases.append({**base_case,
                                             "label": f"{kind}-{lanes}-boundary",
                                             "assignment": boundary_assignment.decode(),
                                             "expected_nodes": expected_native_nodes(
                                                 kind, json.loads(boundary_assignment))})
                if lanes != 2:
                    continue
                changed_statement = json.loads(statement)
                output_name = relation["public_outputs"][0]
                changed_statement["public_outputs"][output_name][0] += 1
                check_statement(work, honest, assignment,
                                canonical(changed_statement), False)
                rejected += 1
                changed_assignment = json.loads(assignment)
                changed_assignment["private_inputs"]["y"][0] += 1
                check_statement(work, honest,
                                canonical(changed_assignment), statement, False)
                rejected += 1
                # Change the tree and re-seal its relation and ABI where
                # possible. The unchanged source must still win.
                tree = json.loads(honest["tree"])
                if kind in ("tuple", "helper_tuple"):
                    changed = copy.deepcopy(tree)
                    changed["program"]["steps"][1]["expr"]["field"] = "1"
                    check(work, reseal(changed, honest), False)
                    rejected += 1
                if kind in ("helper_tuple", "helpers"):
                    changed = copy.deepcopy(tree)
                    body = changed["program"]["helpers"][0]["body"]
                    body["lhs"], body["rhs"] = body["rhs"], body["lhs"]
                    check(work, reseal(changed, honest), False)
                    rejected += 1
                changed = copy.deepcopy(tree)
                changed["program"]["inputs"].reverse()
                check(work, {**honest, "tree": canonical(changed)}, False)
                rejected += 1
                if kind == "helpers":
                    changed = copy.deepcopy(tree)
                    changed["program"]["helpers"].reverse()
                    # Helper order erases from SSA, so this specifically
                    # tests the independently parsed source declaration order.
                    check(work, {**honest, "tree": canonical(changed)}, False)
                    rejected += 1
                if kind in ("tuple", "helper_tuple"):
                    changed = copy.deepcopy(tree)
                    steps = changed["program"]["steps"]
                    steps[0], steps[1] = steps[1], steps[0]
                    check(work, {**honest, "tree": canonical(changed)}, False)
                    rejected += 1
                    changed = copy.deepcopy(tree)
                    del changed["program"]["steps"][1]["expr"]
                    check(work, {**honest, "tree": canonical(changed)}, False)
                    rejected += 1
                for malformed in (
                    {**tree, "unexpected": 1},
                    {key: value for key, value in tree.items() if key != "program"},
                    {**tree, "program": {**tree["program"], "fragment": "record-v2"}},
                ):
                    check(work, {**honest, "tree": canonical(malformed)}, False)
                    rejected += 1
                noncanonical = honest["tree"].replace(b"  \"capability\"",
                                                       b" \"capability\"", 1)
                check(work, {**honest, "tree": noncanonical}, False)
                rejected += 1
        if args.native:
            check_native(work, native_cases)
        print(f"structural Lean gate: {accepted} generated compiler/Python/Lean cases, "
          f"{rejected} mutations rejected")


if __name__ == "__main__":
    main()
