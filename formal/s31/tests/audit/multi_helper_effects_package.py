#!/usr/bin/env python3
"""Cross-check bounded helper chains against production, Python and Lean.

The Lean checker is the production package gate. These generated controls are
evidence of parser agreement across the admitted helper count and arities;
they are not a theorem that the two independent parsers are equivalent.
"""

from __future__ import annotations

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

from package.source_relation_fragment import (  # noqa: E402
    UnsupportedSourceRelationFragment,
    check_source_relation_certificate,
    make_source_relation_certificate,
    parse_source_fragment,
)
from text_frontend import compile_text  # noqa: E402

CHECKER = FORMAL / "S31/Audit/GeneralLinearSSAEffectsPackageCheck.lean"
MODULUS = 2**31 - 1


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def source(helper_count: int, lanes: int) -> bytes:
    helpers = []
    body = []
    prior = "x"
    for index in range(helper_count):
        name = f"h{index}"
        if index % 2:
            helpers.append(f"fn {name}(v: [m31; {lanes}]) -> [m31; {lanes}] "
                           "{ v .* v }")
            call = f"{name}({prior})"
        else:
            op = "-" if index % 4 == 0 else "+"
            helpers.append(f"fn {name}(a: [m31; {lanes}], b: [m31; {lanes}]) "
                           f"-> [m31; {lanes}] {{ a {op} b }}")
            call = f"{name}({prior}, y)"
        body.append(f"  let n{index} = {call};")
        prior = f"n{index}"
    body.append("  assert_eq(x, x);")
    body.append(f"  {prior}")
    return ("\n".join(helpers) + "\n" +
            f"circuit chain{helper_count}x{lanes}(public x: [m31; {lanes}], "
            f"private y: [m31; {lanes}]) -> public [m31; {lanes}] {{\n" +
            "\n".join(body) + "\n}\n").encode()


def run_checker(work: Path, source_bytes: bytes, cert: bytes, relation: bytes,
                abi: bytes, assignment: bytes, statement: bytes,
                accepted: bool) -> None:
    for name, data in (("source.s31", source_bytes), ("certificate.json", cert),
                       ("relation.json", relation), ("abi.json", abi),
                       ("assignment.json", assignment), ("statement.json", statement)):
        (work / name).write_bytes(data)
    args = ["lake", "env", "lean", "--run", str(CHECKER), "statement",
            *(str(work / name) for name in (
        "source.s31", "certificate.json", "relation.json", "abi.json",
        "assignment.json", "statement.json"))]
    result = subprocess.run(args, cwd=FORMAL, capture_output=True,
                            text=True, timeout=30, check=False)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"expected accepted={accepted}: {result.stdout} {result.stderr}")


def evaluated(relation: dict, x: list[int], y: list[int]) -> list[int]:
    values = {"x": x, "y": y}
    for node in relation["nodes"]:
        lhs = values[node["lhs"]]
        rhs = values[node["rhs"]]
        if node["op"] == "add":
            values[node["name"]] = [(a + b) % MODULUS for a, b in zip(lhs, rhs)]
        elif node["op"] == "sub":
            values[node["name"]] = [(a - b) % MODULUS for a, b in zip(lhs, rhs)]
        elif node["op"] == "mul":
            values[node["name"]] = [(a * b) % MODULUS for a, b in zip(lhs, rhs)]
        else:
            raise AssertionError("unexpected helper operation")
    return values[relation["public_outputs"][0]]


def main() -> None:
    accepted = 0
    corpus = hashlib.sha256()
    with tempfile.TemporaryDirectory(prefix="s31-multi-helper-effects-") as root:
        work = Path(root)
        for count in (1, 2, 4, 8):
            for lanes in (1, 2, 3, 4):
                text = source(count, lanes)
                corpus.update(text + b"\0")
                produced, _ = compile_text(text.decode())
                independent = parse_source_fragment(text)
                if produced != independent:
                    raise AssertionError(f"production/Python relation mismatch: {count}, {lanes}")
                relation = canonical(produced)
                certificate = make_source_relation_certificate(text, relation)
                cert = canonical(certificate)
                check_source_relation_certificate(text, relation, cert)
                output = produced["public_outputs"][0]
                abi = canonical({
                    "schema": "s31-public-abi-v1",
                    "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
                    "public_inputs": [{"name": "x", "kind": "m31", "length": lanes}],
                    "public_outputs": [{"name": output, "kind": "m31", "length": lanes}],
                })
                x = list(range(1, lanes + 1))
                y = list(range(5, lanes + 5))
                statement_obj = {"public_inputs": {"x": x},
                                 "public_outputs": {output: evaluated(produced, x, y)}}
                assignment = canonical({"public_inputs": {"x": x},
                                        "private_inputs": {"y": y},
                                        "public_outputs": statement_obj["public_outputs"]})
                statement = canonical(statement_obj)
                run_checker(work, text, cert, relation, abi, assignment, statement, True)
                accepted += 1

                if count == 8 and lanes == 4:
                    # Re-seal an altered compiler graph and certificate. Both
                    # checkers must reject it against the unchanged source.
                    forged_relation = copy.deepcopy(produced)
                    forged_relation["nodes"][0]["op"] = "add"
                    forged_bytes = canonical(forged_relation)
                    forged_cert = copy.deepcopy(certificate)
                    forged_cert["relation_sha256"] = hashlib.sha256(forged_bytes).hexdigest()
                    forged_cert["ssa"]["nodes"][0]["op"] = "add"
                    try:
                        check_source_relation_certificate(text, forged_bytes,
                                                          canonical(forged_cert))
                    except ValueError:
                        pass
                    else:
                        raise AssertionError("Python admitted re-sealed wrong operation")
                    run_checker(work, text, canonical(forged_cert), forged_bytes,
                                abi, assignment, statement, False)
                    changed_source = text.replace(b"{ a - b }", b"{ b - a }", 1)
                    run_checker(work, changed_source, cert, relation, abi,
                                assignment, statement, False)
                    unsupported = (
                        source(9, lanes),
                        text.replace(b"fn h7", b"fn h0", 1),
                        text.replace(b"h1(n0)", b"h1(n0, y)", 1),
                        text.replace(b"circuit chain", b"fn spare(v: [m31; 4]) "
                                     b"-> [m31; 4] { v + v }\ncircuit chain", 1),
                    )
                    for changed in unsupported:
                        try:
                            parse_source_fragment(changed)
                        except UnsupportedSourceRelationFragment:
                            pass
                        else:
                            raise AssertionError("Python admitted unsupported helper grammar")
                        run_checker(work, changed, cert, relation, abi,
                                    assignment, statement, False)
    print(f"multi-helper effects: {accepted} Python/compiler/Lean statement cases, "
          f"six Lean mutations rejected; corpus sha256={corpus.hexdigest()}")


if __name__ == "__main__":
    main()
