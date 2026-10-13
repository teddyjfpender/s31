#!/usr/bin/env python3
"""Exercise the exact-byte Lean helper/tuple interpreter gate and mutations.

The ordinary builder still omits a source-relation certificate for combined
helper/product text. This audit constructs the bounded effects certificate
from the independent Python relation parser, then checks its entire payload
with the Lean byte gate. It is not package enrollment or compiler equivalence.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.source_relation_fragment import _indexed_ssa, parse_source_fragment  # noqa: E402

SOURCE = ("fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }\n"
          "circuit combined_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {\n"
          "    let pair = (x, y);\n    let left = pair.0;\n    let right = pair.1;\n"
          "    let out = subtract(left, right);\n    out\n}\n").encode()
RUNNER = ("lake", "env", "lean", "--run",
          "S31/Audit/GeneralLinearSSAEffectsPackageCheck.lean")


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def artifacts(source: bytes) -> tuple[bytes, bytes, bytes]:
    relation = parse_source_fragment(source, _allow_helper_products=True)
    relation_bytes = canonical(relation)
    ssa, effects = _indexed_ssa(relation)
    if effects or ssa["nodes"] != [{"id": 2, "name": "out", "op": "sub",
                                     "lhs": 0, "rhs": 1}]:
        raise AssertionError("independent parser did not derive one ordered subtraction")
    certificate = {"capability": "source-to-relation-only",
                   "lean_semantic_profile": "linear-ssa-m31-effects-v1",
                   "relation_sha256": hashlib.sha256(relation_bytes).hexdigest(),
                   "schema": "s31-source-relation-certificate-v1",
                   "source_sha256": hashlib.sha256(source).hexdigest(),
                   "ssa": ssa, "unmodeled_features": []}
    abi = {"schema": "s31-public-abi-v1",
           "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
           "public_inputs": [{"name": name, "kind": "m31", "length": 2}
                             for name in ("x", "y")],
           "public_outputs": [{"name": "out", "kind": "m31", "length": 2}]}
    return relation_bytes, canonical(certificate), canonical(abi)


def check(directory: Path, values: dict[str, bytes], accepted: bool) -> None:
    paths: dict[str, Path] = {}
    for name, data in values.items():
        path = directory / name
        path.write_bytes(data)
        paths[name] = path
    result = subprocess.run((*RUNNER, "statement",
                             *(str(paths[name]) for name in
                               ("source", "certificate", "relation", "abi",
                                "assignment", "statement"))),
                            cwd=FORMAL, capture_output=True, text=True,
                            timeout=30, check=False)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"Lean accepted={result.returncode == 0}, expected={accepted}: "
                             f"{result.stdout} {result.stderr}")


def main() -> None:
    relation, certificate, abi = artifacts(SOURCE)
    assignment = {"public_inputs": {"x": [7, 11], "y": [3, 5]},
                  "private_inputs": {}, "public_outputs": {"out": [4, 6]}}
    statement = {key: assignment[key] for key in ("public_inputs", "public_outputs")}
    base = {"source": SOURCE, "relation": relation, "certificate": certificate,
            "abi": abi, "assignment": canonical(assignment),
            "statement": canonical(statement)}
    with tempfile.TemporaryDirectory(prefix="s31-helper-tuple-lean-") as temp:
        work = Path(temp)
        check(work, base, True)
        swapped = SOURCE.replace(b"left = pair.0", b"left = pair.1").replace(
            b"right = pair.1", b"right = pair.0")
        check(work, {**base, "source": swapped}, False)
        reversed_body = SOURCE.replace(b"{ a - b }", b"{ b - a }")
        check(work, {**base, "source": reversed_body}, False)
        check(work, {**base, "source": SOURCE.replace(b"pair.1", b"pair.2")}, False)
        check(work, {**base, "source": SOURCE + b" // trailing comment\n",
                     "relation": relation, "certificate": certificate}, True)
        # The Lean checker validates semantic SSA, not SHA-256 source identity;
        # a changed comment remains semantically equivalent. Its package
        # wrapper independently pins exact source digests.
        mutated_relation = json.loads(relation)
        mutated_relation["nodes"][0]["lhs"] = "y"
        mutated_certificate = json.loads(certificate)
        mutated_certificate["ssa"]["nodes"][0]["lhs"] = 1
        mutated_certificate["relation_sha256"] = hashlib.sha256(
            canonical(mutated_relation)).hexdigest()
        check(work, {**base, "relation": canonical(mutated_relation),
                     "certificate": canonical(mutated_certificate)}, False)
        bad_claim = dict(assignment)
        bad_claim["public_outputs"] = {"out": [5, 6]}
        check(work, {**base, "assignment": canonical(bad_claim),
                     "statement": canonical({"public_inputs": bad_claim["public_inputs"],
                                              "public_outputs": bad_claim["public_outputs"]})}, False)
    print("combined helper/tuple Lean byte run: honest accepted, five semantic mutations rejected")


if __name__ == "__main__":
    main()
