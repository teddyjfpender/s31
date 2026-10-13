#!/usr/bin/env python3
"""Check typed-tree erasure against the exact source, relation, and ABI bytes.

Generated cases exercise the admitted M31 grammar. They are differential
controls, not a universal proof that the Python and Lean parsers agree.
"""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import abi  # noqa: E402
from package import lean_effects_admission as admission  # noqa: E402
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
    accepted = 0
    rejected = 0
    with tempfile.TemporaryDirectory(prefix="s31-structural-lean-") as temp:
        work = Path(temp)
        for kind in ("tuple", "helper_tuple", "constant", "helpers"):
            for lanes in (1, 2, 3):
                honest = artifacts(source(kind, lanes))
                check(work, honest, True)
                accepted += 1
                if lanes != 2:
                    continue
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
        # The opt-in production wrapper must consume the exact artifact in
        # the admitted snapshot before it yields to the native verifier.
        sample = artifacts(source("helper_tuple", 2))
        package = work / "package"
        package.mkdir()
        names = {"source": "source.s31", "tree": "typed-structural-derivation.json",
                 "certificate": "source-relation-certificate.json",
                 "relation": "source.s31.json", "abi": "public-abi.json"}
        for key, name in names.items():
            (package / name).write_bytes(sample[key])
        manifest = {"source_text_sha256": "externally pinned in real admission",
                    "artifacts": {name: "snapshot hash" for name in names.values()}}
        calls: list[str] = []

        @contextmanager
        def fake_pinned(path: Path, digest: str):
            calls.append(f"pin:{path.name}:{digest}")
            yield path

        @contextmanager
        def fake_snapshot(_package: Path, _pins: dict[str, str]):
            yield package, manifest

        def fake_effects(_checker: Path, mode: str, *_paths: Path) -> None:
            calls.append(f"effects:{mode}")

        def fake_structural(_checker: Path, _source: Path, tree: Path,
                            *_paths: Path) -> None:
            if tree != package / names["tree"]:
                raise AssertionError("structural checker saw a different artifact")
            calls.append("structural")

        with patch.object(admission, "_pinned_checker", fake_pinned), \
             patch.object(admission, "admitted_snapshot", fake_snapshot), \
             patch.object(admission, "_run_checker", fake_effects), \
             patch.object(admission, "_run_structural_checker", fake_structural):
            with admission.bounded_effects_snapshot(
                package, {}, Path("effects"), "e" * 64,
                Path("structural"), "s" * 64,
            ):
                calls.append("yield")
            if calls != ["pin:effects:" + "e" * 64,
                         "pin:structural:" + "s" * 64,
                         "effects:static", "structural", "yield"]:
                raise AssertionError(f"production structural gate order: {calls}")
            try:
                with admission.bounded_effects_snapshot(
                    package, {}, Path("effects"), "e" * 64,
                    Path("structural"), None):
                    raise AssertionError("incomplete structural pin accepted")
            except ValueError:
                pass
        print(f"structural Lean gate: {accepted} generated compiler/Python/Lean cases, "
          f"{rejected} mutations rejected; opt-in package dispatch checked")


if __name__ == "__main__":
    main()
