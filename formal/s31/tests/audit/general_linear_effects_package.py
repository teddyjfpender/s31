#!/usr/bin/env python3
"""Exercise the generic Lean effects gate with real fixture bytes and mutations."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def check(executable: Path, mode: str, paths: dict[str, Path], accepted: bool) -> None:
    keys = ["source", "certificate", "relation", "abi"]
    if mode == "statement":
        keys.extend(["assignment", "statement"])
    result = subprocess.run(
        [str(executable), mode, *(str(paths[key]) for key in keys)],
        capture_output=True, text=True, check=False, timeout=30,
    )
    if (result.returncode == 0) != accepted:
        raise AssertionError(
            f"{mode}: accepted={result.returncode == 0}, expected={accepted}; "
            f"{result.stdout} {result.stderr}"
        )


def main() -> None:
    formal = Path(__file__).resolve().parents[2]
    sys.path.insert(0, str(formal.parent.parent / "src/frontends/s31/python"))
    from package import lean_effects_admission as admission
    fixture = formal / "fixtures/correspondence"
    executable = formal / ".lake/build/bin/s31-general-linear-effects-package-check"
    paths = {
        "source": fixture / "effects/affine_guard.s31",
        "certificate": fixture / "effects/affine_guard.certificate.json",
        "relation": fixture / "effects/affine_guard.relation.json",
        "abi": fixture / "public_abi/effects.abi.json",
        "assignment": fixture / "public_abi/effects.assignment.json",
    }
    assignment = json.loads(paths["assignment"].read_bytes())
    statement = {key: assignment[key] for key in ("public_inputs", "public_outputs")}
    relation = json.loads(paths["relation"].read_bytes())
    abi = json.loads(paths["abi"].read_bytes())
    certificate = json.loads(paths["certificate"].read_bytes())

    changed_constant = copy.deepcopy(relation)
    changed_constant["nodes"][1]["constant"] = 8
    changed_assertion = copy.deepcopy(relation)
    changed_assertion["assertions"][0]["rhs"] = "shifted"
    changed_abi = copy.deepcopy(abi)
    changed_abi["public_outputs"][0]["length"] = 2
    changed_certificate = copy.deepcopy(certificate)
    changed_certificate["ssa"]["nodes"][0]["constant"] = 8
    changed_private = copy.deepcopy(assignment)
    changed_private["private_inputs"]["y"][0] = 73
    changed_public = copy.deepcopy(statement)
    changed_public["public_outputs"]["out"][0] = 72
    leaked_private = copy.deepcopy(statement)
    leaked_private["private_inputs"] = assignment["private_inputs"]

    static_mutants = [
        ("source", paths["source"].read_bytes().replace(
            b"assert_eq(y, scaled)", b"assert_eq(y, shifted)", 1)),
        ("relation", canonical(changed_constant)),
        ("relation", canonical(changed_assertion)),
        ("abi", canonical(changed_abi)),
        ("certificate", canonical(changed_certificate)),
        ("source", b"x" * 65537),
    ]
    dynamic_mutants = [
        ("assignment", canonical(changed_private)),
        ("statement", canonical(changed_public)),
        ("statement", canonical(leaked_private)),
        ("statement", canonical(statement).replace(b"  \"public_inputs\"",
                                                 b" \"public_inputs\"", 1)),
        ("statement", canonical(statement).replace(
            b'  "public_inputs": {',
            b'  "public_inputs": {},\n  "public_inputs": {', 1)),
    ]
    with tempfile.TemporaryDirectory(prefix="s31-effects-package-controls-") as temporary:
        directory = Path(temporary)
        statement_path = directory / "statement.json"
        statement_path.write_bytes(canonical(statement))
        paths["statement"] = statement_path
        check(executable, "static", paths, True)
        check(executable, "statement", paths, True)
        for index, (name, content) in enumerate(static_mutants):
            mutant = directory / f"static-{index}"
            mutant.write_bytes(content)
            check(executable, "static", {**paths, name: mutant}, False)
        for index, (name, content) in enumerate(dynamic_mutants):
            mutant = directory / f"dynamic-{index}"
            mutant.write_bytes(content)
            check(executable, "statement", {**paths, name: mutant}, False)
        package = directory / "package"
        package.mkdir()
        for name, target in (
            ("source.s31", "source"),
            ("source-relation-certificate.json", "certificate"),
            ("source.s31.json", "relation"),
            ("public-abi.json", "abi"),
        ):
            shutil.copyfile(paths[target], package / name)
        manifest = {
            "name": "affine_guard", "source_text_sha256": "reviewed fixture",
            "artifacts": {"source-relation-certificate.json": "reviewed fixture"},
        }

        @contextmanager
        def reviewed_snapshot(_package: Path, _pins: dict[str, str]):
            yield package, manifest

        checker_path = directory / "reviewed-lean-checker"
        shutil.copyfile(executable, checker_path)
        digest = hashlib.sha256()
        with checker_path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1 << 20), b""):
                digest.update(chunk)
        checker_sha256 = digest.hexdigest()
        with patch.object(admission, "admitted_snapshot", reviewed_snapshot):
            with admission.bounded_effects_snapshot(
                package, {}, checker_path, checker_sha256) as (snapshot, _, _):
                if snapshot != package:
                    raise AssertionError("static package snapshot changed")
            try:
                with admission.bounded_effects_snapshot(
                    package, {}, checker_path, "0" * 64):
                    raise AssertionError("incorrect checker pin accepted")
            except ValueError as exc:
                if "pin mismatch" not in str(exc):
                    raise
            checked_statement: list[Path] = []
            native_statements: list[Path] = []
            original_check = admission._run_checker

            def observed_check(checker: Path, mode: str, *items: Path) -> None:
                if mode == "statement":
                    checked_statement.append(items[-1])
                original_check(checker, mode, *items)

            def fake_native(*args: str) -> str:
                if len(args) == 4:
                    native_statements.append(Path(args[2]))
                return "native verifier invoked"

            proof = directory / "proof.bin"
            proof.write_bytes(b"reviewed proof placeholder")
            with patch.object(admission, "_run_checker", observed_check), \
                 patch.object(admission, "invoke", fake_native):
                result = admission.verify_effectful_proof(
                    package, proof, paths["assignment"], paths["statement"],
                    {}, checker_path, checker_sha256)
            if (result != "native verifier invoked" or
                    len(checked_statement) != 1 or
                    checked_statement != native_statements):
                raise AssertionError("native verifier did not consume Lean-checked statement copy")
    print(f"generic effects gate accepted fixture; rejected "
          f"{len(static_mutants)} static and {len(dynamic_mutants)} statement mutations; "
          "pinned package and same-statement dispatch passed")


if __name__ == "__main__":
    main()
