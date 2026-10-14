#!/usr/bin/env python3
"""Check exact source, complete fixed rows, and honest zero/nonzero traces."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

from package import build as package_build  # noqa: E402
from package.context import invoke  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.verify import verify_package  # noqa: E402
from package.zero_test_native_rows import (ARTIFACT, UnsupportedZeroTest,
                                           check_export, make_certificate,
                                           parse_source)  # noqa: E402

SOURCE = ("use std@1;\n"
          "circuit zero(public x: [m31; 1]) -> public [m31; 1] {\n"
          "  let z = std::field::is_zero(x);\n"
          "  z\n}\n")


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def run() -> dict[str, object]:
    old_invoke = package_build.invoke

    def bounded(*args: str) -> str:
        if args[:2] == ("zig", "build"):
            args = (*args[:2], "-j4", *args[2:])
        return old_invoke(*args)

    package_build.invoke = bounded
    try:
        with tempfile.TemporaryDirectory(prefix="s31-zero-native-") as temporary:
            work = Path(temporary)
            source = work / "zero.s31"
            source.write_text(SOURCE)
            package = package_build.build_text(source, work / "package", "direct-gate")
            verify_package(package)
            certificate = make_certificate(package)
            if certificate != json.loads((package / ARTIFACT).read_bytes()):
                raise AssertionError("source-bound zero-test certificate differs")
            if certificate["gate_counts"] != {"add": 502, "sub": 3,
                                               "mul": 6, "pointwise_mul": 1}:
                raise AssertionError("unexpected zero-test Gate row geometry")
            key = json.loads((package / "verification-key.json").read_bytes())
            prover = package / "bin" / "s31-zero-prover"
            verifier = package / "bin" / "s31-zero-native-verifier"
            key_path = package / "verification-key.json"
            for input_word, expected in ((0, 1), (7, 0)):
                assignment = work / f"assignment-{input_word}.json"
                assignment.write_bytes(encoded({"public_inputs": {"x": [input_word]},
                                                "private_inputs": {},
                                                "public_outputs": {"z": [expected]}}))
                statement = work / f"statement-{input_word}.json"
                statement.write_bytes(encoded({"public_inputs": {"x": [input_word]},
                                               "public_outputs": {"z": [expected]}}))
                physical = json.loads(invoke(str(prover), "inspect-physical-rows",
                                             str(assignment)))
                root = json.loads(invoke(str(prover), "inspect-physical-root",
                                         str(assignment)))
                digest = check_export(input_word, physical, root)
                proof = work / f"proof-{input_word}.bin"
                invoke(str(prover), "prove", str(assignment), str(proof))
                invoke(str(verifier), str(proof), str(statement), str(key_path))
                fixed_root, main_root, _ = proof_roots(proof.read_bytes())
                if (fixed_root.hex() != key["preprocessed_root"] or
                        main_root.hex() != root["main_root"] or
                        root["main_columns_sha256"] != digest):
                    raise AssertionError("honest zero-test proof roots differ from source")
                wrong_statement = work / f"wrong-statement-{input_word}.json"
                wrong_statement.write_bytes(encoded({"public_inputs": {"x": [input_word]},
                                                     "public_outputs": {"z": [1 - expected]}}))
                try:
                    invoke(str(verifier), str(proof), str(wrong_statement), str(key_path))
                except RuntimeError:
                    pass
                else:
                    raise AssertionError("wrong public zero-test indicator verified")
                for kind in ("fixed", "main", "public", "digest"):
                    changed = copy.deepcopy(physical)
                    wrong_root = copy.deepcopy(root)
                    if kind == "fixed":
                        changed["fixed_columns"][0][0] ^= 1
                    elif kind == "main":
                        changed["main_columns"][8][0] ^= 1
                    elif kind == "public":
                        changed["public_words"][1] ^= 1
                    else:
                        wrong_root["main_columns_sha256"] = "00" * 32
                    try:
                        check_export(input_word, changed, wrong_root)
                    except ValueError:
                        pass
                    else:
                        raise AssertionError(f"zero-test {kind} mutation passed")

            # Re-sealing a different source or a false row-role certificate
            # cannot turn the artifact into a package-verifier admission.
            forged = work / "forged"
            shutil.copytree(package, forged)
            wrong = json.loads((forged / ARTIFACT).read_bytes())
            wrong["row_roles"]["indicator_zero_anchor"]["trace_row"] = 2
            (forged / ARTIFACT).write_bytes(encoded(wrong))
            forged_manifest = json.loads((forged / "manifest.json").read_bytes())
            forged_manifest["artifacts"][ARTIFACT] = hashlib.sha256(
                (forged / ARTIFACT).read_bytes()).hexdigest()
            (forged / "manifest.json").write_bytes(encoded(forged_manifest))
            try:
                verify_package(forged)
            except ValueError:
                pass
            else:
                raise AssertionError("re-sealed false zero-test row role passed")
            renamed = ("// a different exact source spelling\n"
                       "circuit count_zero(public value: [m31; 1]) -> public [m31; 1] {\n"
                       " let answer = std::field::is_zero(value); answer }\n")
            renamed_relation = parse_source(renamed.encode())
            if (renamed_relation["name"] != "count_zero" or
                    renamed_relation["inputs"][0]["name"] != "value" or
                    renamed_relation["public_outputs"] != ["answer"]):
                raise AssertionError("independent parser did not bind renamed source bytes")
            for other in (SOURCE.replace("is_zero", "inv"),
                          SOURCE.replace("is_zero(x)", "select(x, x, x)"),
                          SOURCE.replace("public x", "private x")):
                try:
                    parse_source(other.encode())
                except UnsupportedZeroTest:
                    pass
                else:
                    raise AssertionError("unsupported field control entered zero-test admission")
            return {"schema": "s31-zero-test-correspondence-acceptance-v1",
                    "source_bound_fixed_rows": 512,
                    "source_derived_main_cells_per_case": 6144,
                    "honest_proofs_verified": 2,
                    "zero_and_nonzero_cases": [0, 7],
                    "physical_mutations_rejected": 8,
                    "wrong_public_statements_rejected": 2,
                    "resealed_row_role_rejected": True,
                    "renamed_commented_source_parsed": True,
                    "inv_select_private_admission_rejected": True}
    finally:
        package_build.invoke = old_invoke


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
