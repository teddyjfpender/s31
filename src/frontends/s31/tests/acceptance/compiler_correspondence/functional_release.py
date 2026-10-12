#!/usr/bin/env python3
"""Functional syntax must have zero native AIR cost and pass strict release verification."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Callable

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from package.correspondence import check_package, parse_source  # noqa: E402
from package.direct_gate_main_correspondence import check_export  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.trust import pinned_paths  # noqa: E402
from text_frontend import compile_text  # noqa: E402

EXAMPLE = S31 / "examples/functional/release_square4"
SAME_AIR = ("canonical_ir_sha256", "profile", "chip", "raw", "padded",
            "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
            "input_packing", "public_binding", "finalization", "fri")
P = (1 << 31) - 1


def check_full_public_trace(package: Path, assignment: Path, proof: Path,
                            syntax: dict, input_words: list[int]) -> dict:
    """Join the independent 512-row base trace to one verified public proof.

    This checks an honest prover run. It does not authenticate arbitrary PCS
    openings or establish a general compiler theorem.
    """
    manifest = json.loads((package / "manifest.json").read_bytes())
    key = json.loads((package / "verification-key.json").read_bytes())
    topology = json.loads((package / "gate-topology.json").read_bytes())
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    fresh_topology = json.loads(s31.invoke(str(prover), "inspect-topology"))
    physical = json.loads(s31.invoke(str(prover), "inspect-physical-rows", str(assignment)))
    root = json.loads(s31.invoke(str(prover), "inspect-physical-root", str(assignment)))
    if (fresh_topology != topology or
            topology.get("preprocessed_root") != key.get("preprocessed_root") or
            physical.get("schema") != "s31-direct-gate-public-functional-physical-v1" or
            root.get("schema") != "s31-direct-gate-public-main-root-v1" or
            physical.get("program_sha256") != manifest.get("program_sha256") or
            root.get("program_sha256") != manifest.get("program_sha256") or
            [column.get("values") for column in topology.get("columns", [])] !=
            physical.get("fixed_columns")):
        raise AssertionError("native physical export differs from the source-bound package")
    checked = check_export(syntax, input_words, physical, root)
    fixed_root, main_root, _ = proof_roots(proof.read_bytes())
    if (fixed_root.hex() != key.get("preprocessed_root") or
            main_root.hex() != root.get("main_root")):
        raise AssertionError("accepted proof roots differ from the independently checked trace")
    changed = copy.deepcopy(physical)
    changed["main_columns"][8][0] = (changed["main_columns"][8][0] + 1) % P
    try:
        check_export(syntax, input_words, changed, root)
    except ValueError:
        pass
    else:
        raise AssertionError("changed native main cell passed the independent trace check")
    denied = json.loads(assignment.read_bytes())
    denied["private_inputs"] = {"secret": [1]}
    with tempfile.TemporaryDirectory(prefix="s31-private-trace-control-") as directory:
        denied_path = Path(directory) / "assignment.json"
        s31.write_json(denied_path, denied)
        for command in ("inspect-physical-rows", "inspect-physical-root"):
            attempt = subprocess.run((str(prover), command, str(denied_path)),
                                     capture_output=True, text=True, timeout=120, check=False)
            report = attempt.stdout + attempt.stderr
            if (attempt.returncode == 0 or
                    "PrivatePhysicalRowsUnavailable" not in attempt.stderr or
                    any(field in report for field in ('"main_columns"', '"fixed_columns"',
                                                      '"main_root"', '"main_columns_sha256"'))):
                raise AssertionError("public trace diagnostic exposed private assignment data")
    return {"source_derived_main_cells": checked["source_derived_main_cells"],
            "source_derived_main_columns_sha256": checked["source_derived_main_columns_sha256"],
            "accepted_proof_main_root": main_root.hex(),
            "changed_main_cell_rejected": True,
            "private_assignment_diagnostic_rejected": True}


def run(example: Path = EXAMPLE, *, case: str = "composed",
        result: Callable[[int], int] = lambda value: 2 * value * value,
        full_public_trace: bool = False) -> dict:
    functional_source = example / "functional.s31"
    direct_source = example / "manual.s31"
    functional_text = functional_source.read_text()
    direct_text = direct_source.read_text()
    functional_relation, functional_syntax = parse_source(functional_text.encode())
    direct_relation, direct_syntax = parse_source(direct_text.encode())
    if (functional_relation != direct_relation or functional_syntax != direct_syntax or
            compile_text(functional_text)[0] != functional_relation or
            compile_text(direct_text)[0] != direct_relation):
        raise AssertionError("named helper changed the independently checked relation")

    with tempfile.TemporaryDirectory(prefix="s31-functional-release-") as directory:
        work = Path(directory)
        direct = s31.build(direct_source, work / "direct-package", "direct-gate")
        functional = s31.build(functional_source, work / "functional-package", "direct-gate")
        direct_cost = json.loads((direct / "cost-report.json").read_text())
        cost = json.loads((functional / "cost-report.json").read_text())
        different = [field for field in SAME_AIR if cost[field] != direct_cost[field]]
        if different:
            raise AssertionError(f"named helper changed native AIR geometry: {different}")
        checked = check_package(functional)
        if (checked["status"]["source_to_normalized"] != "source-to-normalized-checked" or
                checked["status"]["native_root_binding"] != "native-reported-fixed-root-matches-key"):
            raise AssertionError("functional package lacks rooted correspondence certificate")

        values = [0, 1, 2, 7]
        expected = [result(value) % P for value in values]
        assignment = work / "assignment.json"
        s31.write_json(assignment, {"public_inputs": {"x": values},
                                    "private_inputs": {},
                                    "public_outputs": {"result": expected}})
        trial = s31.trial(functional, assignment, work / "proof")
        if not trial["native_verifier_accepted"]:
            raise AssertionError("functional package native proof was rejected")

        pins = {kind: s31.file_hash(path) for kind, path in pinned_paths(functional).items()}
        flags = [item for kind, digest in pins.items()
                 for item in (f"--{kind}-sha256", digest)]
        s31.invoke(sys.executable, str(S31 / "python/s31.py"), "verify-release",
                   str(functional), str(work / "proof/proof.bin"),
                   "--statement", str(work / "proof/statement.json"), *flags)

        statement = json.loads((work / "proof/statement.json").read_text())
        statement["public_outputs"]["result"][3] = (expected[3] + 1) % P
        changed = work / "changed-statement.json"
        s31.write_json(changed, statement)
        try:
            s31.invoke(sys.executable, str(S31 / "python/s31.py"), "verify-release",
                       str(functional), str(work / "proof/proof.bin"),
                       "--statement", str(changed), *flags)
        except RuntimeError:
            pass
        else:
            raise AssertionError("strict release verifier accepted a changed public claim")

        trace = (check_full_public_trace(functional, assignment, work / "proof/proof.bin",
                                         functional_syntax, values)
                 if full_public_trace else {})
        return {"schema": "s31-functional-release-v1", "case": case,
                "nodes": len(functional_relation["nodes"]),
                "raw_qm31_rows": cost["raw"]["qm31_ops"],
                "padded_qm31_rows": cost["padded"]["qm31_ops"],
                "proof_bytes": trial["proof_bytes"],
                "functional_and_direct_air_equal": True,
                "rooted_certificate_checked": True,
                "strict_release_proof_accepted": True,
                "changed_public_claim_rejected": True, **trace}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
