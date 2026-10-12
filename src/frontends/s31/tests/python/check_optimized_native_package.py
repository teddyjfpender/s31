"""Opt-in native direct-gate package smoke test for reversed/CSE source.

Run explicitly on a clean pinned Stwo dependency. The normal package builder
remains v2-only. This script attaches the separate v3 correspondence artifact
to a fresh package, derives all public main cells from normalized source,
joins the native proof roots, and rejects rooted and full-trace mutations.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.build import build
from package.context import file_hash, invoke, write_json
from package.correspondence import (check_optimized_package, digest,
                                    make_optimized_certificate, parse_source_optimized)
from package.direct_gate_main_correspondence import check_export, source_values
from package.fixed_root_join import proof_roots

SOURCE = ("circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { "
          "let a = x + x; let b = x .* x; let c = a + b; "
          "let d = b + a; d }\n")
CANONICAL_DIGEST = "2088c1bad15f2ba5b52f0214e9d3d66744b9c84aa6218aa336d8b337157e7132"
P = (1 << 31) - 1
INPUT = [0, 1, 2, 7]
OUTPUT = [(2 * value + value * value) % P for value in INPUT]


def attach_v3(package: Path) -> None:
    topology = json.loads(invoke(
        str(package / "bin" / "s31-reverse_share-prover"), "inspect-topology"))
    topology_path = package / "gate-topology.json"
    write_json(topology_path, topology)
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["artifacts"][topology_path.name] = file_hash(topology_path)
    write_json(manifest_path, manifest)

    certificate_path = package / "correspondence-certificate.json"
    write_json(certificate_path, make_optimized_certificate(package))
    manifest["artifacts"][certificate_path.name] = file_hash(certificate_path)
    write_json(manifest_path, manifest)


def fixed_words(columns: list[dict]) -> bytes:
    if (type(columns) is not list or len(columns) != 8 or
            any(type(column) is not dict or
                type(column.get("values")) is not list or
                len(column["values"]) != 512 or
                any(type(value) is not int or not 0 <= value < P
                    for value in column["values"])
                for column in columns)):
        raise ValueError("optimized fixed columns have the wrong shape")
    return b"".join(struct.pack("<I", value)
                    for column in columns for value in column["values"])


def main_words(columns: list[list[int]]) -> bytes:
    if (type(columns) is not list or len(columns) != 12 or
            any(type(column) is not list or len(column) != 512 or
                any(type(value) is not int or not 0 <= value < P
                    for value in column)
                for column in columns)):
        raise ValueError("optimized main columns have the wrong shape")
    return b"".join(struct.pack("<I", value)
                    for column in columns for value in column)


def rejected_root(verifier: Path, proof: bytes, index: int,
                  statement: Path, key: Path, work: Path, wanted: str) -> None:
    changed = bytearray(proof)
    changed[index] ^= 1
    path = work / f"rejected-{wanted}.bin"
    path.write_bytes(changed)
    result = subprocess.run((str(verifier), str(path), str(statement), str(key)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode == 0 or result.stderr.strip() != f"error: {wanted}":
        raise AssertionError(f"changed proof root was not rejected at {wanted}: {result.stderr}")


def proof_join(package: Path, checked: dict, work: Path) -> dict:
    """Join v3 source-derived fixed cells to one native accepted proof.

    This is a fresh local-package regression. The package's certificate and
    binaries are not authenticated by an external release channel, and the
    check assumes the installed native verifier and commitment implementation.
    """
    prover = package / "bin" / "s31-reverse_share-prover"
    verifier = package / "bin" / "s31-reverse_share-native-verifier"
    key_path = package / "verification-key.json"
    invoke(str(verifier), "check-key", str(key_path))
    topology = json.loads(invoke(str(prover), "inspect-topology"))
    if topology != json.loads((package / "gate-topology.json").read_bytes()):
        raise ValueError("fresh native topology differs from optimized certificate")
    fixed = fixed_words(topology["columns"])
    fixed_input = work / "fixed-columns.json"
    write_json(fixed_input, {"schema": "s31-direct-gate-fixed-columns-v1",
                             "fixed_columns": [column["values"] for column in topology["columns"]]})
    recommitted = json.loads(invoke(str(prover), "inspect-fixed-root-from-columns",
                                    str(fixed_input)))
    key = json.loads(key_path.read_bytes())
    fixed_root = recommitted.get("fixed_root")
    if (recommitted.get("schema") != "s31-direct-gate-recommitted-fixed-root-v1" or
            fixed_root != key.get("preprocessed_root") or
            fixed_root != topology.get("preprocessed_root")):
        raise ValueError("optimized source fixed columns do not match sealed key")
    changed_columns = [column["values"].copy() for column in topology["columns"]]
    changed_columns[0][3] = (changed_columns[0][3] + 1) % P
    changed_path = work / "changed-fixed-columns.json"
    write_json(changed_path, {"schema": "s31-direct-gate-fixed-columns-v1",
                              "fixed_columns": changed_columns})
    changed_root = json.loads(invoke(str(prover), "inspect-fixed-root-from-columns",
                                      str(changed_path)))["fixed_root"]
    if changed_root == fixed_root:
        raise AssertionError("changed optimized source selector retained fixed root")

    assignment = work / "assignment.json"
    statement = work / "statement.json"
    proof_path = work / "proof.bin"
    write_json(assignment, {"public_inputs": {"x": INPUT}, "private_inputs": {},
                            "public_outputs": {"d": OUTPUT}})
    write_json(statement, {"public_inputs": {"x": INPUT},
                           "public_outputs": {"d": OUTPUT}})
    source_bytes = (package / "source.s31").read_bytes()
    _, syntax = parse_source_optimized(source_bytes)
    _, source_output = source_values(syntax, INPUT)
    if (hashlib.sha256(source_bytes).hexdigest() != checked["source_sha256"] or
            list(source_output) != OUTPUT or syntax["output_name"] != "d"):
        raise ValueError("independently evaluated normalized source differs from claim")
    invoke(str(prover), "prove", str(assignment), str(proof_path))
    invoke(str(verifier), str(proof_path), str(statement), str(key_path))
    proof = proof_path.read_bytes()
    proof_fixed, proof_main, main_offset = proof_roots(proof)
    if proof_fixed.hex() != fixed_root:
        raise ValueError("accepted optimized proof fixed root differs from source roster")

    physical = json.loads(invoke(str(prover), "inspect-physical-rows", str(assignment)))
    main = json.loads(invoke(str(prover), "inspect-physical-root", str(assignment)))
    main_blob = main_words(physical.get("main_columns"))
    reference = check_export(syntax, INPUT, physical, main)
    if (physical.get("fixed_columns") != [column["values"] for column in topology["columns"]] or
            physical.get("public_words") != INPUT + OUTPUT or
            main.get("public_words") != INPUT + OUTPUT or
            main.get("main_columns_sha256") != hashlib.sha256(main_blob).hexdigest() or
            proof_main.hex() != main.get("main_root")):
        raise ValueError("accepted optimized proof main root differs from exported public trace")
    if reference["source_derived_main_columns_sha256"] != hashlib.sha256(main_blob).hexdigest():
        raise ValueError("source-derived main trace digest differs from accepted proof root report")
    for label, changed_trace in (
        ("main-cell", copy.deepcopy(physical)),
        ("column-order", copy.deepcopy(physical)),
    ):
        if label == "main-cell":
            changed_trace["main_columns"][0][0] = (changed_trace["main_columns"][0][0] + 1) % P
        else:
            changed_trace["main_columns"][0], changed_trace["main_columns"][1] = (
                changed_trace["main_columns"][1], changed_trace["main_columns"][0])
        try:
            check_export(syntax, INPUT, changed_trace, main)
        except ValueError as error:
            if "native main columns differ" not in str(error):
                raise
        else:
            raise AssertionError(f"forged optimized {label} matched source-derived trace")
    rejected_root(verifier, proof, main_offset - 32, statement, key_path, work,
                  "InvalidPreprocessedRoot")
    rejected_root(verifier, proof, main_offset, statement, key_path, work,
                  "InvalidInteractionNonce")
    forged_statement = work / "forged-statement.json"
    write_json(forged_statement, {"public_inputs": {"x": INPUT},
                                  "public_outputs": {"d": [0, 3, 8, 64]}})
    wrong_claim = subprocess.run((str(verifier), str(proof_path), str(forged_statement),
                                  str(key_path)), capture_output=True, text=True,
                                 timeout=120, check=False)
    if (wrong_claim.returncode == 0 or
            wrong_claim.stderr.strip() != "error: InvalidInteractionNonce"):
        raise AssertionError(f"optimized changed public output had wrong result: {wrong_claim.stderr}")
    if checked["source_ssa"]["source_to_canonical"] != [0, 1, 2, 3, 3]:
        raise ValueError("optimized source did not reuse its final arithmetic gate")
    return {
        "schema": "s31-optimized-v3-native-root-join-v1",
        "scope": "one fresh public four-lane reversed/CSE program and one accepted proof",
        "source_sha256": checked["source_sha256"],
        "canonical_ir_sha256": checked["key_core"]["canonical_ir_sha256"],
        "source_to_canonical": checked["source_ssa"]["source_to_canonical"],
        "arithmetic_source_lets": 4,
        "native_arithmetic_gates": len(checked["source_ssa"]["instructions"]),
        "fixed_cells": 4096,
        "fixed_columns_sha256": hashlib.sha256(fixed).hexdigest(),
        "main_cells": 6144,
        "main_columns_sha256": hashlib.sha256(main_blob).hexdigest(),
        "source_derived_public_words": reference["source_derived_public_words"],
        "source_derived_main_columns_sha256": reference["source_derived_main_columns_sha256"],
        "source_derived_main_cells": reference["source_derived_main_cells"],
        "sealed_fixed_root": fixed_root,
        "accepted_proof_fixed_root": proof_fixed.hex(),
        "accepted_proof_main_root": proof_main.hex(),
        "proof_sha256": hashlib.sha256(proof).hexdigest(),
        "proof_bytes": len(proof),
        "native_verifier_accepted": True,
        "changed_fixed_root_rejected": "InvalidPreprocessedRoot",
        "changed_fixed_selector_changed_root": True,
        "changed_main_root_rejected": "InvalidInteractionNonce",
        "changed_public_claim_rejected": "InvalidInteractionNonce",
        "forged_main_cell_rejected": True,
        "swapped_main_columns_rejected": True,
    }


def run(root: Path) -> None:
    source = root / "reverse_share.s31"
    source.write_text(SOURCE)
    package = build(source, root / "package", "direct-gate")
    if (package / "correspondence-certificate.json").exists():
        raise AssertionError("default v2 builder unexpectedly admitted optimized source")
    attach_v3(package)
    checked = check_optimized_package(package)
    if (checked["source_ssa"]["source_to_canonical"] != [0, 1, 2, 3, 3] or
            checked["key_core"]["canonical_ir_sha256"] != CANONICAL_DIGEST or
            [(row["qm31_start"], row["qm31_end"])
             for row in checked["gate_schedule"]] !=
            [(0, 6), (6, 7), (7, 8), (8, 9)]):
        raise AssertionError("native optimized certificate differs from pinned fixture")

    joined = proof_join(package, checked, root)

    forged = root / "forged"
    shutil.copytree(package, forged)
    report_path = forged / "cost-report.json"
    report = json.loads(report_path.read_text())
    report["source_map"][-1]["qm31_start"] = 9
    write_json(report_path, report)
    manifest_path = forged / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["artifacts"][report_path.name] = file_hash(report_path)
    write_json(manifest_path, manifest)
    if manifest["artifacts"][report_path.name] != digest(report_path.read_bytes()):
        raise AssertionError("forged cost report was not resealed")
    try:
        check_optimized_package(forged)
    except ValueError as error:
        if "native gate spans differ" not in str(error):
            raise
    else:
        raise AssertionError("resealed malformed native source map was admitted")
    print(json.dumps({**joined, "resealed_bad_source_span_rejected": True},
                     sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, help="retain package, proof, and exports")
    args = parser.parse_args()
    if args.work is None:
        with tempfile.TemporaryDirectory(prefix="s31-optimized-native-") as directory:
            run(Path(directory))
    else:
        args.work.mkdir(parents=True, exist_ok=True)
        run(args.work)


if __name__ == "__main__":
    main()
