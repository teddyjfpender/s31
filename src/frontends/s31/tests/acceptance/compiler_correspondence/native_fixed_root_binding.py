#!/usr/bin/env python3
"""Check the pinned square4 fixed roster against a native verifier and proof.

The static check is quick and reads checked-in evidence.  --native rebuilds a
source-bound direct-Gate package, produces a proof, and changes only the
serialized preprocessed root.  These checks do not prove PCS opening soundness.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/direct_gate_release_cost"))
sys.path.insert(0, str(ROOT / "formal/s31/scripts"))

import s31  # noqa: E402
import fixed_columns  # noqa: E402
import check_square4_native_witness as witness  # noqa: E402

REPORT = ROOT / "formal/s31/fixtures/square4-native-physical.json"
VALUES = (ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/"
          "PinnedSquare4ConstantValues.lean")
MAIN_LEAN = ROOT / "formal/s31/S31/Gadgets/Functional/TextSquare4NativeWitness.lean"
ASSIGNMENT = S31 / "examples/arithmetic/functional_square4.valid.json"
MAGIC = b"S31NAT7G"


def lean_values(source: str) -> list[tuple[int, int, int, int]]:
    match = re.search(r"(?ms)^def nativeValues : List Quad := \[\n(.*?)^\]$", source)
    if match is None:
        raise ValueError("Lean nativeValues literal missing")
    pattern = re.compile(r"\s*⟨(\d+), (\d+), (\d+), (\d+)⟩,?\s*")
    result = []
    for line in match.group(1).splitlines():
        item = pattern.fullmatch(line)
        if item is None:
            raise ValueError("Lean nativeValues literal has invalid syntax")
        result.append(tuple(map(int, item.groups())))
    if len(result) != 512 or any(word >= fixed_columns.P for row in result for word in row):
        raise ValueError("Lean nativeValues shape or M31 canonicality differs")
    return result


def check_evidence(report: dict, metadata: dict, fixed: list[tuple[int, ...]],
                   formal_rows: list[tuple[int, ...]], values: list[tuple[int, ...]],
                   main_lean: str, values_lean: str) -> dict:
    """Compare every fixed cell and every address-indexed main output."""
    witness.check_report(report)
    if len(formal_rows) != 512 or len(fixed) != 8 or len(values) != 512:
        raise ValueError("pinned fixed/Lean roster shape differs")
    for row in range(512):
        for column in range(8):
            native_word = fixed[column][row]
            if (report["fixed_columns"][column][row] != native_word or
                    formal_rows[row][column] != native_word):
                raise ValueError(f"native/physical/Lean fixed cell differs at {row}:{column}")
    addresses = report["fixed_columns"][6]
    if sorted(addresses) != list(range(512)):
        raise ValueError("physical output addresses are not a permutation of 0..511")
    for row, address in enumerate(addresses):
        physical = tuple(report["main_columns"][column][row] for column in range(8, 12))
        if values[address] != physical:
            raise ValueError(f"Lean/native output value differs at address {address}")
    root = metadata["preprocessed_root"]
    declared_roots = re.findall(
        r'(?m)^def preprocessedRoot : String := "([0-9a-f]{64})"$', main_lean)
    if (type(root) is not str or re.fullmatch(r"[0-9a-f]{64}", root) is None or
            declared_roots != [root]):
        raise ValueError("Lean main witness root differs from fixed-column fixture")
    digest = hashlib.sha256(REPORT.read_bytes()).hexdigest()
    declared_digests = re.findall(
        r"(?m)^-- Source physical SHA-256: ([0-9a-f]{64})$", values_lean)
    if declared_digests != [digest]:
        raise ValueError("Lean address-value source digest differs from physical report")
    return {"schema": "s31-square4-native-fixed-root-binding-v1",
            "fixed_cells": 4096, "address_values": 512,
            "preprocessed_root": root,
            "physical_report_sha256": digest,
            "fixed_column_bytes_sha256": metadata["binary_sha256"]}


def static_check() -> tuple[dict, dict, dict]:
    report = json.loads(REPORT.read_bytes())
    metadata, fixed = fixed_columns.read_fixture()
    formal_rows = fixed_columns.read_formal_rows()
    values_lean = VALUES.read_text()
    main_lean = MAIN_LEAN.read_text()
    values = lean_values(values_lean)
    result = check_evidence(report, metadata, fixed, formal_rows, values,
                            main_lean, values_lean)
    return result, report, {"metadata": metadata, "fixed": fixed,
                            "formal_rows": formal_rows, "values": values,
                            "main_lean": main_lean, "values_lean": values_lean}


def reject_static_mutations(report: dict, evidence: dict) -> int:
    altered_report = copy.deepcopy(report)
    altered_report["fixed_columns"][0][11] ^= 1
    altered_rows = list(evidence["formal_rows"])
    row = list(altered_rows[11])
    row[0] ^= 1
    altered_rows[11] = tuple(row)
    altered_values = list(evidence["values"])
    quad = list(altered_values[0])
    quad[0] ^= 1
    altered_values[0] = tuple(quad)
    altered_metadata = dict(evidence["metadata"])
    altered_metadata["preprocessed_root"] = "00" * 32
    root_line = (f'def preprocessedRoot : String := '
                 f'"{evidence["metadata"]["preprocessed_root"]}"')
    spoofed_root_source = evidence["main_lean"].replace(
        root_line, 'def preprocessedRoot : String := "' + "00" * 32 +
        '"\n-- ' + root_line, 1)
    if spoofed_root_source == evidence["main_lean"]:
        raise AssertionError("Lean root declaration missing from mutation fixture")
    digest_line = "-- Source physical SHA-256: " + hashlib.sha256(REPORT.read_bytes()).hexdigest()
    spoofed_digest_source = evidence["values_lean"].replace(
        digest_line, "-- Source physical SHA-256: " + "00" * 32 +
        "\n" + digest_line, 1)
    if spoofed_digest_source == evidence["values_lean"]:
        raise AssertionError("Lean physical digest missing from mutation fixture")
    changes = (
        (altered_report, evidence["metadata"], evidence["formal_rows"], evidence["values"],
         evidence["main_lean"], evidence["values_lean"]),
        (report, evidence["metadata"], altered_rows, evidence["values"],
         evidence["main_lean"], evidence["values_lean"]),
        (report, evidence["metadata"], evidence["formal_rows"], altered_values,
         evidence["main_lean"], evidence["values_lean"]),
        (report, altered_metadata, evidence["formal_rows"], evidence["values"],
         evidence["main_lean"], evidence["values_lean"]),
        (report, evidence["metadata"], evidence["formal_rows"], evidence["values"],
         spoofed_root_source, evidence["values_lean"]),
        (report, evidence["metadata"], evidence["formal_rows"], evidence["values"],
         evidence["main_lean"], spoofed_digest_source),
    )
    for index, (changed, metadata, rows, values, main_lean, values_lean) in enumerate(changes):
        try:
            check_evidence(changed, metadata, evidence["fixed"], rows, values,
                           main_lean, values_lean)
        except ValueError:
            pass
        else:
            raise AssertionError(f"static mutation {index} was accepted")
    return len(changes)


def checked_native(work: Path, expected: dict) -> dict:
    # An absent temporary path forces the current compiler and native verifier
    # to be built; the script never edits the checked-in fixture or a package.
    package = s31.build(fixed_columns.SOURCE, work / "package", "direct-gate")
    metadata, encoded = fixed_columns.native_fixture(package)
    fixture, _ = fixed_columns.read_fixture()
    if metadata != fixture or encoded != fixed_columns.WORDS.read_bytes():
        raise ValueError("fresh native package differs from pinned fixed-column fixture")
    if metadata["preprocessed_root"] != expected["preprocessed_root"]:
        raise ValueError("fresh native package root differs from Lean/pinned root")
    inspected = witness.inspect_package(package, ASSIGNMENT)
    if inspected != json.loads(REPORT.read_bytes()):
        raise ValueError("fresh native physical trace differs from pinned report")

    manifest = json.loads((package / "manifest.json").read_bytes())
    key = package / "verification-key.json"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    proof = work / "proof.bin"
    statement = work / "statement.json"
    claim = json.loads(ASSIGNMENT.read_bytes())
    claim.pop("private_inputs", None)
    statement.write_text(json.dumps(claim, sort_keys=True) + "\n")
    s31.invoke(str(prover), "prove", str(ASSIGNMENT), str(proof))
    s31.invoke(str(verifier), str(proof), str(statement), str(key))

    raw = proof.read_bytes()
    root = bytes.fromhex(expected["preprocessed_root"])
    if not raw.startswith(MAGIC) or len(raw) < 32:
        raise ValueError("unexpected direct-Gate bound proof envelope")
    # The first 32 bytes occur in the postcard body after the eight-byte
    # envelope, nonce, and single four-limb interaction claim.
    start = len(MAGIC) + 8 + 16
    positions = [i for i in range(start, len(raw) - 31) if raw[i:i + 32] == root]
    if len(positions) != 1:
        raise ValueError(f"expected one serialized fixed root, found {len(positions)}")
    changed = bytearray(raw)
    changed[positions[0]] ^= 1
    if changed[:positions[0]] != raw[:positions[0]] or changed[positions[0] + 1:] != raw[positions[0] + 1:]:
        raise AssertionError("root mutation changed another proof byte")
    mutant = work / "wrong-fixed-root.bin"
    mutant.write_bytes(changed)
    result = subprocess.run((str(verifier), str(mutant), str(statement), str(key)),
                            capture_output=True, text=True, timeout=60, check=False)
    if result.returncode == 0 or result.stderr.strip() != "error: InvalidPreprocessedRoot":
        raise AssertionError(f"native verifier did not reject fixed-root mutation: {result.stderr}")
    return {"native_proof_bytes": len(raw), "native_proof_sha256": hashlib.sha256(raw).hexdigest(),
            "serialized_root_offset": positions[0],
            "native_root_mutation_rejected": "InvalidPreprocessedRoot"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build, prove and verify from fresh source")
    args = parser.parse_args()
    result, report, evidence = static_check()
    result["static_mutations_rejected"] = reject_static_mutations(report, evidence)
    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-square4-root-binding-") as directory:
            result.update(checked_native(Path(directory), result))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
