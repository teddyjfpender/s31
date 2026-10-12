#!/usr/bin/env python3
"""Compare a public writeBase recommitment with a verified proof's main root.

This is an honest-prover diagnostic. It does not authenticate every committed
row, prove a general source-to-PCS theorem, or expose private trace values.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402

SOURCE = S31 / "examples/arithmetic/functional_square4_manual.s31"
ASSIGNMENT = S31 / "examples/arithmetic/functional_square4.valid.json"
P = (1 << 31) - 1


def main_words(report: dict) -> bytes:
    columns = report.get("main_columns")
    if (type(columns) is not list or len(columns) != 12 or
            any(type(column) is not list or len(column) != 512 for column in columns)):
        raise ValueError("public physical export has the wrong main shape")
    words = bytearray()
    for column in columns:
        for value in column:
            if type(value) is not int or not 0 <= value < P:
                raise ValueError("public physical export has a noncanonical M31 word")
            words.extend(struct.pack("<I", value))
    return bytes(words)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, help="retain package, proof and statement")
    args = parser.parse_args()
    if args.work:
        args.work.mkdir(parents=True, exist_ok=True)
        run(args.work)
    else:
        with tempfile.TemporaryDirectory(prefix="s31-public-main-root-") as directory:
            run(Path(directory))


def run(work: Path) -> None:
    package = s31.build(SOURCE, work / "package", "direct-gate")
    manifest = s31.verify_package(package)
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    assignment = json.loads(ASSIGNMENT.read_bytes())
    statement = {key: value for key, value in assignment.items() if key != "private_inputs"}
    statement_path = work / "statement.json"
    statement_path.write_text(json.dumps(statement, sort_keys=True) + "\n")
    proof = work / "proof.bin"
    s31.invoke(str(prover), "prove", str(ASSIGNMENT), str(proof))
    s31.invoke(str(verifier), str(proof), str(statement_path),
               str(package / "verification-key.json"))
    physical = json.loads(s31.invoke(str(prover), "inspect-physical-root", str(ASSIGNMENT)))
    exported = json.loads(s31.invoke(str(prover), "inspect-physical-rows", str(ASSIGNMENT)))
    topology = json.loads(s31.invoke(str(prover), "inspect-topology"))
    if (physical.get("schema") != "s31-direct-gate-public-main-root-v1" or
            manifest.get("source_text_sha256") != hashlib.sha256(SOURCE.read_bytes()).hexdigest() or
            physical.get("program_sha256") != manifest.get("program_sha256") or
            physical.get("public_words") != assignment["public_inputs"]["x"] +
            assignment["public_outputs"]["result"] or
            exported.get("program_sha256") != physical["program_sha256"] or
            exported.get("public_words") != physical["public_words"] or
            [column.get("values") for column in topology.get("columns", [])] !=
            exported.get("fixed_columns")):
        raise ValueError("public physical-root diagnostic differs from admitted source/statement")
    root_hex = physical.get("main_root")
    main_sha = physical.get("main_columns_sha256")
    if (type(root_hex) is not str or re.fullmatch(r"[0-9a-f]{64}", root_hex) is None or
            type(main_sha) is not str or re.fullmatch(r"[0-9a-f]{64}", main_sha) is None or
            hashlib.sha256(main_words(exported)).hexdigest() != main_sha):
        raise ValueError("main root/digest differs from serialized public physical rows")
    changed_export = copy.deepcopy(exported)
    changed_export["main_columns"][0][0] = (changed_export["main_columns"][0][0] + 1) % P
    if hashlib.sha256(main_words(changed_export)).hexdigest() == main_sha:
        raise AssertionError("one-cell physical-row mutation retained the main digest")
    raw = proof.read_bytes()
    fixed_root, proof_main_root, main_offset = proof_roots(raw)
    key = json.loads((package / "verification-key.json").read_bytes())
    if fixed_root.hex() != key.get("preprocessed_root") or proof_main_root.hex() != root_hex:
        raise ValueError("diagnostic main commitment differs from verified proof")

    changed = bytearray(raw)
    changed[main_offset] ^= 1
    mutant = work / "wrong-main-root.bin"
    mutant.write_bytes(changed)
    denied = subprocess.run((str(verifier), str(mutant), str(statement_path),
                             str(package / "verification-key.json")),
                            capture_output=True, text=True, timeout=120, check=False)
    if denied.returncode == 0 or denied.stderr.strip() != "error: InvalidInteractionNonce":
        raise ValueError(f"one-byte main-root mutation was not rejected at nonce: {denied.stderr}")
    print(json.dumps({"schema": "s31-public-main-root-binding-v1",
                      "source_text_sha256": manifest["source_text_sha256"],
                      "program_sha256": physical["program_sha256"],
                      "preprocessed_root": fixed_root.hex(),
                      "main_root": root_hex,
                      "main_columns_sha256": main_sha,
                      "main_cells": 6144,
                      "proof_bytes": len(raw),
                      "proof_sha256": hashlib.sha256(raw).hexdigest(),
                      "honest_native_verifier_accepted": True,
                      "changed_main_root_rejected": "InvalidInteractionNonce"},
                     sort_keys=True))


if __name__ == "__main__":
    main()
