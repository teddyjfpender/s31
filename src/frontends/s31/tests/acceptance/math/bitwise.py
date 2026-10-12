#!/usr/bin/env python3
"""Native proof, false-claim, and pinned geometry controls for integer bits."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


EXAMPLES = S31 / "examples/math/bitwise"
EXPECTED = {
    "u8_xor": {
        "canonical_ir_sha256": "019bb9d642147499bba94a50f59883b5b8438ed473dc3e7bb990c363f85853d2",
        "raw": {"blake_g": 0, "eq": 20, "m31_to_u32": 4, "qm31_ops": 141, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 32, "m31_to_u32": 16, "qm31_ops": 256, "triple_xor": 0},
        "preprocessed_cells": 67696,
    },
    "u32_mix": {
        "canonical_ir_sha256": "96592086adf85d67c781e7b1cdf5a9e3ca5fa6aa177297619f1cbbc9770fbabe",
        "raw": {"blake_g": 0, "eq": 68, "m31_to_u32": 4, "qm31_ops": 820, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 128, "m31_to_u32": 16, "qm31_ops": 1024, "triple_xor": 0},
        "preprocessed_cells": 74032,
    },
    "i128_xor": {
        "canonical_ir_sha256": "b529539ef2e01f54c36fe963144ef6d03fbe4ad31930a4990daa6002ffa5f389",
        "raw": {"blake_g": 0, "eq": 272, "m31_to_u32": 16, "qm31_ops": 1812, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 512, "m31_to_u32": 16, "qm31_ops": 2048, "triple_xor": 0},
        "preprocessed_cells": 82992,
    },
}


def run_case(work: Path, name: str) -> dict:
    source = EXAMPLES / f"{name}.s31"
    fixture = EXAMPLES / f"{name}.valid.json"
    assignment = json.loads(fixture.read_text())
    relation, _ = compile_text(source.read_text(), str(source))
    ops = [node["op"] for node in relation["nodes"]]
    expected_ops = ["int_view", "int_view", "int_bit_xor"] if name.endswith("_xor") else [
        "int_view", "int_view", "int_bit_and", "int_bit_xor", "int_bit_not", "int_bit_or"]
    if ops != expected_ops:
        raise AssertionError(f"{name}: lowering changed: {ops}")
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{name}: independent oracle rejected honest assignment")

    package = s31.build(source, work / name, "sparse-wide-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "sparse-wide-v5" or cost["constant_min_base"] != 16:
        raise AssertionError(f"{name}: changed AIR profile or constant policy")
    if any(cost[field] != value for field, value in EXPECTED[name].items()):
        raise AssertionError(f"{name}: changed canonical circuit or AIR geometry")
    trial = s31.trial(package, fixture, work / f"{name}-trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError(f"{name}: native proof or changed statement control failed")

    forged = json.loads(fixture.read_text())
    forged["public_outputs"]["result"][0] ^= 1
    try:
        evaluate_relation(relation, forged)
    except OracleError:
        pass
    else:
        raise AssertionError(f"{name}: oracle accepted false output")
    invalid = work / f"{name}.false-output.json"
    s31.write_json(invalid, forged)
    prover = package / "bin" / f"s31-{name}-prover"
    rejected = subprocess.run([str(prover), "prove", str(invalid),
                               str(work / f"{name}.false-output.proof")],
                              capture_output=True, text=True, timeout=120)
    if rejected.returncode == 0:
        raise AssertionError(f"{name}: native prover accepted false output")
    return {"name": name, "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"], "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
            "false_output_rejected": True}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-int-bits-") as temporary:
        work = Path(temporary)
        cases = [run_case(work, name) for name in EXPECTED]
    print(json.dumps({"schema": "s31-int-bits-native-v1", "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
