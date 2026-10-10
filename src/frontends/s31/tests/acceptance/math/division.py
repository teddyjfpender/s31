#!/usr/bin/env python3
"""Native proofs and negative controls for fused fixed-width division."""

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


EXAMPLES = S31 / "examples/math/division"
CASES = {
    "u8_div_rem": {
        "spec": 8,
        "canonical_ir_sha256": "01974444113fe3a63061d4a72ba79d5cbf200e86ca84c9aa99419923da100e10",
        "raw": {"blake_g": 0, "eq": 13, "m31_to_u32": 14, "qm31_ops": 55, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "u32_div_rem": {
        "spec": 32,
        "canonical_ir_sha256": "76a5ec985ccd6ca98987f22f1447bd9549652061006a54f46c122b805363251a",
        "raw": {"blake_g": 0, "eq": 30, "m31_to_u32": 42, "qm31_ops": 136, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 32, "m31_to_u32": 64, "qm31_ops": 256, "triple_xor": 0},
        "preprocessed_cells": 67840,
    },
    "i8_div_rem": {
        "spec": 264,
        "canonical_ir_sha256": "d5fe4e98aad634c55bed7ef83790ee49de72dfcd610472a756d30e1ae116ec95",
        "raw": {"blake_g": 0, "eq": 34, "m31_to_u32": 28, "qm31_ops": 122, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 64, "m31_to_u32": 32, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66784,
    },
    "u128_div_quotient": {
        "spec": 128,
        "canonical_ir_sha256": "e41f23f0d422d1e7821ca1a5c6619e6aae9d0a3140840c2f68c19667dbbbb1c4",
        "raw": {"blake_g": 0, "eq": 114, "m31_to_u32": 168, "qm31_ops": 802, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 128, "m31_to_u32": 256, "qm31_ops": 1024, "triple_xor": 0},
        "preprocessed_cells": 74752,
    },
    "i128_div_quotient": {
        "spec": 384,
        "canonical_ir_sha256": "bcbe032a2ffa65c57521bbb65dc2775d2e4dccc8263d58eb221155ba374f1250",
        "raw": {"blake_g": 0, "eq": 187, "m31_to_u32": 206, "qm31_ops": 1121, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 256, "m31_to_u32": 256, "qm31_ops": 2048, "triple_xor": 0},
        "preprocessed_cells": 83200,
    },
}


def rejected_by_native_prover(package: Path, name: str, work: Path,
                              assignment: dict, label: str) -> bool:
    invalid = work / f"{name}.{label}.json"
    s31.write_json(invalid, assignment)
    prover = package / "bin" / f"s31-{name}-prover"
    result = subprocess.run([str(prover), "prove", str(invalid),
                             str(work / f"{name}.{label}.proof")],
                            capture_output=True, text=True, timeout=120)
    return result.returncode != 0


def run_case(work: Path, name: str, expected: dict) -> dict:
    source = EXAMPLES / f"{name}.s31"
    fixture = EXAMPLES / f"{name}.valid.json"
    assignment = json.loads(fixture.read_text())
    relation, _ = compile_text(source.read_text(), str(source))
    div_nodes = [node for node in relation["nodes"] if node["op"] == "int_div_rem"]
    if len(div_nodes) != 1 or div_nodes[0]["constant"] != expected["spec"]:
        raise AssertionError(f"{name}: division must lower exactly once with its width/sign tag")
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{name}: independent oracle rejected honest assignment")

    package = s31.build(source, work / name, "sparse-wide-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "sparse-wide-v5" or cost["constant_min_base"] != 16:
        raise AssertionError(f"{name}: changed AIR profile or integer constant policy")
    if any(cost[field] != expected[field] for field in (
        "canonical_ir_sha256", "raw", "padded", "preprocessed_cells")):
        raise AssertionError(f"{name}: changed canonical circuit or AIR geometry")
    trial = s31.trial(package, fixture, work / f"{name}-trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError(f"{name}: native proof or changed-statement control failed")

    output_name = next(iter(assignment["public_outputs"]))
    false_output = json.loads(fixture.read_text())
    false_output["public_outputs"][output_name][0] ^= 1
    try:
        evaluate_relation(relation, false_output)
    except OracleError:
        pass
    else:
        raise AssertionError(f"{name}: oracle accepted false output")
    if not rejected_by_native_prover(package, name, work, false_output, "false-output"):
        raise AssertionError(f"{name}: native prover accepted false output")

    zero = json.loads(fixture.read_text())
    zero["private_inputs"]["divisor"] = [0] * len(zero["private_inputs"]["divisor"])
    try:
        evaluate_relation(relation, zero)
    except OracleError as exc:
        if "division by zero" not in str(exc):
            raise
    else:
        raise AssertionError(f"{name}: oracle accepted zero divisor")
    if not rejected_by_native_prover(package, name, work, zero, "zero-divisor"):
        raise AssertionError(f"{name}: native prover accepted zero divisor")

    overflow_rejected = None
    if expected["spec"] & 256:
        width = expected["spec"] & 255
        count = max(1, width // 16)
        overflow = json.loads(fixture.read_text())
        minimum_pattern = 1 << (width - 1)
        negative_one_pattern = (1 << width) - 1
        overflow["private_inputs"]["numerator"] = [
            (minimum_pattern >> (16 * i)) & 0xffff for i in range(count)]
        overflow["private_inputs"]["divisor"] = [
            (negative_one_pattern >> (16 * i)) & 0xffff for i in range(count)]
        try:
            evaluate_relation(relation, overflow)
        except OracleError as exc:
            if "division overflow" not in str(exc):
                raise
        else:
            raise AssertionError(f"{name}: oracle accepted MIN / -1")
        overflow_rejected = rejected_by_native_prover(package, name, work, overflow, "min-overflow")
        if not overflow_rejected:
            raise AssertionError(f"{name}: native prover accepted MIN / -1")

    return {"name": name, "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"], "native_verifier_accepted": True,
            "prove_wall_seconds": trial["prove_seconds"],
            "verify_wall_seconds": trial["verify_seconds"],
            "prover_stages": trial["prover_stages"],
            "changed_public_statement_rejected": True,
            "false_output_rejected": True, "zero_divisor_rejected": True,
            "signed_overflow_rejected": overflow_rejected}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-int-division-") as temporary:
        work = Path(temporary)
        cases = [run_case(work, name, expected) for name, expected in CASES.items()]
    print(json.dumps({"schema": "s31-int-division-native-v1", "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
