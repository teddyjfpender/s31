#!/usr/bin/env python3
"""Native proofs and false-claim controls for static integer shifts."""

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


EXAMPLES = S31 / "examples/math/shifts"
CASES = {
    "i128_sar128": {
        "op": "int_shr_arithmetic", "spec": 384, "index": 128,
        "canonical_ir_sha256": "4fd4b4a1bb6f33070dffa14ee806d66240cf046515164eac3d14d1a317707f03",
        "raw": {"blake_g": 0, "eq": 3, "m31_to_u32": 10, "qm31_ops": 71, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66640,
    },
    "i8_sar8": {
        "op": "int_shr_arithmetic", "spec": 264, "index": 8,
        "canonical_ir_sha256": "0b58959847fd077f423601d92d5f0891357c053a393a9b86d757dbeb5ece9dd0",
        "raw": {"blake_g": 0, "eq": 4, "m31_to_u32": 4, "qm31_ops": 45, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "u32_rotl16": {
        "op": "int_rotl", "spec": 32, "index": 16,
        "canonical_ir_sha256": "16a87cdf2710caeb467c52cfde1af4292ae6b0e39a22e1550c150ff1c3127973",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 2, "qm31_ops": 36, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "u32_rotr4": {
        "op": "int_rotr", "spec": 32, "index": 4,
        "canonical_ir_sha256": "ab937b70de109aca38eeff9d69b0a754c63bdfb1d1a2f9c6521d5950fd493096",
        "raw": {"blake_g": 0, "eq": 34, "m31_to_u32": 2, "qm31_ops": 220, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 64, "m31_to_u32": 16, "qm31_ops": 256, "triple_xor": 0},
        "preprocessed_cells": 67760,
    },
    "u32_shl16": {
        "op": "int_shl", "spec": 32, "index": 16,
        "canonical_ir_sha256": "ed5ce7fa20e0f528a464001b3086e1d3dd55b1eeb34e86c7d8564ce99028ff72",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 2, "qm31_ops": 35, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "u32_shr_logical4": {
        "op": "int_shr_logical", "spec": 32, "index": 4,
        "canonical_ir_sha256": "92c4cc6e608b16df4c6422fc1e87f8faea7a276948130bc2abfe315f87c327e1",
        "raw": {"blake_g": 0, "eq": 34, "m31_to_u32": 2, "qm31_ops": 212, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 64, "m31_to_u32": 16, "qm31_ops": 256, "triple_xor": 0},
        "preprocessed_cells": 67760,
    },
}


def run_case(work: Path, name: str, expected: dict) -> dict:
    source = EXAMPLES / f"{name}.s31"
    fixture = EXAMPLES / f"{name}.valid.json"
    assignment = json.loads(fixture.read_text())
    relation, _ = compile_text(source.read_text(), str(source))
    nodes = relation["nodes"]
    if [node["op"] for node in nodes] != ["int_view", expected["op"]] or \
       nodes[-1]["constant"] != expected["spec"] or nodes[-1]["index"] != expected["index"]:
        raise AssertionError(f"{name}: lowering or static count changed")
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{name}: independent oracle rejected honest assignment")

    package = s31.build(source, work / name, "sparse-wide-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "sparse-wide-v5" or cost["constant_min_base"] != 16:
        raise AssertionError(f"{name}: changed AIR profile or constant policy")
    if any(cost[field] != expected[field] for field in (
        "canonical_ir_sha256", "raw", "padded", "preprocessed_cells")):
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
            "changed_public_statement_rejected": True, "false_output_rejected": True}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-int-shifts-") as temporary:
        work = Path(temporary)
        cases = [run_case(work, name, expected) for name, expected in CASES.items()]
    print(json.dumps({"schema": "s31-int-shifts-native-v1", "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
