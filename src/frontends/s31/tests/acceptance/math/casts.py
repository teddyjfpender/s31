#!/usr/bin/env python3
"""Native proof and overflow controls for checked fixed-width numeric casts."""

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


EXAMPLES = S31 / "examples/math/casts"
CASES = {
    "i8_to_i16": (8, True, 16, True, [255], [65535]),
    "i16_to_i8": (16, True, 8, True, [65408], [128]),
    "i128_to_i64": (128, True, 64, True,
                     [65531] + [65535] * 7, [65531] + [65535] * 3),
}
OVERFLOW = {
    "i16_to_i8": ([65407], [127]),  # -129 with the plausible low byte
    "i128_to_i64": ([0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0]),  # +2^64 with low bits zero
}
EXPECTED_GEOMETRY = {
    "i8_to_i16": {
        "canonical_ir_sha256": "308bb5b5a5428a890cf859165c06c1b47ed04a8d9152d8e88f2d3712a9f4b4f6",
        "raw": {"blake_g": 0, "eq": 4, "m31_to_u32": 4, "qm31_ops": 48, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "i16_to_i8": {
        "canonical_ir_sha256": "1a723c60b1911e282c80bfd318dffadab8eda99081e3d924fa8a545fa43eed4c",
        "raw": {"blake_g": 0, "eq": 10, "m31_to_u32": 8, "qm31_ops": 54, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
    },
    "i128_to_i64": {
        "canonical_ir_sha256": "5f364373a4516ade0ac8b44272fd2e16b5fdd93cebbded4c66a9fd2120bf864f",
        "raw": {"blake_g": 0, "eq": 11, "m31_to_u32": 12, "qm31_ops": 70, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66640,
    },
}


def run_case(work: Path, name: str, case: tuple) -> dict:
    source_width, source_signed, target_width, target_signed, input_words, output_words = case
    source = EXAMPLES / f"{name}.s31"
    fixture = EXAMPLES / f"{name}.valid.json"
    relation, _ = compile_text(source.read_text(), str(source))
    if [node["op"] for node in relation["nodes"]] != ["int_view", "int_cast_checked"]:
        raise AssertionError(f"{name}: unexpected lowering")
    encoded = (source_width | (256 if source_signed else 0)) | \
              ((target_width | (256 if target_signed else 0)) << 9)
    if relation["nodes"][1]["constant"] != encoded:
        raise AssertionError(f"{name}: width or sign tags changed")
    assignment = json.loads(fixture.read_text())
    if assignment["private_inputs"] != {"value": input_words} or \
       assignment["public_outputs"] != {"result": output_words}:
        raise AssertionError(f"{name}: fixture changed")
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{name}: independent oracle rejected the honest cast")
    package = s31.build(source, work / name, "sparse-wide-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "sparse-wide-v5" or cost["constant_min_base"] != 16:
        raise AssertionError(f"{name}: unexpected AIR profile or constant policy")
    if any(cost[field] != value for field, value in EXPECTED_GEOMETRY[name].items()):
        raise AssertionError(f"{name}: pinned AIR geometry changed")
    trial = s31.trial(package, fixture, work / f"{name}-trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError(f"{name}: native proof or statement rejection failed")

    native_overflow_rejected = None
    if name != "i8_to_i16":
        forged = json.loads(fixture.read_text())
        forged["private_inputs"]["value"], forged["public_outputs"]["result"] = OVERFLOW[name]
        try:
            evaluate_relation(relation, forged)
        except OracleError as error:
            if "cast overflow" not in str(error):
                raise AssertionError(f"{name}: overflow rejected for another reason") from error
        else:
            raise AssertionError(f"{name}: oracle accepted overflow")
        invalid = work / f"{name}.overflow.json"
        s31.write_json(invalid, forged)
        prover = package / "bin" / f"s31-{name}-prover"
        rejected = subprocess.run([str(prover), "prove", str(invalid),
                                   str(work / f"{name}.overflow.proof")],
                                  capture_output=True, text=True, timeout=120)
        if rejected.returncode == 0:
            raise AssertionError(f"{name}: native prover accepted overflow")
        native_overflow_rejected = True

    return {"name": name, "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"], "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
            "native_overflow_rejected": native_overflow_rejected}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-int-casts-") as temporary:
        work = Path(temporary)
        cases = [run_case(work, name, case) for name, case in CASES.items()]
    print(json.dumps({"schema": "s31-int-casts-native-v1", "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
