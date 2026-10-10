#!/usr/bin/env python3
"""Native proof and false-statement gate for fixed-width products."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


CASES = {
    "u8_wrapping": 8, "u32_wrapping": 32, "i128_wrapping": 128,
    "u8_checked": 8, "i8_checked": 8, "u32_checked": 32, "i128_checked": 128,
}
EXAMPLES = S31 / "examples/math/multiplication"
EXPECTED_GEOMETRY: dict[str, dict] = {
    "u8_wrapping": {
        "canonical_ir_sha256": "4fb68eabb270bd1a7113b114d289ac9ad6ec4fcc9fffd4b193cf184a3a58424d",
        "raw": {"blake_g": 0, "eq": 4, "m31_to_u32": 7, "qm31_ops": 39, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
        "constant_min_base": 16,
    },
    "u32_wrapping": {
        "canonical_ir_sha256": "508967fe1e0364715d9f71c415cf8fb444b1f4c204f84e4fc39c9323c9047362",
        "raw": {"blake_g": 0, "eq": 16, "m31_to_u32": 28, "qm31_ops": 86, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 32, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66688,
        "constant_min_base": 16,
    },
    "i128_wrapping": {
        "canonical_ir_sha256": "0c0b0aa924714ddf11319e86efa2ae25d049e2e962d26fbfaa3708fcf62c9107",
        "raw": {"blake_g": 0, "eq": 64, "m31_to_u32": 112, "qm31_ops": 452, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 64, "m31_to_u32": 128, "qm31_ops": 512, "triple_xor": 0},
        "preprocessed_cells": 70144,
        "constant_min_base": 16,
    },
    "u8_checked": {
        "canonical_ir_sha256": "fe40aeb6924a7b3ff60e26d74005c0c95f4a15ed624af3714da1cd22d8cbdd47",
        "raw": {"blake_g": 0, "eq": 7, "m31_to_u32": 10, "qm31_ops": 43, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 16, "m31_to_u32": 16, "qm31_ops": 64, "triple_xor": 0},
        "preprocessed_cells": 66128,
        "constant_min_base": 16,
    },
    "i8_checked": {
        "canonical_ir_sha256": "39305c62b8d531146d9f8eb93d6117b6b7f36e1961eb7df1104db36049a888d2",
        "raw": {"blake_g": 0, "eq": 19, "m31_to_u32": 16, "qm31_ops": 78, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 32, "m31_to_u32": 16, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66672,
        "constant_min_base": 16,
    },
    "u32_checked": {
        "canonical_ir_sha256": "8ae78ab4f881d2c8c4758d7ea3fe9159325ba0e6fae41fa9a04c4da69fdaa097",
        "raw": {"blake_g": 0, "eq": 25, "m31_to_u32": 40, "qm31_ops": 116, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 32, "m31_to_u32": 64, "qm31_ops": 128, "triple_xor": 0},
        "preprocessed_cells": 66816,
        "constant_min_base": 16,
    },
    "i128_checked": {
        "canonical_ir_sha256": "e3d448a826ac57ecf4a9451a1f5bc5bcb6dd1ce1662fc33a755339808a01acfd",
        "raw": {"blake_g": 0, "eq": 123, "m31_to_u32": 166, "qm31_ops": 903, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 128, "m31_to_u32": 256, "qm31_ops": 1024, "triple_xor": 0},
        "preprocessed_cells": 74752,
        "constant_min_base": 16,
    },
}


def decode(words: list[int]) -> int:
    return sum(word << (16 * index) for index, word in enumerate(words))


def check_case(work: Path, name: str, width: int) -> dict:
    source = EXAMPLES / f"{name}.s31"
    fixture = EXAMPLES / f"{name}.valid.json"
    relation, _ = compile_text(source.read_text(), str(source))
    assignment = json.loads(fixture.read_text())
    checked = name.endswith("_checked")
    op = "int_mul_checked" if checked else "int_mul_wrapping"
    if [node["op"] for node in relation["nodes"]] != ["int_view", "int_view", op]:
        raise AssertionError(f"{name}: multiplication relation changed")
    spec = width + (256 if name.startswith("i") else 0)
    if any(node["constant"] != spec for node in relation["nodes"]):
        raise AssertionError(f"{name}: width or signedness tag changed")
    private = assignment["private_inputs"]
    expected = (decode(private["a"]) * decode(private["b"])) % (1 << width)
    limbs = [(expected >> (16 * index)) & 0xffff
             for index in range(max(1, width // 16))]
    if assignment["public_outputs"] != {"product": limbs}:
        raise AssertionError(f"{name}: fixture differs from independent integer product")
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{name}: independent oracle rejected honest product")
    forged = json.loads(fixture.read_text())
    forged["public_outputs"]["product"][0] ^= 1
    try:
        evaluate_relation(relation, forged)
    except OracleError:
        pass
    else:
        raise AssertionError(f"{name}: independent oracle accepted false product")
    if checked:
        overflow = json.loads(fixture.read_text())
        over_a = 1 << (width - 1) if name.startswith("i") else (1 << width) - 1
        over_b = (1 << width) - 1 if name.startswith("i") else 2
        overflow["private_inputs"] = {
            "a": [(over_a >> (16 * i)) & 0xffff for i in range(max(1, width // 16))],
            "b": [(over_b >> (16 * i)) & 0xffff for i in range(max(1, width // 16))],
        }
        overflow["public_outputs"]["product"] = [0] * max(1, width // 16)
        try:
            evaluate_relation(relation, overflow)
        except OracleError as error:
            if "overflow" not in str(error):
                raise AssertionError(f"{name}: overflow control failed for another reason") from error
        else:
            raise AssertionError(f"{name}: overflow control was accepted")

    package = s31.build(source, work / name, "sparse-wide-gate")
    cost = json.loads((package / "cost-report.json").read_text())
    if cost["profile"] != "sparse-wide-v5" or cost["raw"]["qm31_ops"] == 0:
        raise AssertionError(f"{name}: expected constrained sparse-wide AIR")
    expected_geometry = EXPECTED_GEOMETRY[name]
    if any(cost[key] != value for key, value in expected_geometry.items()):
        raise AssertionError(f"{name}: pinned AIR geometry changed")
    trial = s31.trial(package, fixture, work / f"{name}-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{name}: native proof or false-statement rejection failed")
    return {"name": name, "width": width,
            "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "constant_min_base": cost["constant_min_base"],
            "proof_bytes": trial["proof_bytes"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
            "overflow_oracle_rejected": checked}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=CASES)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="s31-int-multiplication-") as temporary:
        work = Path(temporary)
        names = [args.case] if args.case else list(CASES)
        results = [check_case(work, name, CASES[name]) for name in names]
    print(json.dumps({"schema": "s31-int-multiplication-native-v1", "cases": results},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
