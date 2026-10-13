#!/usr/bin/env python3
"""Prove a large static power while pinning its native AIR saving."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402

P = (1 << 31) - 1
EXAMPLES = S31 / "examples/arithmetic/powers"
EXPONENT = 65535**4
FUSED_EXPONENT = (EXPONENT - 1) % (P - 1) + 1
EXPECTED = {
    "addition-chain": {"nodes": 39, "raw": 397, "padded": 512,
                       "preprocessed_cells": 4096},
    "binary": {"nodes": 120, "raw": 559, "padded": 1024,
               "preprocessed_cells": 8192},
}


def symbolic_exponent(relation: dict, *, name: str = "pow_chain") -> int:
    """Check every residual gate computes the claimed power for all inputs."""
    if (relation.get("version") != 1 or relation.get("name") != name or
            relation.get("inputs") != [{"name": "x", "kind": "m31",
                                         "length": 8, "visibility": "private"}] or
            relation.get("assertions") != [] or
            relation.get("public_outputs") != ["result"]):
        raise AssertionError("power relation has unexpected boundary")
    powers = {"x": 1}
    for node in relation["nodes"]:
        if (set(node) != {"name", "op", "lhs", "rhs"} or node["op"] != "mul" or
                node["name"] in powers or node["lhs"] not in powers or
                node["rhs"] not in powers):
            raise AssertionError("power relation contains a non-multiplication or bad wire")
        powers[node["name"]] = powers[node["lhs"]] + powers[node["rhs"]]
    return powers["result"]


def run() -> dict:
    assignment_path = EXAMPLES / "pow65535_chain4.valid.json"
    assignment = json.loads(assignment_path.read_text())
    x = assignment["private_inputs"]["x"]
    if (type(x) is not list or len(x) != 8 or
            any(type(word) is not int or not 0 <= word < P for word in x) or
            assignment["public_inputs"] != {} or
            assignment["public_outputs"] != {"result": [pow(word, EXPONENT, P)
                                                       for word in x]}):
        raise AssertionError("power assignment differs from independent modular arithmetic")

    cases = []
    with tempfile.TemporaryDirectory(prefix="s31-power-chain-") as directory:
        work = Path(directory)
        for kind, filename in (("addition-chain", "pow65535_chain4.s31"),
                               ("binary", "pow65535_binary4.s31")):
            package = s31.build(EXAMPLES / filename, work / kind, "direct-gate")
            relation = json.loads((package / "source.s31.json").read_text())
            expected_exponent = FUSED_EXPONENT if kind == "addition-chain" else EXPONENT
            if symbolic_exponent(relation) != expected_exponent:
                raise AssertionError(f"{kind} has the wrong symbolic exponent")
            cost = json.loads((package / "cost-report.json").read_text())
            expected = EXPECTED[kind]
            if (len(relation["nodes"]) != expected["nodes"] or
                    cost["profile"] != "direct-m31-v4" or
                    cost["raw"] != {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                                    "qm31_ops": expected["raw"], "triple_xor": 0} or
                    cost["padded"] != {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                                       "qm31_ops": expected["padded"], "triple_xor": 0} or
                    cost["preprocessed_cells"] != expected["preprocessed_cells"]):
                raise AssertionError(f"{kind} native AIR baseline changed")
            trial = s31.trial(package, assignment_path, work / f"{kind}-trial")
            if (trial["native_verifier_accepted"] is not True or
                    not trial["changed_public_statement_rejected"] or
                    trial["independent_value_oracle"]["status"] != "passed" or
                    trial["proof_bytes"] <= 0):
                raise AssertionError(f"{kind} native proof controls failed")
            cases.append({"kind": kind, "nodes": len(relation["nodes"]),
                          "raw_qm31_rows": cost["raw"]["qm31_ops"],
                          "padded_qm31_rows": cost["padded"]["qm31_ops"],
                          "preprocessed_cells": cost["preprocessed_cells"],
                          "proof_bytes": trial["proof_bytes"],
                          "prove_seconds": trial["prove_seconds"],
                          "native_verified": True,
                          "changed_claim_rejected": True,
                          "independent_oracle_passed": True,
                          "symbolic_exponent_checked": True})
        # A positive exponent divisible by p-1 must remain p-1 rather than
        # becoming zero: zero to a positive power is zero, not one.
        edge_source = work / "zero-residue.s31"
        edge_source.write_text(
            "use std@1;\n"
            "circuit power_zero_residue(private x: [m31; 8]) -> public [m31; 8] {\n"
            "    let first = std::math::pow<2147483646>(x);\n"
            "    let result = std::math::pow<2>(first);\n"
            "    result\n}\n")
        edge_values = [0, 1, 2, 3, 7, P - 1, 1234567, 42]
        edge_assignment = work / "zero-residue.valid.json"
        s31.write_json(edge_assignment, {"public_inputs": {},
                                         "private_inputs": {"x": edge_values},
                                         "public_outputs": {"result": [0, *([1] * 7)]}})
        edge_package = s31.build(edge_source, work / "zero-residue", "direct-gate")
        edge_relation = json.loads((edge_package / "source.s31.json").read_text())
        if (symbolic_exponent(edge_relation, name="power_zero_residue") != P - 1 or
                len(edge_relation["nodes"]) != 37):
            raise AssertionError("zero-residue power did not keep the positive exponent")
        edge_trial = s31.trial(edge_package, edge_assignment, work / "zero-residue-trial")
        if (edge_trial["native_verifier_accepted"] is not True or
                not edge_trial["changed_public_statement_rejected"] or
                edge_trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("zero-residue native proof controls failed")
    return {"schema": "s31-power-chain-native-v2", "lanes": 8,
            "stages": 4, "exponent_per_stage": 65535,
            "fused_exponent": FUSED_EXPONENT,
            "saved_arithmetic_nodes": 81, "saved_raw_qm31_rows": 162,
            "halved_padded_rows": True, "cases": cases,
            "zero_residue": {"symbolic_exponent": P - 1, "nodes": 37,
                             "zero_input_verified": True,
                             "nonzero_input_verified": True,
                             "native_verified": True,
                             "changed_claim_rejected": True,
                             "independent_oracle_passed": True,
                             "proof_bytes": edge_trial["proof_bytes"]}}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
