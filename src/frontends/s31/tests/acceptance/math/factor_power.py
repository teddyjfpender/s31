#!/usr/bin/env python3
"""Compare a factor-reused static power with an explicit binary circuit."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from power_chain import symbolic_exponent  # noqa: E402

P = (1 << 31) - 1
FACTOR = 3
QUOTIENT = 65535
EXPONENT = FACTOR * QUOTIENT
STAGES = 4
FUSED_EXPONENT = (EXPONENT**STAGES - 1) % (P - 1) + 1
EXAMPLES = S31 / "examples/arithmetic/powers"
EXPECTED = {
    "factor-chain": (47, 413, 512, 4096),
    "binary": (128, 575, 1024, 8192),
}


def _binary_source() -> str:
    """Spell out left-to-right square/multiply without compiler power lowering."""
    bits = bin(EXPONENT)[3:]
    lines = ["use std@1;",
             "circuit pow_factor(private x: [m31; 8]) -> public [m31; 8] {"]
    seed = "x"
    for stage in range(STAGES):
        current = seed
        for index, bit in enumerate(bits):
            last = stage == STAGES - 1 and index == len(bits) - 1
            square = "result" if last and bit == "0" else f"s{stage}_{index}_square"
            lines.append(f"    let {square} = {current} .* {current};")
            current = square
            if bit == "1":
                added = "result" if last else f"s{stage}_{index}_add"
                lines.append(f"    let {added} = {current} .* {seed};")
                current = added
        seed = current
    lines.extend(["    result", "}"])
    return "\n".join(lines) + "\n"


def _check(kind: str, source: Path, assignment: Path, work: Path) -> dict:
    package = s31.build(source, work / kind, "direct-gate")
    relation = json.loads((package / "source.s31.json").read_text())
    expected_exponent = FUSED_EXPONENT if kind == "factor-chain" else EXPONENT**STAGES
    if symbolic_exponent(relation, name="pow_factor") != expected_exponent:
        raise AssertionError(f"{kind} has the wrong symbolic exponent")
    cost = json.loads((package / "cost-report.json").read_text())
    nodes, raw, padded, cells = EXPECTED[kind]
    zeros = {"blake_g": 0, "eq": 0, "m31_to_u32": 0, "triple_xor": 0}
    if (len(relation["nodes"]) != nodes or cost["profile"] != "direct-m31-v4" or
            cost["raw"] != {**zeros, "qm31_ops": raw} or
            cost["padded"] != {**zeros, "qm31_ops": padded} or
            cost["preprocessed_cells"] != cells):
        raise AssertionError(f"{kind} native AIR geometry changed")
    trial = s31.trial(package, assignment, work / f"{kind}-trial")
    if (trial["native_verifier_accepted"] is not True or
            trial["changed_public_statement_rejected"] != "public_outputs.result[0]" or
            trial["independent_value_oracle"]["status"] != "passed" or
            trial["proof_bytes"] <= 0):
        raise AssertionError(f"{kind} native proof controls failed")
    return {"kind": kind, "nodes": nodes, "raw_qm31_rows": raw,
            "padded_qm31_rows": padded, "preprocessed_cells": cells,
            "proof_bytes": trial["proof_bytes"],
            "native_verified": True, "changed_claim_rejected": True,
            "independent_oracle_passed": True, "symbolic_exponent_checked": True}


def run() -> dict:
    assignment = EXAMPLES / "pow196605_factor4.valid.json"
    data = json.loads(assignment.read_text())
    values = data["private_inputs"]["x"]
    if (type(values) is not list or len(values) != 8 or
            any(type(word) is not int or not 0 <= word < P for word in values) or
            data["public_inputs"] != {} or
            data["public_outputs"] != {
                "result": [pow(word, EXPONENT**STAGES, P) for word in values]}):
        raise AssertionError("factor-power assignment differs from modular arithmetic")

    binary_source = _binary_source()
    with tempfile.TemporaryDirectory(prefix="s31-factor-power-") as directory:
        work = Path(directory)
        binary = work / "binary.s31"
        binary.write_text(binary_source)
        cases = [
            _check("factor-chain", EXAMPLES / "pow196605_factor4.s31", assignment, work),
            _check("binary", binary, assignment, work),
        ]
    return {"schema": "s31-factor-power-native-v2", "lanes": 8,
            "stages": STAGES, "exponent_per_stage": EXPONENT,
            "fused_exponent": FUSED_EXPONENT,
            "binary_source_sha256": hashlib.sha256(binary_source.encode()).hexdigest(),
            "saved_arithmetic_nodes": 81, "saved_raw_qm31_rows": 162,
            "halved_padded_rows": True, "cases": cases}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
