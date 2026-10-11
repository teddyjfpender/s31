#!/usr/bin/env python3
"""Independent arithmetic control for the three admitted private chip examples.

This checks the hand-derived coordinate change against the normalized source
steps and claimed output. It does not inspect AIR constraints or prove STARK
soundness; native package acceptance is a separate gate.
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
FIXTURES = ROOT / "src/frontends/s31/examples/boundary"
P = (1 << 31) - 1

# Hand-derived s = q*x + r, s' = s² + k. These are intentionally independent
# of the compiler's ChipSpec extraction routine.
CASES = {
    "private_step16": (1, 0, 13),
    "private_add_square16": (1, 13, 13),
    "private_affine_square16": (63, 105, 798),
}


def source_step(value: int, body: list[dict]) -> int:
    for step in body:
        operation = step["op"]
        if operation == "square":
            value = value * value % P
        elif operation == "add_const":
            value = (value + step["constant"]) % P
        elif operation == "mul_const":
            value = value * step["constant"] % P
        else:
            raise AssertionError(f"unexpected chip source operation: {operation}")
    return value


def check_case(name: str, q: int, r: int, k: int) -> None:
    source = json.loads((FIXTURES / f"{name}.s31.json").read_text())
    assignment = json.loads((FIXTURES / f"{name}.valid.json").read_text())
    node = source["nodes"][0]
    rounds = node["rounds"]
    body = node["body"]
    assert rounds == 16 and q != 0
    inverse_q = pow(q, -1, P)
    inputs = [0, 1, 3, 5, 7, 11, P - 1]
    for original in inputs:
        direct = original
        transformed = (q * original + r) % P
        for _ in range(rounds):
            direct = source_step(direct, body)
            transformed = (transformed * transformed + k) % P
            recovered = (transformed - r) * inverse_q % P
            assert recovered == direct, (name, original, direct, recovered)
    private = assignment["private_inputs"]["secret"]
    outputs = []
    for original in private:
        for _ in range(rounds):
            original = source_step(original, body)
        outputs.append(original)
    assert sum(outputs) % P == assignment["public_outputs"]["total"][0]


def main() -> None:
    for name, (q, r, k) in CASES.items():
        check_case(name, q, r, k)
    print(json.dumps({"field": "M31", "cases": len(CASES), "samples_per_case": 7,
                      "rounds_per_sample": 16, "result": "matched"}, sort_keys=True))


if __name__ == "__main__":
    main()
