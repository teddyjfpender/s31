#!/usr/bin/env python3
"""Prove static enum effect staging adds no direct-Gate circuit or AIR work."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from text_frontend import SourceError, compile_file, compile_text  # noqa: E402

P = (1 << 31) - 1
EXAMPLE = S31 / "examples/functional/static_enum_if"
COST_FIELDS = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY = {
    "profile": "direct-m31-v4",
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 280, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}


def _must_reject(source: str, reason: str) -> None:
    try:
        compile_text(source)
    except SourceError as exc:
        if reason not in str(exc):
            raise AssertionError(f"wrong static enum effect diagnostic: {exc}") from exc
    else:
        raise AssertionError("a selected or eager partial enum operation was admitted")


def run() -> dict:
    functional = EXAMPLE / "functional.s31"
    manual = EXAMPLE / "manual.s31"
    source = functional.read_text()
    wrapped, wrapped_map = compile_file(functional)
    direct, _ = compile_file(manual)
    if wrapped != direct or [node["op"] for node in wrapped["nodes"]] != ["add", "select"]:
        raise AssertionError("static enum and helper did not erase to the direct selector")
    if set(wrapped_map) != {node["name"] for node in wrapped["nodes"]}:
        raise AssertionError("source map still contains an erased enum arm")
    _must_reject(source.replace("Choice::Safe(x)", "Choice::Risky(x)"),
                 "if branch may fail when inactive: std::math::inv")
    _must_reject(source.replace("Choice::Safe(x)",
                                "Choice::Safe(std::math::inv(x))"),
                 "if branch may fail when inactive: std::math::inv")

    with tempfile.TemporaryDirectory(prefix="s31-static-enum-if-") as directory:
        work = Path(directory)
        functional_package = s31.build(functional, work / "functional", "direct-gate")
        manual_package = s31.build(manual, work / "manual", "direct-gate")
        cost = json.loads((functional_package / "cost-report.json").read_text())
        manual_cost = json.loads((manual_package / "cost-report.json").read_text())
        mismatch = [field for field in COST_FIELDS if cost[field] != manual_cost[field]]
        if mismatch:
            raise AssertionError(f"static enum syntax changed native AIR geometry: {mismatch}")
        changed = [field for field, expected in EXPECTED_GEOMETRY.items()
                   if cost[field] != expected]
        if changed:
            raise AssertionError(f"static enum selector AIR baseline changed: {changed}")

        proofs: list[dict[str, int | bool]] = []
        for name in ("valid", "alternate.valid", "zero.valid"):
            assignment_path = EXAMPLE / f"{name}.json"
            assignment = json.loads(assignment_path.read_text())
            flag = assignment["public_inputs"]["flag"][0]
            x = assignment["private_inputs"]["x"][0]
            if type(flag) is not int or flag not in (0, 1) or type(x) is not int or not 0 <= x < P:
                raise AssertionError(f"{name} has invalid canonical input words")
            expected = (x * (1 + flag)) % P
            if assignment["public_outputs"] != {"result": [expected]}:
                raise AssertionError(f"{name} differs from independent M31 arithmetic")
            trial = s31.trial(functional_package, assignment_path, work / name)
            if (not trial["native_verifier_accepted"] or
                    not trial["changed_public_statement_rejected"] or
                    trial["independent_value_oracle"]["status"] != "passed"):
                raise AssertionError(f"native proof or changed-claim rejection failed: {name}")
            proofs.append({"flag": flag, "x": x,
                           "proof_bytes": trial["proof_bytes"],
                           "native_verified": True,
                           "changed_claim_rejected": True,
                           "oracle_passed": True})

        return {"schema": "s31-static-enum-if-acceptance-v1",
                "canonical_ir_sha256": cost["canonical_ir_sha256"],
                "profile": cost["profile"], "raw": cost["raw"],
                "padded": cost["padded"],
                "preprocessed_cells": cost["preprocessed_cells"],
                "equal_relation_and_air": True,
                "selected_and_eager_partial_arms_rejected": True,
                "proofs": proofs}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
