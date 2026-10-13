#!/usr/bin/env python3
"""Exact AIR-cost and native proof gate for complete runtime array views."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import evaluate_relation
from text_frontend import compile_file


GEOMETRY = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)


def main() -> None:
    example = S31 / "examples/functional/reshape_flatten_zero_cost"
    assignment = json.loads((example / "valid.json").read_text())
    relations = {name: compile_file(example / f"{name}.s31")[0]
                 for name in ("functional", "direct", "expanded")}
    if relations["functional"] != relations["direct"]:
        raise AssertionError("reshape/flatten did not erase to the direct relation")
    if [(node["op"], node.get("index")) for node in relations["functional"]["nodes"]] != [
        ("array_get", 3)
    ]:
        raise AssertionError("functional circuit emitted unexpected view nodes")
    if not any(node["op"] == "array_concat" for node in relations["expanded"]["nodes"]):
        raise AssertionError("expanded cost reference lost its explicit views")
    if [assignment["private_inputs"]["x"][3]] != assignment["public_outputs"]["result"]:
        raise AssertionError("independent selection fixture changed")
    for relation in relations.values():
        if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
            raise AssertionError("value semantics changed")

    with tempfile.TemporaryDirectory(prefix="s31-reshape-zero-cost-") as temporary:
        work = Path(temporary)
        packages = {name: s31.build(example / f"{name}.s31", work / name, "direct-gate")
                    for name in relations}
        costs = {name: json.loads((package / "cost-report.json").read_text())
                 for name, package in packages.items()}
        mismatch = [field for field in GEOMETRY
                    if costs["functional"][field] != costs["direct"][field]]
        if mismatch:
            raise AssertionError(f"functional view changed direct AIR geometry: {mismatch}")
        functional_rows = costs["functional"]["raw"]["qm31_ops"]
        expanded_rows = costs["expanded"]["raw"]["qm31_ops"]
        if not functional_rows < expanded_rows:
            raise AssertionError("complete view did not remove packed circuit gates")
        trials = {name: s31.trial(packages[name], example / "valid.json", work / f"{name}-trial")
                  for name in ("functional", "direct")}
        for name, trial in trials.items():
            if (not trial["native_verifier_accepted"] or
                    not trial["changed_public_statement_rejected"] or
                    trial["independent_value_oracle"]["status"] != "passed"):
                raise AssertionError(f"{name} native proof or oracle control failed")
        print(json.dumps({
            "schema": "s31-reshape-flatten-zero-cost-v1",
            "same_normalized_relation": True,
            "same_air_fields": list(GEOMETRY),
            "raw_qm31_rows": {name: costs[name]["raw"]["qm31_ops"] for name in costs},
            "padded_qm31_rows": {name: costs[name]["padded"]["qm31_ops"] for name in costs},
            "preprocessed_cells": costs["functional"]["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
