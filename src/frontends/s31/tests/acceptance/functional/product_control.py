#!/usr/bin/env python3
"""Native gate for zero-cost whole-record selection under public ABI v2."""

from __future__ import annotations

import json
import contextlib
import io
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from cli.commands import dispatch
from cli.parser import make_parser
from package.trust import pinned_paths
from text_frontend import compile_file


MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY = {
    "profile": "direct-m31-v4",
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 299, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
}


def main() -> None:
    source = S31 / "examples/control/record_choice.s31"
    manual = source.with_name("record_choice_manual.s31")
    selected, _ = compile_file(source)
    explicit, _ = compile_file(manual)
    if selected != explicit:
        raise AssertionError("whole-record selection changed the normalized relation")
    if [node["op"] for node in selected["nodes"]] != [
        "is_zero", "add", "add", "select", "select", "select"
    ]:
        raise AssertionError("unexpected record-selection relation")

    with tempfile.TemporaryDirectory(prefix="s31-product-control-") as temporary:
        work = Path(temporary)
        packages = {
            "product": s31.build(source, work / "product", "direct-gate"),
            "fieldwise": s31.build(manual, work / "fieldwise", "direct-gate"),
        }
        costs = {name: json.loads((package / "cost-report.json").read_text())
                 for name, package in packages.items()}
        for field in MATCHED_COST:
            if costs["product"][field] != costs["fieldwise"][field]:
                raise AssertionError(f"product selection changed {field}")
        for field, expected in EXPECTED_GEOMETRY.items():
            if costs["product"][field] != expected:
                raise AssertionError(f"record selection changed {field} baseline")

        assignments = [source.with_suffix(".valid.json")]
        alternate = work / "record_choice.alternate.valid.json"
        alternate.write_text(json.dumps({
            "version": 2, "public_inputs": {},
            "private_inputs": {"x": [3], "y": [7]},
            "result": {"first": [14], "nested": [[7], [3]]},
        }, sort_keys=True) + "\n")
        assignments.append(alternate)
        reports = []
        for index, assignment in enumerate(assignments):
            report = s31.trial(packages["product"], assignment, work / f"trial-{index}")
            if (not report["native_verifier_accepted"] or
                    not report["changed_public_statement_rejected"] or
                    report["independent_value_oracle"]["status"] != "passed"):
                raise AssertionError(f"record selection failed native trial {index}")
            reports.append({"selector": 1 if index == 0 else 0,
                            "proof_bytes": report["proof_bytes"]})
        package = packages["product"]
        first_trial = work / "trial-0"
        pinned_args = ["verify-pinned", str(package),
                       str(first_trial / "proof.bin"),
                       "--statement", str(first_trial / "statement.json")]
        for kind, path in pinned_paths(package).items():
            pinned_args.extend((f"--{kind}-sha256", s31.file_hash(path)))
        with contextlib.redirect_stdout(io.StringIO()) as native_output:
            dispatch(make_parser().parse_args(pinned_args))
        if not native_output.getvalue().strip():
            raise AssertionError("externally pinned native verifier produced no acceptance")
        print(json.dumps({
            "schema": "s31-functional-product-control-acceptance-v1",
            "same_normalized_relation": True,
            "same_cost_fields": list(MATCHED_COST),
            "raw": costs["product"]["raw"],
            "padded": costs["product"]["padded"],
            "trials": reports,
            "externally_pinned_verification": True,
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
