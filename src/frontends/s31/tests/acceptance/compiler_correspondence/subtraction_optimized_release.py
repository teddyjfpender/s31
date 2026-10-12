#!/usr/bin/env python3
"""Ordered-subtraction reuse must save one gate and pass strict v3 release."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

import s31
from functional_release import SAME_AIR
from package.correspondence import (OPTIMIZED_SCHEMA, canonical_ir_bytes,
                                    check_optimized_package, parse_source,
                                    parse_source_optimized)
from package.trust import pinned_paths
from text_frontend import compile_text

EXAMPLE = S31 / "examples/functional/release_sub4"
P = (1 << 31) - 1


def run() -> dict:
    optimized_source = EXAMPLE / "optimized.s31"
    manual_source = EXAMPLE / "optimized_manual.s31"
    optimized_text = optimized_source.read_text()
    relation, syntax = parse_source_optimized(optimized_text.encode())
    _, manual_syntax = parse_source(manual_source.read_bytes())
    if (relation != compile_text(optimized_text)[0] or
            syntax["source_to_canonical"] != [0, 1, 2, 2, 3] or
            len(syntax["instructions"]) != 3 or
            len(relation["nodes"]) != 4 or
            canonical_ir_bytes(syntax) != canonical_ir_bytes(manual_syntax)):
        raise AssertionError("ordered subtraction was incorrectly shared or emitted")

    with tempfile.TemporaryDirectory(prefix="s31-sub-cse-release-") as directory:
        work = Path(directory)
        manual = s31.build(manual_source, work / "manual", "direct-gate")
        package = s31.build(optimized_source, work / "optimized", "direct-gate",
                            correspondence="optimized")
        manifest = s31.verify_package(package)
        checked = check_optimized_package(package)
        if (manifest.get("correspondence_schema") != OPTIMIZED_SCHEMA or
                checked["source_ssa"] != syntax or
                checked["status"]["native_root_binding"] !=
                "native-reported-fixed-root-matches-key"):
            raise AssertionError("ordered subtraction lacks rooted v3 correspondence")
        manual_cost = json.loads((manual / "cost-report.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
        different = [field for field in SAME_AIR if cost[field] != manual_cost[field]]
        if different or cost["raw"]["qm31_ops"] != 323 or cost["padded"]["qm31_ops"] != 512:
            raise AssertionError(f"subtraction reuse changed expected native AIR: {different}")

        values = [0, 1, 2, P - 1]
        assignment = work / "assignment.json"
        s31.write_json(assignment, {"public_inputs": {"x": values},
                                    "private_inputs": {},
                                    "public_outputs": {"result": [(-2 * x) % P for x in values]}})
        trial = s31.trial(package, assignment, work / "proof")
        if (trial["independent_value_oracle"]["status"] != "passed" or
                not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"]):
            raise AssertionError("ordered subtraction proof controls failed")
        pins = {kind: s31.file_hash(path) for kind, path in pinned_paths(package).items()}
        flags = [item for kind, digest in pins.items()
                 for item in (f"--{kind}-sha256", digest)]
        command = [sys.executable, str(S31 / "python/s31.py"), "verify-release",
                   str(package), str(work / "proof/proof.bin"), "--statement",
                   str(work / "proof/statement.json"), *flags]
        s31.invoke(*command)
        changed = command.copy()
        changed[changed.index(str(work / "proof/statement.json"))] = str(
            work / "proof/changed-statement.json")
        try:
            s31.invoke(*changed)
        except RuntimeError:
            pass
        else:
            raise AssertionError("strict release accepted a changed subtraction claim")
        return {"schema": "s31-ordered-subtraction-optimized-release-v1",
                "source_operations": len(relation["nodes"]),
                "native_arithmetic_gates": len(syntax["instructions"]),
                "raw_qm31_rows": cost["raw"]["qm31_ops"],
                "padded_qm31_rows": cost["padded"]["qm31_ops"],
                "manual_and_optimized_air_equal": True,
                "strict_release_proof_accepted": True,
                "changed_public_claim_rejected": True}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
