#!/usr/bin/env python3
"""Accepted and adversarial controls for the generic sealed Gate trace audit.

Pass a built package, its native proof and statement, and the witness JSON.
The controls keep the proof fixed while changing unused source nodes. This
tests the parser and the compiled physical topology independently of whether
the node contributes to a public output.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path

from gate_claim_trace_audit import audit
from control_claim_trace_audit import run_native


def controls(package: Path, proof: Path, statement: Path, assignment: Path) -> dict:
    accepted = audit(package, proof, statement, assignment)
    source = json.loads((package / "source.s31.json").read_text())
    if not source["nodes"]:
        raise ValueError("unused-node controls need at least one source node")
    existing = {item["name"] for item in source["inputs"] + source["nodes"]}
    name = "audit_unused_node"
    if name in existing:
        raise ValueError("reserved control name is already used")
    operand = source["nodes"][-1]["name"]
    mutations = {
        "unknown_operand": {"name": name, "op": "add_const",
                            "lhs": "audit_missing_operand", "constant": 1},
        "valid_unused_node": {"name": name, "op": "add_const",
                              "lhs": operand, "constant": 1},
    }
    with tempfile.TemporaryDirectory(prefix="s31-gate-claim-controls-") as temporary:
        source_path = Path(temporary) / "source.s31.json"
        for label, node in mutations.items():
            modified = {**source, "nodes": [*source["nodes"], node]}
            source_path.write_text(json.dumps(modified))
            try:
                run_native(source_path, assignment, proof, statement,
                           expected_counts=None)
            except ValueError as exc:
                expected = ("UnknownOperand" if label == "unknown_operand"
                            else "fixed proof root changed")
                if expected not in str(exc):
                    raise AssertionError(f"{label} rejected for unexpected reason: {exc}") from exc
                continue
            raise AssertionError(f"unchanged proof accepted {label}")
    return {"schema": "s31-gate-claim-trace-controls-v1",
            "accepted_program_sha256": accepted["program_sha256"],
            "accepted_source_nodes_mapped": accepted["source_nodes_mapped"],
            "unknown_operand_rejected": True,
            "valid_unused_node_rejected": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("package", "proof", "statement", "assignment"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    print(json.dumps(controls(args.package, args.proof, args.statement,
                              args.assignment), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
