#!/usr/bin/env python3
"""Accepted and adversarial controls for the generic sealed Gate trace audit.

Pass a built package, its native proof and statement, and the witness JSON.
The controls keep the proof fixed while changing unused source nodes. This
tests the parser and the compiled physical topology independently of whether
the node contributes to a public output.
"""

from __future__ import annotations

import argparse
import copy
import json
import tempfile
from pathlib import Path

from gate_claim_trace_audit import audit
from control_claim_trace_audit import run_native
from gate_source_physical_certificate import validate as validate_physical_certificate


def controls(package: Path, proof: Path, statement: Path, assignment: Path) -> dict:
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
        certificate_path = Path(temporary) / "certificate.json"
        accepted = audit(package, proof, statement, assignment,
                         certificate=certificate_path)
        certificate = json.loads(certificate_path.read_text())
        manifest = json.loads((package / "manifest.json").read_text())
        key = json.loads((package / "verification-key.json").read_text())
        report = json.loads((package / "cost-report.json").read_text())
        receipt = {"source_nodes_mapped": accepted["source_nodes_mapped"],
                   "source_qm31_rows": accepted["source_qm31_rows"],
                   "physical_certificate_sha256": accepted["physical_certificate_sha256"]}
        validate_physical_certificate(certificate, source, manifest, key, report,
                                      receipt, certificate_bytes=certificate_path.read_bytes())
        def other_add_const_address(c: dict) -> int:
            current = c["add_const_compositions"][0]["constant_address"]
            return current - 1 if current > 0 else 1

        def change_address_and_physical_in1(c: dict) -> None:
            address = other_add_const_address(c)
            c["add_const_compositions"][0]["constant_address"] = address
            c["add_const_compositions"][0]["physical_in1"] = address

        certificate_mutations = [
                ("wrong_fixed_root", lambda c: c.__setitem__("preprocessed_root", "0" * 64)),
                ("missing_source", lambda c: c["source_map"].pop()),
                ("wrong_row_interval", lambda c: c["source_map"][-1]["add"].__setitem__(
                    "end", c["source_map"][-1]["add"]["end"] + 1)),
        ]
        if certificate["add_const_compositions"]:
            certificate_mutations.extend((
                ("wrong_add_const_value", lambda c: c["add_const_compositions"][0].__setitem__(
                    "constant", c["add_const_compositions"][0]["constant"] + 1)),
                ("out_of_range_add_const_address", lambda c: c["add_const_compositions"][0].__setitem__(
                    "constant_address", c["n_vars"])),
                ("in_range_add_const_address", lambda c: c["add_const_compositions"][0].__setitem__(
                    "constant_address", other_add_const_address(c))),
                ("in_range_add_const_address_and_in1", change_address_and_physical_in1),
                ("wrong_add_const_input", lambda c: c["add_const_compositions"][0][
                    "lhs_packed_outputs"].__setitem__(0, c["n_vars"])),
                ("wrong_add_const_row_count", lambda c: c["add_const_compositions"][0][
                    "add"].__setitem__("end", c["add_const_compositions"][0]["add"]["end"] + 1)),
            ))
        for label, change in certificate_mutations:
            altered = copy.deepcopy(certificate)
            change(altered)
            try:
                validate_physical_certificate(altered, source, manifest, key,
                                              report, receipt,
                                              certificate_bytes=json.dumps(altered, separators=(",", ":")).encode())
            except (ValueError, KeyError, TypeError) as exc:
                if (label == "in_range_add_const_address" and
                        "add_const physical ports differ" not in str(exc)):
                    raise AssertionError("in-range constant edit rejected for the wrong reason") from exc
                if (label == "in_range_add_const_address_and_in1" and
                        "bytes differ from native checked receipt" not in str(exc)):
                    raise AssertionError("joint in-range constant edit rejected for the wrong reason") from exc
            else:
                raise AssertionError(f"physical certificate accepted {label}")
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
        add_const_source_rejected = False
        if certificate["add_const_compositions"]:
            owner = certificate["add_const_compositions"][0]["canonical_id"]
            aliases = {entry["name"] for entry in certificate["source_map"]
                       if entry["canonical_id"] == owner}
            changed = copy.deepcopy(source)
            target = next(node for node in changed["nodes"]
                          if node["name"] in aliases and node["op"] == "add_const")
            target["constant"] += 1
            source_path.write_text(json.dumps(changed))
            try:
                run_native(source_path, assignment, proof, statement,
                           expected_counts=None)
            except ValueError:
                add_const_source_rejected = True
            else:
                raise AssertionError("unchanged proof accepted changed add_const source")
    return {"schema": "s31-gate-claim-trace-controls-v1",
            "accepted_program_sha256": accepted["program_sha256"],
            "accepted_source_nodes_mapped": accepted["source_nodes_mapped"],
            "accepted_source_qm31_rows": accepted["source_qm31_rows"],
            "physical_certificate_mutants_rejected": len(certificate_mutations),
            "in_range_add_const_address_rejected": bool(certificate["add_const_compositions"]),
            "joint_in_range_address_edit_rejected": bool(certificate["add_const_compositions"]),
            "changed_add_const_source_rejected": add_const_source_rejected,
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
