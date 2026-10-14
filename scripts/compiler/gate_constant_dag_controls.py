#!/usr/bin/env python3
"""Prove and audit source-derived finalization DAGs across the M31 range."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from gate_claim_trace_audit import audit
from gate_source_physical_certificate import validate as validate_certificate

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / "src/frontends/s31/python/s31.py"
SOURCE = ROOT / "scripts/compiler/fixtures/physical_add_const.s31.json"
ASSIGNMENT = ROOT / "scripts/compiler/fixtures/physical_add_const.valid.json"
P = 2147483647
CASES = (1, 7, 255, 256, 65535, P - 1)


def command(*args: str) -> None:
    result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                            check=False, timeout=240)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stderr[-1600:]}")


def run_case(constant: int, root: Path) -> dict[str, int]:
    source = copy.deepcopy(json.loads(SOURCE.read_text()))
    source["name"] = f"physical_add_const_{constant}"
    for node in source["nodes"]:
        node["constant"] = constant
    assignment = copy.deepcopy(json.loads(ASSIGNMENT.read_text()))
    assignment["public_outputs"]["shifted"] = [
        (value + constant) % P for value in assignment["private_inputs"]["a"]]
    source_path, assignment_path = root / "source.s31.json", root / "assignment.json"
    package, proof, certificate = root / "package", root / "proof.bin", root / "certificate.json"
    source_path.write_text(json.dumps(source, separators=(",", ":")))
    assignment_path.write_text(json.dumps(assignment, separators=(",", ":")))
    command(sys.executable, str(CLI), "build", str(source_path), "--out", str(package),
            "--lowering", "gate")
    command(sys.executable, str(CLI), "prove", str(package), str(assignment_path), str(proof))
    result = audit(package, proof, Path(str(proof) + ".statement.json"), assignment_path,
                   certificate=certificate)
    checked = json.loads(certificate.read_text())
    path = checked["constant_finalizations"]
    if (result["constant_finalizations_checked"] != 1 or len(path) != 1 or
            path[0]["constant"] != constant or not path[0]["steps"] or
            path[0]["steps"][-1]["out"] != path[0]["constant_address"]):
        raise AssertionError("accepted source constant lacks a complete native DAG")
    # The independent Python evaluator rejects a changed value or edge even
    # when the mutation keeps all addresses in range. This calls the same
    # strict validator used by package audits with the original native receipt.
    manifest = json.loads((package / "manifest.json").read_text())
    key = json.loads((package / "verification-key.json").read_text())
    report = json.loads((package / "cost-report.json").read_text())
    receipt = {"source_nodes_mapped": result["source_nodes_mapped"],
               "source_qm31_rows": result["source_qm31_rows"],
               "physical_certificate_sha256": result["physical_certificate_sha256"]}
    for label, change in (
            ("value", lambda c: c["constant_finalizations"][0].__setitem__(
                "constant", (constant + 1) % P)),
            ("edge", lambda c: c["constant_finalizations"][0]["steps"][-1].__setitem__(
                "in0", 0)),
            ("missing", lambda c: c["constant_finalizations"][0]["steps"].pop()),
    ):
        mutant = copy.deepcopy(checked)
        change(mutant)
        mutant_bytes = json.dumps(mutant, separators=(",", ":")).encode()
        # Forge a test-only receipt so rejection must come from the independent
        # DAG evaluator rather than the native byte digest.
        mutant_receipt = {**receipt, "physical_certificate_sha256":
                          hashlib.sha256(mutant_bytes).hexdigest()}
        try:
            validate_certificate(mutant, source, manifest, key, report,
                                 mutant_receipt, certificate_bytes=mutant_bytes)
        except ValueError as exc:
            if "bytes differ from native checked receipt" in str(exc):
                raise AssertionError(f"{label} rejected only by byte digest") from exc
        else:
            raise AssertionError(f"accepted {label} DAG mutation for constant {constant}")
    return {"constant": constant, "dag_rows": len(path[0]["steps"]) + 3,
            "physical_add_rows": checked["add_const_compositions"][0]["add"]["end"] -
            checked["add_const_compositions"][0]["add"]["start"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--constant", type=int, action="append",
                        help="run one or more canonical M31 constants (default: boundary suite)")
    args = parser.parse_args()
    constants = args.constant or CASES
    if any(not 0 < constant < P for constant in constants):
        raise ValueError("controls require canonical nonzero M31 constants")
    with tempfile.TemporaryDirectory(prefix="s31-constant-dag-") as temporary:
        root = Path(temporary)
        results = []
        for constant in constants:
            case = root / str(constant)
            case.mkdir()
            results.append(run_case(constant, case))
            print(f"checked add_const {constant}: {results[-1]['dag_rows']} DAG rows",
                  file=sys.stderr, flush=True)
    print(json.dumps({"schema": "s31-gate-constant-dag-controls-v1",
                      "cases": results, "mutants_rejected_per_case": 3},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
