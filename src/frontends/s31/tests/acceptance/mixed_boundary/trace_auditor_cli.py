#!/usr/bin/env python3
"""Black-box opt-in full-trace auditor command for a private N=2 source."""

from __future__ import annotations

import json
import hashlib
import subprocess
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
SOURCE = S31 / "examples/boundary/private_arithmetic_chip_input.s31.json"
ASSIGNMENT = S31 / "examples/boundary/private_arithmetic_chip_input.valid.json"
MODULUS = 2_147_483_647


def run(*argv: str, accept: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(argv, text=True, capture_output=True, check=False)
    if (result.returncode == 0) != accept or result.returncode < 0:
        raise AssertionError(
            f"unexpected exit {result.returncode}: {argv}\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-mixed-trace-auditor-") as temporary:
        directory = Path(temporary)
        prefix = directory / "package"
        run(
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=1",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={SOURCE}",
            "-Ds31-name=trace_audit_cli", "-j1", "--prefix", str(prefix),
        )
        binary = prefix / "bin/s31-trace_audit_cli-mixed-general"
        prover = Path(str(binary) + "-prover")
        verifier = Path(str(binary) + "-native-verifier")
        auditor = Path(str(binary) + "-trace-auditor")
        proof = directory / "proof.bin"
        statement = directory / "statement.json"
        run(str(prover), str(ASSIGNMENT), str(proof), str(statement))
        run(str(verifier), str(proof), str(statement))
        audited = run(str(auditor), str(proof), str(statement), str(ASSIGNMENT))
        reports = [line.partition(" ")[2] for line in audited.stderr.splitlines()
                   if line.startswith("S31_MIXED_TRACE_AUDIT_V2 ")]
        if len(reports) != 1:
            raise AssertionError("auditor did not print exactly one report")
        report = json.loads(reports[0])
        if (report.get("schema") != "s31-mixed-full-trace-audit-v2" or
                report.get("verified") is not True or
                report.get("circuit_rows") != 512 or
                report.get("chip_rows") != 32 or
                report.get("bridge_rows") != 32 or
                any(len(report.get(key, "")) != 64 for key in (
                    "fixed_root", "main_root", "interaction_root")) or
                report.get("source_sha256") != hashlib.sha256(SOURCE.read_bytes()).hexdigest() or
                report.get("statement_sha256") != hashlib.sha256(statement.read_bytes()).hexdigest() or
                report.get("proof_sha256") != hashlib.sha256(proof.read_bytes()).hexdigest() or
                "assignment_sha256" in report):
            raise AssertionError(f"unexpected full-trace audit report: {report}")

        changed_assignment = json.loads(ASSIGNMENT.read_text())
        changed_assignment["private_inputs"]["x"][0] = (
            changed_assignment["private_inputs"]["x"][0] + 1) % MODULUS
        changed_assignment_path = directory / "changed-assignment.json"
        changed_assignment_path.write_text(json.dumps(changed_assignment))
        bad_assignment_result = run(str(auditor), str(proof), str(statement),
                                    str(changed_assignment_path), accept=False)
        if "S31_MIXED_TRACE_AUDIT_V2 " in bad_assignment_result.stderr:
            raise AssertionError("rejected assignment emitted an accepted audit")

        changed_statement = json.loads(statement.read_text())
        changed_statement["public_words"][0] = (
            changed_statement["public_words"][0] + 1) % MODULUS
        changed_statement_path = directory / "changed-statement.json"
        changed_statement_path.write_text(json.dumps(changed_statement))
        run(str(verifier), str(proof), str(changed_statement_path), accept=False)
        bad_statement_result = run(str(auditor), str(proof),
                                   str(changed_statement_path),
                                   str(ASSIGNMENT), accept=False)
        if "S31_MIXED_TRACE_AUDIT_V2 " in bad_statement_result.stderr:
            raise AssertionError("rejected statement emitted an accepted audit")
        changed_proof = bytearray(proof.read_bytes())
        changed_proof[-1] ^= 1
        changed_proof_path = directory / "changed-proof.bin"
        changed_proof_path.write_bytes(changed_proof)
        bad_proof_result = run(str(auditor), str(changed_proof_path),
                               str(statement), str(ASSIGNMENT), accept=False)
        if "S31_MIXED_TRACE_AUDIT_V2 " in bad_proof_result.stderr:
            raise AssertionError("rejected proof emitted an accepted audit")
        print(json.dumps({"schema": "s31-mixed-trace-auditor-cli-acceptance-v1",
                          "accepted": 1, "rejected": 4,
                          "proof_bytes": proof.stat().st_size,
                          "audit": report}, sort_keys=True))


if __name__ == "__main__":
    main()
