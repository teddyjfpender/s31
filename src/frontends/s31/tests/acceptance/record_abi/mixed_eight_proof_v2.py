#!/usr/bin/env python3
"""Admit the exact eight-word text/Lean record fixture to a native mixed proof."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

from mixed_eight_lean_correspondence_v2 import (S31, SOURCE, STATEMENT,
                                                 canonical, valid_case)


def run(*args: str, ok: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, capture_output=True, text=True, check=False)
    if (result.returncode == 0) != ok:
        raise AssertionError(f"exit {result.returncode}: {args}\n{result.stderr}")
    if not ok and (result.returncode != 1 or "error:" not in result.stderr or
                   "panic:" in result.stderr):
        raise AssertionError(f"unclean rejection: {args}\n{result.stderr}")
    return result


def changed_statement(base: dict, changed: list[tuple[int, int, int]]) -> bytes:
    result = copy.deepcopy(base)
    for leaf, lane, word in changed:
        result["leaves"][leaf]["words"][lane] = word
    return canonical(result)


def main() -> None:
    source, source_bytes, _, typed, _, expected = valid_case()
    if SOURCE.read_bytes() != source_bytes or STATEMENT.read_bytes() != typed:
        raise AssertionError("proof fixture drifted from byte-pinned text and statement")
    y = expected[4:]
    assignment = {
        "public_inputs": {"_s31_abi_input_0": [1],
                          "_s31_abi_input_1": [5, 6]},
        "private_inputs": {"x": [1, 2, 3, 4]},
        "public_outputs": {"_s31_abi_input_0": [1], "y": y},
    }
    with tempfile.TemporaryDirectory(prefix="s31-mixed-eight-v2-proof-") as temporary:
        work = Path(temporary)
        prefix = work / "package"
        assignment_path = work / "assignment.json"
        assignment_path.write_bytes(canonical(assignment))
        run("zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={SOURCE}",
            "-Ds31-name=mixed_eight_alias_bit", "-j1", "--prefix", str(prefix))
        binaries = prefix / "bin"
        prover = binaries / "s31-mixed_eight_alias_bit-mixed-general-prover"
        verifier = binaries / "s31-mixed_eight_alias_bit-mixed-general-native-verifier"
        auditor = binaries / "s31-mixed_eight_alias_bit-mixed-general-trace-auditor"
        manifest = json.loads(run(str(binaries /
                                  "s31-mixed_eight_alias_bit-mixed-general-manifest")).stdout)
        if (manifest["source_sha256"] != hashlib.sha256(source_bytes).hexdigest() or
                manifest["call_count"] != 1 or manifest["slot_count"] != 3):
            raise AssertionError("the native schedule did not seal this source and one call")
        proof = work / "proof.bin"
        statement = work / "statement.json"
        run(str(prover), str(assignment_path), str(proof), str(statement), str(STATEMENT))
        if statement.read_bytes() != typed:
            raise AssertionError("prover did not preserve the exact canonical v2 statement")
        run(str(verifier), str(proof), str(statement))
        audit_result = run(str(auditor), str(proof), str(statement),
                           str(assignment_path))
        audit_lines = [line.removeprefix("S31_MIXED_TRACE_AUDIT_V1 ")
                       for line in audit_result.stderr.splitlines()
                       if line.startswith("S31_MIXED_TRACE_AUDIT_V1 ")]
        if len(audit_lines) != 1:
            raise AssertionError(f"missing v2 trace audit report: {audit_result.stderr}")
        audit = json.loads(audit_lines[0])
        if (audit["schema"] != "s31-mixed-full-trace-audit-v1" or
                audit["verified"] is not True or
                (audit["circuit_rows"], audit["chip_rows"], audit["bridge_rows"]) !=
                (512, 16, 16)):
            raise AssertionError(f"unexpected v2 trace audit geometry: {audit}")
        for root in ("fixed_root", "main_root", "interaction_root"):
            if len(audit[root]) != 64 or any(c not in "0123456789abcdef" for c in audit[root]):
                raise AssertionError(f"invalid {root} in v2 trace audit report")

        honest = json.loads(typed)
        valid_changes = {
            "public_bit_and_result_alias": [(0, 0, 0), (2, 0, 0)],
            "unused_public_salt": [(1, 0, 7)],
            "chip_result_and_repeat_alias": [(3, 2, (y[2] + 1) % (2**31 - 1)),
                                             (4, 2, (y[2] + 1) % (2**31 - 1))],
        }
        changed_errors = {}
        for label, changes in valid_changes.items():
            path = work / f"changed-{label}.json"
            path.write_bytes(changed_statement(honest, changes))
            rejected = run(str(verifier), str(proof), str(path), ok=False)
            if "InvalidRecordStatement" in rejected.stderr:
                raise AssertionError(f"{label}: valid changed claim stopped in ABI parser")
            changed_errors[label] = rejected.stderr.strip().splitlines()[-1]
            if label == "unused_public_salt":
                audited_rejection = run(str(auditor), str(proof), str(path),
                                        str(assignment_path), ok=False)
                if "S31_MIXED_TRACE_AUDIT_V1 " in audited_rejection.stderr:
                    raise AssertionError("auditor reported verified for changed v2 statement")

        malformed = {
            "split_public_bit_alias": [(2, 0, 0)],
            "split_chip_result_alias": [(4, 2, (y[2] + 1) % (2**31 - 1))],
            "non_bit_public_claim": [(0, 0, 2), (2, 0, 2)],
        }
        for label, changes in malformed.items():
            path = work / f"malformed-{label}.json"
            path.write_bytes(changed_statement(honest, changes))
            rejected = run(str(verifier), str(proof), str(path), ok=False)
            if "InvalidRecordStatement" not in rejected.stderr:
                raise AssertionError(f"{label}: expected ABI rejection: {rejected.stderr}")

        wrong_layout = copy.deepcopy(honest)
        wrong_layout["leaves"][1]["path"][1]["field"] = "pepper"
        path = work / "wrong-record-field.json"
        path.write_bytes(canonical(wrong_layout))
        rejected = run(str(verifier), str(proof), str(path), ok=False)
        if "InvalidRecordStatement" not in rejected.stderr:
            raise AssertionError(f"record field mutation missed ABI parser: {rejected.stderr}")

        wrong_private = copy.deepcopy(assignment)
        wrong_private["private_inputs"]["x"][0] = 9
        path = work / "wrong-private.json"
        path.write_bytes(canonical(wrong_private))
        run(str(prover), str(path), str(work / "wrong-private.proof"),
            str(work / "wrong-private.statement"), str(STATEMENT), ok=False)
        audited_rejection = run(str(auditor), str(proof), str(statement),
                                str(path), ok=False)
        if "S31_MIXED_TRACE_AUDIT_V1 " in audited_rejection.stderr:
            raise AssertionError("auditor reported verified for changed private witness")

        print(json.dumps({
            "schema": "s31-mixed-eight-record-proof-v2",
            "source_sha256": manifest["source_sha256"],
            "proof_bytes": proof.stat().st_size,
            "public_words": expected,
            "verified": True,
            "trace_audit": audit,
            "trace_auditor_changed_statement_rejected": True,
            "trace_auditor_changed_private_witness_rejected": True,
            "abi_valid_changed_claim_rejections": changed_errors,
            "malformed_alias_bit_layout_rejections": len(malformed) + 1,
            "private_witness_mismatch_rejected": True,
        }, sort_keys=True))


if __name__ == "__main__":
    main()
