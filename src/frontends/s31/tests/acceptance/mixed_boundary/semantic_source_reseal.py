#!/usr/bin/env python3
"""Reject an old mixed proof under a same-roster, semantically changed source.

The existing source-byte control adds whitespace. This independent control
changes a repeat constant, then also proves the changed program to show that
its generated verifier is live and that rejection is proof-specific.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

from source_pinned_general import MAGIC, MODULUS, build, family, run


def changed_family(count: int, changed_call: int = 0) -> tuple[dict, dict]:
    if not 0 <= changed_call < count:
        raise ValueError("changed call must be a valid source call")
    source, assignment = family(count)
    source = copy.deepcopy(source)
    assignment = copy.deepcopy(assignment)
    # Keep all names, calls, rounds and endpoints. Change one chosen call's
    # arithmetic, so a later many-chip call is testable independently.
    source["nodes"][changed_call]["body"][1]["constant"] += 1
    initial = assignment["private_inputs"]["x"]
    result = initial.copy()
    for call in range(count):
        constant = 14 + call if call == changed_call else 13 + call
        for _ in range(16):
            result = [(word * word + constant) % MODULUS for word in result]
    assignment["public_outputs"] = {
        "sum": [(word + x) % MODULUS for word, x in zip(result, initial)],
        "product": [(word * x) % MODULUS for word, x in zip(result, initial)],
    }
    return source, assignment


def exercise(work: Path, count: int, changed_call: int = 0) -> dict:
    source, assignment = family(count)
    changed_source, changed_assignment = changed_family(count, changed_call)
    source_path = work / f"original-{count}.s31.json"
    changed_path = work / f"semantic-change-{count}-call-{changed_call}.s31.json"
    source_path.write_text(json.dumps(source, separators=(",", ":")))
    changed_path.write_text(json.dumps(changed_source, separators=(",", ":")))
    assignment_path = work / f"original-{count}.assignment.json"
    changed_assignment_path = work / f"semantic-change-{count}-call-{changed_call}.assignment.json"
    assignment_path.write_text(json.dumps(assignment, separators=(",", ":")))
    changed_assignment_path.write_text(json.dumps(changed_assignment, separators=(",", ":")))

    original_prover, original_verifier, original_inspector = build(
        source_path, work / f"original-build-{count}")
    changed_prover, changed_verifier, changed_inspector = build(
        changed_path, work / f"semantic-build-{count}-call-{changed_call}")
    original_manifest = json.loads(run(str(original_inspector)).stdout)
    changed_manifest = json.loads(run(str(changed_inspector)).stdout)
    if (original_manifest["source_sha256"] != hashlib.sha256(source_path.read_bytes()).hexdigest() or
            changed_manifest["source_sha256"] != hashlib.sha256(changed_path.read_bytes()).hexdigest() or
            original_manifest["call_count"] != count or changed_manifest["call_count"] != count or
            original_manifest["slot_count"] != 1 + 2 * count or
            changed_manifest["slot_count"] != 1 + 2 * count or
            [call["constant"] for call in original_manifest["calls"]] !=
            [13 + i for i in range(count)] or
            [call["constant"] for call in changed_manifest["calls"]] !=
            [13 + i + int(i == changed_call) for i in range(count)] or
            original_manifest["source_sha256"] == changed_manifest["source_sha256"] or
            original_manifest["fixed_root"] != changed_manifest["fixed_root"] or
            original_manifest["tree_columns"] != changed_manifest["tree_columns"] or
            original_manifest["registry_manifest_sha256"] == changed_manifest["registry_manifest_sha256"]):
        raise AssertionError("native generated verifiers do not preserve the same circuit layout")
    for original_slot, changed_slot in zip(original_manifest["slots"],
                                           changed_manifest["slots"]):
        if original_slot["call_id"] == changed_call:
            if original_slot["program_binding_sha256"] == changed_slot["program_binding_sha256"]:
                raise AssertionError("changed call did not change its chip/bridge binding")
        elif original_slot["call_id"] is not None:
            if original_slot["program_binding_sha256"] != changed_slot["program_binding_sha256"]:
                raise AssertionError("unmodified call changed its chip/bridge binding")

    original_proof = work / f"original-{count}.proof"
    original_statement = work / f"original-{count}.statement.json"
    changed_proof = work / f"semantic-{count}-call-{changed_call}.proof"
    changed_statement = work / f"semantic-{count}-call-{changed_call}.statement.json"
    run(str(original_prover), str(assignment_path), str(original_proof), str(original_statement))
    run(str(original_verifier), str(original_proof), str(original_statement))
    run(str(changed_prover), str(changed_assignment_path), str(changed_proof), str(changed_statement))
    run(str(changed_verifier), str(changed_proof), str(changed_statement))
    original_claim = json.loads(original_statement.read_text())
    changed_claim = json.loads(changed_statement.read_text())
    if original_claim["public_words"] == changed_claim["public_words"]:
        raise AssertionError("semantic mutation unexpectedly left the public result unchanged")

    # Re-seal the old proof's transport identity to the new verifier. A
    # shallow source/count/envelope check can no longer explain rejection.
    resealed_claim = {
        **original_claim,
        **{key: changed_claim[key] for key in (
            "source_sha256", "selected_manifest_sha256",
            "registry_manifest_sha256", "circuit_identity_sha256")},
    }
    resealed_statement = work / f"resealed-{count}-call-{changed_call}.statement.json"
    resealed_statement.write_text(json.dumps(resealed_claim))
    old = original_proof.read_bytes()
    if old[:len(MAGIC) + 4] != MAGIC + bytes((count, 1 + 2 * count, 3, 0)):
        raise AssertionError("old proof has a different mixed transport geometry")
    resealed = bytearray(old)
    for key, offset in (("source_sha256", len(MAGIC) + 4),
                        ("registry_manifest_sha256", len(MAGIC) + 36),
                        ("circuit_identity_sha256", len(MAGIC) + 68)):
        resealed[offset:offset + 32] = bytes.fromhex(changed_claim[key])
    resealed_proof = work / f"resealed-{count}-call-{changed_call}.proof"
    resealed_proof.write_bytes(resealed)
    result = subprocess.run((str(changed_verifier), str(resealed_proof), str(resealed_statement)),
                            text=True, capture_output=True, check=False, timeout=60)
    if (result.returncode == 0 or result.returncode < 0 or
            "InvalidMixedNativeEnvelope" in result.stderr or
            "InvalidMixedPreprocessedRoot" in result.stderr or
            "InvalidMixedStatementIdentity" in result.stderr):
        raise AssertionError(
            f"semantic reseal accepted, crashed or failed only at transport identity: "
            f"exit={result.returncode}, stderr={result.stderr}")
    return {"calls": count, "changed_call": changed_call,
            "changed_call_kind": "pair" if changed_call < 2 else "many",
            "unchanged_fixed_root": original_manifest["fixed_root"],
            "original_proof_sha256": hashlib.sha256(old).hexdigest(),
            "changed_proof_sha256": hashlib.sha256(changed_proof.read_bytes()).hexdigest(),
            "resealed_rejection": result.stderr.strip().splitlines()[-1]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--counts", nargs="+", type=int, default=[1])
    parser.add_argument("--changed-call", type=int, default=0,
                        help="zero-based repeat call whose constant is changed")
    args = parser.parse_args()
    if len(set(args.counts)) != len(args.counts) or any(not 1 <= n <= 8 for n in args.counts):
        parser.error("counts must be distinct values in 1..8")
    if any(not 0 <= args.changed_call < n for n in args.counts):
        parser.error("changed call must exist in every requested profile")
    with tempfile.TemporaryDirectory(prefix="s31-mixed-semantic-reseal-") as temp:
        results = [exercise(Path(temp), count, args.changed_call) for count in args.counts]
    print(json.dumps({"schema": "s31-mixed-semantic-reseal-v1", "profiles": results}, sort_keys=True))


if __name__ == "__main__":
    main()
