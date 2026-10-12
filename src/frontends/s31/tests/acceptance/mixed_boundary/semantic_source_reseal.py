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


def changed_family(count: int) -> tuple[dict, dict]:
    source, assignment = family(count)
    source = copy.deepcopy(source)
    assignment = copy.deepcopy(assignment)
    # Keep all names, calls, rounds and endpoints. Only source arithmetic
    # changes; the first repeat's constant is one greater.
    source["nodes"][0]["body"][1]["constant"] += 1
    initial = assignment["private_inputs"]["x"]
    result = initial.copy()
    for call in range(count):
        constant = 14 if call == 0 else 13 + call
        for _ in range(16):
            result = [(word * word + constant) % MODULUS for word in result]
    assignment["public_outputs"] = {
        "sum": [(word + x) % MODULUS for word, x in zip(result, initial)],
        "product": [(word * x) % MODULUS for word, x in zip(result, initial)],
    }
    return source, assignment


def exercise(work: Path, count: int) -> dict:
    source, assignment = family(count)
    changed_source, changed_assignment = changed_family(count)
    source_path = work / f"original-{count}.s31.json"
    changed_path = work / f"semantic-change-{count}.s31.json"
    source_path.write_text(json.dumps(source, separators=(",", ":")))
    changed_path.write_text(json.dumps(changed_source, separators=(",", ":")))
    assignment_path = work / f"original-{count}.assignment.json"
    changed_assignment_path = work / f"semantic-change-{count}.assignment.json"
    assignment_path.write_text(json.dumps(assignment, separators=(",", ":")))
    changed_assignment_path.write_text(json.dumps(changed_assignment, separators=(",", ":")))

    original_prover, original_verifier, original_inspector = build(
        source_path, work / f"original-build-{count}")
    changed_prover, changed_verifier, changed_inspector = build(
        changed_path, work / f"semantic-build-{count}")
    original_manifest = json.loads(run(str(original_inspector)).stdout)
    changed_manifest = json.loads(run(str(changed_inspector)).stdout)
    if (original_manifest["source_sha256"] != hashlib.sha256(source_path.read_bytes()).hexdigest() or
            changed_manifest["source_sha256"] != hashlib.sha256(changed_path.read_bytes()).hexdigest() or
            original_manifest["call_count"] != count or changed_manifest["call_count"] != count or
            original_manifest["slot_count"] != 1 + 2 * count or
            changed_manifest["slot_count"] != 1 + 2 * count or
            original_manifest["calls"][0]["constant"] != 13 or
            changed_manifest["calls"][0]["constant"] != 14 or
            original_manifest["source_sha256"] == changed_manifest["source_sha256"] or
            original_manifest["registry_manifest_sha256"] == changed_manifest["registry_manifest_sha256"]):
        raise AssertionError("native generated verifiers do not represent distinct same-count arithmetic")

    original_proof = work / f"original-{count}.proof"
    original_statement = work / f"original-{count}.statement.json"
    changed_proof = work / f"semantic-{count}.proof"
    changed_statement = work / f"semantic-{count}.statement.json"
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
    resealed_statement = work / f"resealed-{count}.statement.json"
    resealed_statement.write_text(json.dumps(resealed_claim))
    old = original_proof.read_bytes()
    if old[:len(MAGIC) + 4] != MAGIC + bytes((count, 1 + 2 * count, 3, 0)):
        raise AssertionError("old proof has a different mixed transport geometry")
    resealed = bytearray(old)
    for key, offset in (("source_sha256", len(MAGIC) + 4),
                        ("registry_manifest_sha256", len(MAGIC) + 36),
                        ("circuit_identity_sha256", len(MAGIC) + 68)):
        resealed[offset:offset + 32] = bytes.fromhex(changed_claim[key])
    resealed_proof = work / f"resealed-{count}.proof"
    resealed_proof.write_bytes(resealed)
    result = subprocess.run((str(changed_verifier), str(resealed_proof), str(resealed_statement)),
                            text=True, capture_output=True, check=False, timeout=60)
    if (result.returncode == 0 or result.returncode < 0 or
            "InvalidMixedNativeEnvelope" in result.stderr or
            "InvalidMixedStatementIdentity" in result.stderr):
        raise AssertionError(
            f"semantic reseal accepted, crashed or failed only at transport identity: "
            f"exit={result.returncode}, stderr={result.stderr}")
    return {"calls": count, "original_proof_sha256": hashlib.sha256(old).hexdigest(),
            "changed_proof_sha256": hashlib.sha256(changed_proof.read_bytes()).hexdigest(),
            "resealed_rejection": result.stderr.strip().splitlines()[-1]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--counts", nargs="+", type=int, default=[1])
    args = parser.parse_args()
    if len(set(args.counts)) != len(args.counts) or any(not 1 <= n <= 8 for n in args.counts):
        parser.error("counts must be distinct values in 1..8")
    with tempfile.TemporaryDirectory(prefix="s31-mixed-semantic-reseal-") as temp:
        results = [exercise(Path(temp), count) for count in args.counts]
    print(json.dumps({"schema": "s31-mixed-semantic-reseal-v1", "profiles": results}, sort_keys=True))


if __name__ == "__main__":
    main()
