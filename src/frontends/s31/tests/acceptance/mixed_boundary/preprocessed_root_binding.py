#!/usr/bin/env python3
"""Reject a well-formed mixed proof carrying another source's fixed PCS root.

The proof header does not carry the preprocessed commitment. This test changes
only commitment slot zero in the postcard body, after checking that its bytes
equal the root separately reported by the source-derived inspector.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

from source_pinned_general import MAGIC, SUMS_OFFSET, build, family, run


def profile(work: Path, count: int) -> dict:
    source_value, assignment_value = family(count)
    source = work / f"source-{count}.s31.json"
    assignment = work / f"assignment-{count}.json"
    source.write_text(json.dumps(source_value, separators=(",", ":")))
    assignment.write_text(json.dumps(assignment_value, separators=(",", ":")))
    prover, verifier, inspector = build(source, work / f"build-{count}")
    manifest = json.loads(run(str(inspector)).stdout)
    if (manifest["call_count"] != count or
            manifest["source_sha256"] != hashlib.sha256(source.read_bytes()).hexdigest()):
        raise AssertionError("inspector did not select the source")
    root = bytes.fromhex(manifest["fixed_root"])
    if len(root) != 32:
        raise AssertionError("expected a 32-byte preprocessed root")
    proof = work / f"proof-{count}.bin"
    statement = work / f"statement-{count}.json"
    run(str(prover), str(assignment), str(proof), str(statement))
    run(str(verifier), str(proof), str(statement))
    raw = proof.read_bytes()
    if raw[:len(MAGIC) + 4] != MAGIC + bytes((count, 1 + 2 * count, 3, 0)):
        raise AssertionError("unexpected mixed proof envelope")
    body_start = SUMS_OFFSET + 16 * (1 + 2 * count)
    locations = [at for at in range(body_start, len(raw) - len(root) + 1)
                 if raw[at:at + len(root)] == root]
    if len(locations) != 1:
        raise AssertionError(
            f"expected exactly one serialized preprocessed commitment root; "
            f"found {len(locations)} for N={count}"
        )
    return {"count": count, "manifest": manifest, "root": root, "raw": raw,
            "root_at": locations[0], "proof": proof, "statement": statement,
            "verifier": verifier}


def reject_swapped_root(work: Path, own: dict, other: dict) -> dict:
    if own["root"] == other["root"]:
        raise AssertionError("N=1 and N=8 fixed roots unexpectedly coincide")
    changed = bytearray(own["raw"])
    at = own["root_at"]
    changed[at:at + 32] = other["root"]
    if (len(changed) != len(own["raw"]) or
            changed[:at] != own["raw"][:at] or
            changed[at + 32:] != own["raw"][at + 32:]):
        raise AssertionError("mutation changed bytes outside the PCS root")
    altered = work / f"wrong-fixed-root-{own['count']}.bin"
    altered.write_bytes(changed)
    result = subprocess.run((str(own["verifier"]), str(altered), str(own["statement"])),
                            text=True, capture_output=True, check=False, timeout=60)
    # Zig's CLI prints `error: Name`, rather than its source-level
    # `error.Name` spelling. Requiring the exact message also confirms that
    # postcard decoding and shape preflight reached the native root check.
    if (result.returncode <= 0 or
            result.stderr.strip() != "error: InvalidMixedPreprocessedRoot"):
        raise AssertionError(
            f"N={own['count']} verifier did not reject the decoded swapped PCS "
            f"root at its source-derived commitment check: "
            f"exit={result.returncode}, stderr={result.stderr}"
        )
    return {"calls": own["count"], "fixed_root": own["root"].hex(),
            "other_fixed_root": other["root"].hex(),
            "postcard_root_offset": at,
            "proof_sha256": hashlib.sha256(own["raw"]).hexdigest(),
            "rejection": "InvalidMixedPreprocessedRoot"}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-mixed-preprocessed-root-") as temp:
        work = Path(temp)
        one = profile(work, 1)
        eight = profile(work, 8)
        results = [reject_swapped_root(work, one, eight),
                   reject_swapped_root(work, eight, one)]
    print(json.dumps({"schema": "s31-mixed-preprocessed-root-binding-v1",
                      "profiles": results}, sort_keys=True))


if __name__ == "__main__":
    main()
