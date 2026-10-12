#!/usr/bin/env python3
"""Replay every saved paired proof through its external source-pinned verifier."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

import design
import protocol

RESULT = protocol.ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-result.json"
SUMMARY = protocol.ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-summary.json"
AUDIT = protocol.ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-audit.json"


def bins(out: Path, case: str, profile: str) -> tuple[Path, Path | None]:
    base = out / case
    name = f"s31-{design.name(case)}"
    if profile == "direct":
        return (base / "direct-package/bin" / f"{name}-native-verifier",
                base / "direct-package/verification-key.json")
    if profile == "mixed":
        return (base / "mixed-package/bin" / f"{name}-mixed-general-native-verifier", None)
    raise ValueError("unknown lowering profile")


def run(out: Path) -> dict:
    frozen, protocol_sha = protocol.frozen()
    raw = RESULT.read_bytes()
    result = json.loads(raw)
    summary_raw = SUMMARY.read_bytes()
    summary = json.loads(summary_raw)
    if (raw != design.canonical(result) or summary_raw != design.canonical(summary) or
            result["protocol_sha256"] != protocol_sha or
            summary["protocol_sha256"] != protocol_sha or
            summary["result_sha256"] != design.digest(raw)):
        raise ValueError("saved result, summary, or protocol differs")
    expected_rows = 2 * len(protocol.CASES) * (protocol.SCORED + 1)
    rows = result["warmup_and_scored_rows"]
    if len(rows) != expected_rows:
        raise ValueError("wrong number of saved proof rows")
    identities = set()
    for row in rows:
        case, index, profile = row["case"], row["index"], row["profile"]
        if (case not in protocol.CASES or not 0 <= index <= protocol.SCORED or
                profile not in ("direct", "mixed") or
                (case, index, profile) in identities):
            raise ValueError("duplicate or invalid paired proof identity")
        identities.add((case, index, profile))
        claim = frozen["roster"][case]["claims"][index]
        proof = out / row["proof_relative_path"]
        statement = out / row["statement_relative_path"]
        changed = out / row["changed_relative_path"]
        if (design.digest(proof.read_bytes()) != row["proof_sha256"] or
                len(proof.read_bytes()) != row["proof_bytes"] or
                design.digest(statement.read_bytes()) != claim["statement_sha256"] or
                design.digest(changed.read_bytes()) != row["changed_statement_sha256"] or
                row["assignment_sha256"] != claim["assignment_sha256"]):
            raise ValueError("saved proof or claim bytes differ")
        verifier, key = bins(out, case, profile)
        base = [str(verifier), str(proof)]
        suffix = [str(key)] if key is not None else []
        honest = subprocess.run([*base, str(statement), *suffix],
                                cwd=protocol.ROOT, capture_output=True,
                                timeout=frozen["native_process_timeout_seconds"])
        wrong = subprocess.run([*base, str(changed), *suffix],
                               cwd=protocol.ROOT, capture_output=True,
                               timeout=frozen["native_process_timeout_seconds"])
        expected_rejection = (b"error: InvalidInteractionNonce" if profile == "direct"
                              else b"error: InvalidMixedInteractionNonce")
        if (honest.returncode or wrong.returncode <= 0 or
                wrong.stderr.strip() != expected_rejection):
            raise ValueError(f"replayed native verifier control failed: {case}/{index}/{profile}")
    if identities != {(case, index, profile) for case in protocol.CASES
                     for index in range(protocol.SCORED + 1)
                     for profile in ("direct", "mixed")}:
        raise ValueError("missing paired proof identity")
    report = {"schema": "s31-paired-mixed-vs-direct-v1-replay-audit",
              "protocol_sha256": protocol_sha,
              "result_sha256": design.digest(raw),
              "summary_sha256": design.digest(summary_raw),
              "honest_native_verifier_acceptances": expected_rows,
              "changed_claim_native_verifier_rejections": expected_rows,
              "all_source_assignment_pairs_complete": True}
    if AUDIT.exists():
        raise FileExistsError("replay audit already exists")
    AUDIT.write_bytes(design.canonical(report))
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.out.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
