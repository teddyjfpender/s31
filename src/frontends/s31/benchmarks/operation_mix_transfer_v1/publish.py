#!/usr/bin/env python3
"""Post hoc compact publication of completed operation-family transfer data."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

from independent_score import check as independent_check

OPS = ("add", "mul")
COUNTS = (96, 256, 448)
FILES = ("plan.json", "heldout-report.json", "heldout-score.json", "audit.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def publish(root: Path, target: Path) -> None:
    independent = independent_check(root)
    audit = json.loads((root / "audit.json").read_bytes())
    if (independent["trial_count"] != 72 or
            audit.get("replayed_accepted_proofs") != 72 or
            audit.get("replayed_rejected_changed_claims") != 72):
        raise ValueError("independent score or native replay is incomplete")
    if target.exists():
        raise FileExistsError("publication target already exists")
    plan = json.loads((root / "plan.json").read_bytes())
    report = json.loads((root / "heldout-report.json").read_bytes())
    rows = []
    for op in OPS:
        for count in COUNTS:
            label = f"{op}-{count}"
            for sample in range(12):
                path = root / "heldout" / label / "trials" / f"{sample:03}" / "trial-report.json"
                trial = json.loads(path.read_bytes())
                if (sha(path) != report["cases"][label]["trial_report_sha256"][sample] or
                        sha(path.parent / "proof.bin") != trial["proof_sha256"] or
                        trial.get("independent_value_oracle_provenance") !=
                        plan["identity"]["independent_oracle_provenance"]):
                    raise ValueError("saved trial, proof, or oracle provenance mismatch")
                rows.append({
                    "operation": op, "gates": count, "sample": sample,
                    "assignment_sha256": plan["sources"][label]["assignment_sha256"][sample],
                    "trial_report_sha256": sha(path),
                    "proof_sha256": trial["proof_sha256"],
                    "raw_qm31_rows": trial["raw"]["qm31_ops"],
                    "padded_qm31_rows": trial["padded"]["qm31_ops"],
                    "paired_wall_seconds": trial["prove_seconds"] + trial["verify_seconds"],
                    "fri_pow_seconds": trial["prover_stages"]["fri_pow_seconds"],
                    "interaction_pow_seconds": trial["prover_stages"]["interaction_pow_seconds"],
                    "proof_bytes": trial["proof_bytes"],
                    "prover_peak_rss_bytes": trial["prover_peak_rss_bytes"],
                    "native_verifier_accepted": trial["native_verifier_accepted"],
                    "changed_public_statement_rejected": trial["changed_public_statement_rejected"],
                    "independent_value_oracle_status": trial["independent_value_oracle"]["status"],
                })
    target.mkdir(parents=True)
    for name in FILES:
        shutil.copyfile(root / name, target / name)
    ledger = {
        "schema": "s31-operation-mix-transfer-v1-compact-ledger",
        "status": "post-hoc-publication-of-local-evidence",
        "source_evidence_root": str(root.resolve()),
        "prior_calibration_sha256": plan["prior_calibration_sha256"],
        "native_replay_audit_sha256": sha(root / "audit.json"),
        "trial_count": len(rows), "trials": rows,
    }
    (target / "compact-trials.json").write_text(
        json.dumps(ledger, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--publish", type=Path, required=True)
    args = parser.parse_args()
    publish(args.out.resolve(), args.publish.resolve())


if __name__ == "__main__":
    main()
