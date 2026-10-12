#!/usr/bin/env python3
"""Publish compact, explicitly post hoc copies of a completed local study."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

from independent_score import check as independent_check

PHASES = {"train": (32, 192, 384), "heldout": (96, 256, 448)}
FILES = ("plan.json", "train-report.json", "calibration.json",
         "heldout-report.json", "heldout-score.json", "audit.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def publish(root: Path, destination: Path) -> None:
    result = independent_check(root)
    audit = json.loads((root / "audit.json").read_bytes())
    if (result["trial_reports_checked"] != 72 or
            audit.get("replayed_accepted_proofs") != 72 or
            audit.get("replayed_rejected_changed_claims") != 72):
        raise ValueError("native replay or independent scoring is incomplete")
    if destination.exists():
        raise FileExistsError("publication destination already exists")
    rows = []
    provenance = None
    for phase, counts in PHASES.items():
        report = json.loads((root / f"{phase}-report.json").read_bytes())
        for gates in counts:
            for sample in range(12):
                file = root / phase / f"gates-{gates}" / "trials" / f"{sample:03}" / "trial-report.json"
                trial = json.loads(file.read_bytes())
                current = trial["independent_value_oracle_provenance"]
                if provenance is None:
                    provenance = current
                elif provenance != current:
                    raise ValueError("oracle provenance differs between saved trials")
                if (sha(file) != report["cases"][str(gates)]["trial_report_sha256"][sample] or
                        sha(file.parent / "proof.bin") != trial["proof_sha256"]):
                    raise ValueError("saved trial or proof differs from phase report")
                rows.append({
                    "phase": phase, "gates": gates, "sample": sample,
                    "trial_report_sha256": sha(file),
                    "proof_sha256": trial["proof_sha256"],
                    "assignment_sha256": json.loads((root / "plan.json").read_bytes())[
                        "sources"][str(gates)]["assignment_sha256"][sample],
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
    destination.mkdir(parents=True)
    for name in FILES:
        shutil.copyfile(root / name, destination / name)
    ledger = {
        "schema": "s31-direct-gate-geometry-transfer-v1-compact-ledger",
        "status": "post-hoc-publication-of-local-evidence",
        "source_evidence_root": str(root.resolve()),
        "trial_count": len(rows), "native_replay_audit_sha256": sha(root / "audit.json"),
        "oracle_provenance_status": "post-hoc-consistency-check-not-in-prospective-plan",
        "oracle_provenance": provenance,
        "trials": rows,
    }
    (destination / "compact-trials.json").write_text(
        json.dumps(ledger, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="raw local study root")
    parser.add_argument("--publish", type=Path, required=True)
    args = parser.parse_args()
    publish(args.out.resolve(), args.publish.resolve())


if __name__ == "__main__":
    main()
