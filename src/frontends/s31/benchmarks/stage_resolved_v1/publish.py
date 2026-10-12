#!/usr/bin/env python3
"""Post hoc compact publication of the completed stage-resolved study."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

from independent_score import check as independent_check
from posthoc_calibration_audit import replay as calibration_replay

COUNTS = (96, 256, 448)
FILES = ("plan.json", "heldout-report.json", "heldout-score.json", "audit.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def publish(root: Path, target: Path) -> None:
    independent = independent_check(root)
    posthoc = calibration_replay()
    audit = json.loads((root / "audit.json").read_bytes())
    if (independent["trial_count"] != 36 or
            audit.get("replayed_accepted_proofs") != 36 or
            audit.get("replayed_rejected_changed_claims") != 36 or
            posthoc["exact_replay_passed"] is not True):
        raise ValueError("independent score, replay, or calibration audit incomplete")
    if target.exists():
        raise FileExistsError("publication target already exists")
    plan = json.loads((root / "plan.json").read_bytes())
    report = json.loads((root / "heldout-report.json").read_bytes())
    rows = []
    for count in COUNTS:
        for sample in range(12):
            path = root / "heldout" / f"gates-{count}" / "trials" / f"{sample:03}" / "trial-report.json"
            trial = json.loads(path.read_bytes())
            native = trial["prover_stages"]
            if (sha(path) != report["cases"][str(count)]["trial_report_sha256"][sample] or
                    sha(path.parent / "proof.bin") != trial["proof_sha256"] or
                    trial.get("independent_value_oracle_provenance") !=
                    plan["identity"]["independent_oracle_provenance"]):
                raise ValueError("saved trial, proof, or oracle provenance mismatch")
            rows.append({
                "gates": count, "sample": sample,
                "assignment_sha256": plan["sources"][str(count)]["assignment_sha256"][sample],
                "trial_report_sha256": sha(path), "proof_sha256": trial["proof_sha256"],
                "raw_qm31_rows": trial["raw"]["qm31_ops"],
                "padded_qm31_rows": trial["padded"]["qm31_ops"],
                "prover_process_seconds": trial["prove_seconds"],
                "verifier_process_seconds": trial["verify_seconds"],
                "paired_wall_seconds": trial["prove_seconds"] + trial["verify_seconds"],
                "witness_seconds": native["witness_seconds"],
                "setup_seconds": native["setup_seconds"],
                "native_nonpow_prove_seconds": native["prove_excluding_pow_seconds"],
                "native_pow_seconds": native["fri_pow_seconds"] + native["interaction_pow_seconds"],
                "native_runtime_other_seconds": native["runtime_other_seconds"],
                "prover_process_residual_seconds": trial["prove_seconds"] -
                    native["total_through_verification_seconds"],
                "proof_bytes": trial["proof_bytes"],
                "prover_peak_rss_bytes": trial["prover_peak_rss_bytes"],
                "native_verifier_accepted": trial["native_verifier_accepted"],
                "changed_public_statement_rejected": trial["changed_public_statement_rejected"],
                "independent_value_oracle_status": trial["independent_value_oracle"]["status"],
            })
    target.mkdir(parents=True)
    for name in FILES:
        shutil.copyfile(root / name, target / name)
    (target / "posthoc-calibration-audit.json").write_text(
        json.dumps(posthoc, indent=2, sort_keys=True) + "\n")
    ledger = {
        "schema": "s31-stage-resolved-v1-compact-ledger",
        "status": "post-hoc-publication-of-local-evidence",
        "source_evidence_root": str(root.resolve()),
        "plan_sha256": sha(root / "plan.json"),
        "native_replay_audit_sha256": sha(root / "audit.json"),
        "trial_count": len(rows), "trials": rows,
    }
    (target / "compact-trials.json").write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--publish", type=Path, required=True)
    args = parser.parse_args()
    publish(args.out.resolve(), args.publish.resolve())


if __name__ == "__main__":
    main()
