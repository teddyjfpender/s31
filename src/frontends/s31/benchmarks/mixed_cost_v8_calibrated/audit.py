#!/usr/bin/env python3
"""Post-run artifact audit; --native replays every saved proof and changed claim."""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
from pathlib import Path

import protocol as p
_spec = importlib.util.spec_from_file_location("v8_calibrated_study", p.HERE / "study.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("V8 calibrated study module unavailable")
s = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(s)


def run(out: Path, native: bool) -> dict:
    protocol_raw = p.PROTOCOL.read_bytes()
    protocol = p.v2.parse(protocol_raw)
    if (protocol_raw != p.canonical(protocol) or
            p.v2.git("show", f"HEAD:{p.PROTOCOL.relative_to(p.ROOT).as_posix()}") !=
            protocol_raw):
        raise ValueError("protocol was not committed unchanged")
    raw = s.RESULT.read_bytes()
    score_raw = s.SCORE.read_bytes()
    corpus = p.v2.parse(raw)
    score = p.v2.parse(score_raw)
    if (raw != p.canonical(corpus) or score_raw != p.canonical(score) or
            corpus.get("schema") != "s31-mixed-cost-v8-calibrated-result" or
            score.get("schema") != "s31-mixed-cost-v8-calibrated-score" or
            (out / "result.json").read_bytes() != raw or
            corpus["protocol_sha256"] != p.sha(protocol_raw) or
            score["protocol_sha256"] != p.sha(protocol_raw) or
            score["result_sha256"] != p.sha(raw) or
            corpus["v8_model_sha256"] != protocol["v8_model_sha256"] or
            corpus["host"] != protocol["host"] or
            len(corpus["records"]) != len(protocol["source_roster"])):
        raise ValueError("canonical corpus, model, protocol or score identity differs")
    checked = 0
    for record, (name, expected) in zip(corpus["records"], protocol["source_roster"].items()):
        directory = out / name
        binary_paths = s.bins(directory, name)
        tracked_source = p.SOURCE_DIR / f"{name}.json"
        if (record["name"] != name or record["call_count"] != expected["call_count"] or
                record["source_sha256"] != expected["source_sha256"] or
                tracked_source.read_bytes() != (directory / "source.s31.json").read_bytes() or
                p.v2.git("show", f"HEAD:{tracked_source.relative_to(p.ROOT).as_posix()}") !=
                tracked_source.read_bytes() or
                p.sha((directory / "source.s31.json").read_bytes()) != expected["source_sha256"] or
                {role: p.sha(path.read_bytes()) for role, path in binary_paths.items()} !=
                record["binary_sha256"] or
                p.sha((directory / "manifest.stdout").read_bytes()) != record["manifest_sha256"] or
                p.v2.parse((directory / "manifest.stdout").read_bytes()) != record["native_manifest"] or
                len(record["trials"]) != len(s.TRIALS)):
            raise ValueError(f"source, binary or manifest artifact differs: {name}")
        s.check_manifest(record["native_manifest"], expected)
        for row, (index, repeat) in zip(record["trials"], s.TRIALS):
            prefix = f"a{index:02d}r{repeat}"
            assignment = (directory / f"{prefix}.assignment.json").read_bytes()
            statement = (directory / f"{prefix}.statement.json").read_bytes()
            changed = directory / f"{prefix}.changed.json"
            proof = directory / f"{prefix}.proof"
            if (row["claim_index"] != index or row["repeat"] != repeat or
                    row["assignment_sha256"] != expected["assignment_sha256"][index] or
                    row["statement_sha256"] != expected["statement_sha256"][index] or
                    p.sha(assignment) != row["assignment_sha256"] or
                    p.sha(statement) != row["statement_sha256"] or
                    p.sha(proof.read_bytes()) != row["proof_sha256"] or
                    proof.stat().st_size != row["proof_bytes"] or
                    (directory / f"{prefix}.emitted.json").read_bytes() != statement or
                    b"verified" not in (directory / f"{prefix}.verified.stderr").read_bytes() or
                    b"InvalidMixedInteractionNonce" not in
                    (directory / f"{prefix}.changed.stderr").read_bytes() or
                    row["native_phases_ns"]["source_sha256"] != expected["source_sha256"]):
                raise ValueError(f"claim, proof or native report differs: {name}/{prefix}")
            for key in ("prover_process_monotonic_ns", "external_verifier_process_monotonic_ns"):
                endpoint = row[key]
                if (set(endpoint) != {"start", "end", "duration"} or
                        endpoint["end"] - endpoint["start"] != endpoint["duration"] or
                        endpoint["duration"] <= 0):
                    raise ValueError(f"timing endpoints differ: {name}/{prefix}")
            if row["first_verified_process_wall_ns"] != (
                    row["prover_process_monotonic_ns"]["duration"] +
                    row["external_verifier_process_monotonic_ns"]["duration"]):
                raise ValueError(f"first-verified wall differs: {name}/{prefix}")
            if native:
                accepted = subprocess.run([str(binary_paths["verifier"]), str(proof),
                                           str(directory / f"{prefix}.statement.json")],
                                          capture_output=True, check=False)
                rejected = subprocess.run([str(binary_paths["verifier"]), str(proof),
                                           str(changed)], capture_output=True, check=False)
                if (accepted.returncode or b"verified" not in accepted.stderr or
                        not p.v2.proof_layer_rejection(rejected)):
                    raise ValueError(f"native proof replay differs: {name}/{prefix}")
            checked += 1
        rescored = s.score_record(record, expected, protocol["gates"])
        if rescored != score["sources"][name]:
            raise ValueError(f"score differs from frozen prediction: {name}")
    if (checked != corpus["verified_proofs"] or
            checked != corpus["changed_claim_proof_rejections"] or
            score["all_gates_pass"] != all(row["all_gates_pass"]
                                          for row in score["sources"].values())):
        raise ValueError("total proof count or final gate differs")
    return {"schema": "s31-mixed-cost-v8-calibrated-audit",
            "protocol_sha256": p.sha(protocol_raw), "result_sha256": p.sha(raw),
            "score_sha256": p.sha(score_raw),
            "checked_proofs": checked, "native_replay": native,
            "changed_claims_rejected": checked,
            "all_gates_pass": score["all_gates_pass"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--write", action="store_true",
                        help="save the audit in design/s31/measurements/language")
    args = parser.parse_args()
    result = run(args.out, args.native)
    if args.write:
        destination = p.LANGUAGE / "mixed-cost-v8-calibrated-audit.json"
        if destination.exists():
            raise ValueError("audit artifact already exists")
        destination.write_bytes(p.canonical(result))
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
