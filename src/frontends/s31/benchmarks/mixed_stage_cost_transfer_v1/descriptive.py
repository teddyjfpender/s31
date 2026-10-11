#!/usr/bin/env python3
"""Recompute descriptive whole-prover costs from the sealed transfer corpus.

This is deliberately not the frozen model score. It reads no fitted model and
cannot turn the unscored prospective transfer into a predictive result.
"""

from __future__ import annotations

import hashlib
import json
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
LANGUAGE = ROOT / "design/s31/measurements/language"
CORPUS_DIR = LANGUAGE / "mixed-stage-cost-transfer-v1-unscored"
STAGES = (
    "profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
    "witness_compile_ns", "native_prove_including_setup_ns",
    "envelope_and_serialization_ns",
)
SAVED_SHA256 = (
    "87f0cccb359ab28501ce9f12d99e83fd2090097e16c1ab5f17d52445b664a862",
    "0cd7e3b3bdaaf7f5f84c39d8b2698ad5b8a72d889fd5539b34fba6c4758d5e2f",
    "a1d591bbf7c37703d24b84728f37fd593caf40b61456edba552f85eb8828bd6c",
    "16fe257c763a91aa06b0eee73dffb3ebaf944f42a7d88c1ab5ac8b1830379b38",
    "7ae215e9187dc5553f93ac043f7842ebce0364be02948e08cb3bd7ca06f08926",
)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def quantile(values: list[int], fraction: float) -> float:
    ordered = sorted(values)
    require(bool(ordered), "empty timing distribution")
    rank = fraction * (len(ordered) - 1)
    lower = int(rank)
    return ordered[lower] + (ordered[min(lower + 1, len(ordered) - 1)] -
                             ordered[lower]) * (rank - lower)


def analyze(protocol_raw: bytes, phase_raw: bytes, corpus_raw: bytes,
            audit_raw: bytes, seal_raw: bytes) -> dict:
    for raw in (protocol_raw, phase_raw, corpus_raw, audit_raw, seal_raw):
        require(raw == canonical(json.loads(raw)), "noncanonical evidence JSON")
    protocol, phase, corpus, audit, seal = map(json.loads,
        (protocol_raw, phase_raw, corpus_raw, audit_raw, seal_raw))
    protocol_hash, phase_hash = digest(protocol_raw), digest(phase_raw)
    require(protocol["schema"] == "s31-mixed-stage-cost-transfer-v1-protocol-candidate",
            "wrong protocol schema")
    require(corpus["schema"] == "s31-mixed-stage-cost-transfer-v1-audited-corpus" and
            audit["schema"] == "s31-mixed-stage-cost-transfer-v1-audit" and
            phase["schema"] == "s31-mixed-stage-cost-transfer-v1-phase-root" and
            seal["schema"] == "s31-mixed-stage-cost-transfer-v1-unscored-evidence-anchor",
            "wrong evidence schema")
    require(seal["status"] == "unscored_missing_frozen_model_bytes" and
            seal["evaluation_status"] == "not_run" and
            seal["required_frozen_train_model_sha256"] ==
                protocol["reference_train_model_sha256"], "evidence is not unscored")
    require(all(value == protocol_hash for value in
                (phase["protocol_sha256"], corpus["protocol_sha256"],
                 audit["protocol_sha256"], seal["protocol_sha256"])),
            "protocol digest mismatch")
    require(all(value == phase_hash for value in
                (corpus["phase_root_sha256"], audit["phase_root_sha256"],
                 seal["phase_root_file_sha256"])), "phase digest mismatch")
    require(phase["content_root_sha256"] == seal["internal_content_root_sha256"] and
            phase["file_count"] == 4069, "raw phase summary mismatch")
    require(digest(corpus_raw) == audit["corpus_sha256"] == seal["corpus_sha256"] and
            digest(audit_raw) == seal["audit_sha256"], "audit or corpus digest mismatch")
    require(audit["native_verified_proofs"] == seal["verified_trials"] == 360 and
            audit["changed_input_and_result_rejected"] is True and
            audit["raw_build_and_process_endpoints_replayed"] is True and
            audit["source_assignment_statement_manifest_and_binary_hashes_replayed"] is True,
            "native audit is incomplete")
    require(corpus["host"] == protocol["host"] and
            corpus["compiler_sha256"] == protocol["compiler_sha256"] and
            corpus["engine_gitlink_commit"] == protocol["engine_gitlink_commit"] and
            corpus["inventory_sha256"] == protocol["inventory_sha256"] and
            digest(canonical(protocol["inventory"])) == protocol["inventory_sha256"],
            "corpus identity differs from protocol")

    roster = protocol["inventory"]
    records = corpus["records"]
    require(len(records) == len(roster) == 12 and
            [record["name"] for record in records] == list(roster),
            "program roster or order changed")
    seen_assignments, seen_statements, seen_proofs = set(), set(), set()
    summaries = []
    for record in records:
        name = record["name"]
        expected = roster[name]
        require(record["shape"] == expected["shape"] and
                record["call_count"] == expected["call_count"] and
                record["source_sha256"] == expected["source_sha256"] and
                len(record["trials"]) == protocol["assignments_per_program"] == 30 and
                type(record["build_wall_ns"]) is int and record["build_wall_ns"] > 0,
                f"program identity or build time changed: {name}")
        wall, native, verifier, proof, residual = [], [], [], [], []
        for index, trial in enumerate(record["trials"]):
            require(trial["schema"] == "s31-mixed-stage-diagnostic-v1" and
                    trial["external_native_verification_accepted"] is True and
                    trial["engine_setup_preprocessing_ns"] is None and
                    trial["engine_pow_ns"] is None and
                    trial["source_sha256"] == expected["source_sha256"] and
                    trial["assignment_sha256"] == expected["assignment_sha256"][index] and
                    trial["typed_statement_sha256"] ==
                        expected["typed_statement_sha256"][index],
                    f"trial identity changed: {name}/{index}")
            for field, seen in (("assignment_sha256", seen_assignments),
                                ("typed_statement_sha256", seen_statements),
                                ("proof_sha256", seen_proofs)):
                value = trial[field]
                require(value not in seen, f"duplicate {field}: {name}/{index}")
                seen.add(value)
            stage = trial["prover_internal_stages_ns"]
            require(set(stage) == {*STAGES, "package_total_ns"} and
                    all(type(stage[key]) is int and stage[key] >= 0 for key in stage) and
                    stage["package_total_ns"] == sum(stage[key] for key in STAGES),
                    f"package stage partition changed: {name}/{index}")
            values = [trial[key] for key in
                      ("prover_process_wall_ns", "external_verifier_process_wall_ns",
                       "first_verified_process_wall_ns", "proof_bytes")]
            require(all(type(value) is int and value > 0 for value in values) and
                    values[2] == values[0] + values[1] and
                    values[0] >= stage["package_total_ns"],
                    f"process accounting changed: {name}/{index}")
            clock = trial["process_monotonic_ns"]
            require(clock["prover_end"] - clock["prover_start"] == values[0] and
                    clock["verifier_end"] - clock["verifier_start"] == values[1] and
                    clock["prover_start"] < clock["prover_end"] <=
                        clock["verifier_start"] < clock["verifier_end"],
                    f"process endpoints changed: {name}/{index}")
            wall.append(values[2])
            native.append(stage["native_prove_including_setup_ns"])
            verifier.append(values[1])
            proof.append(values[3])
            residual.append(values[0] - stage["package_total_ns"])
        summaries.append({
            "name": name, "shape": record["shape"], "call_count": record["call_count"],
            "total_rounds": expected["total_rounds"], "trials": len(wall),
            "build_wall_ns": record["build_wall_ns"],
            "first_verified_wall_p50_ns": statistics.median(wall),
            "first_verified_wall_p90_ns": quantile(wall, .9),
            "native_prove_including_setup_p50_ns": statistics.median(native),
            "external_verifier_process_p50_ns": statistics.median(verifier),
            "prover_process_residual_p50_ns": statistics.median(residual),
            "proof_p50_bytes": statistics.median(proof),
        })
    require(len(seen_assignments) == len(seen_statements) == len(seen_proofs) == 360,
            "trial set incomplete")
    return {"schema": "s31-mixed-stage-transfer-v1-descriptive-replay",
            "status": "descriptive_only_frozen_model_unavailable",
            "protocol_sha256": protocol_hash, "phase_root_file_sha256": phase_hash,
            "corpus_sha256": digest(corpus_raw), "audit_sha256": digest(audit_raw),
            "verified_trials": 360, "programs": summaries,
            "prediction_error_reported": False, "speedup_claim_enabled": False}


def main() -> None:
    paths = (LANGUAGE / "mixed-stage-cost-transfer-v1-protocol.json",
             CORPUS_DIR / "phase-root.json", CORPUS_DIR / "corpus.json",
             CORPUS_DIR / "audit.json",
             LANGUAGE / "mixed-stage-cost-transfer-v1-unscored-evidence-anchor.json")
    raw = tuple(path.read_bytes() for path in paths)
    require(tuple(digest(value) for value in raw) == SAVED_SHA256,
            "saved evidence differs from the independently recorded digests")
    print(canonical(analyze(*raw)).decode(), end="")


if __name__ == "__main__":
    main()
