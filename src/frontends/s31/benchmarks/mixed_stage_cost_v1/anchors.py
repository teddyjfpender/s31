"""Train-before-heldout and report seals for the prospective mixed cost study."""

from __future__ import annotations

import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from cohort import ROOT, canonical, sha
from model import evaluate, fit_model
from protocol import committed


def anchored(path: Path, commit: str, schema: str) -> dict:
    committed(path, commit)
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       commit, "HEAD"], check=False).returncode:
        raise ValueError("cost anchor is not an ancestor")
    value = json.loads(path.read_bytes())
    try:
        instant = datetime.fromisoformat(value["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, ValueError, TypeError) as exc:
        raise ValueError("cost anchor requires UTC timestamp") from exc
    if (value.get("schema") != schema or instant.utcoffset() is None or
            instant.utcoffset().total_seconds() != 0 or instant > datetime.now(timezone.utc)):
        raise ValueError("cost anchor schema or timestamp differs")
    return value


def train_model_admission(train_out: Path, protocol_sha256: str,
                          train_phase_root_sha256: str, train_phase_anchor_commit: str,
                          model_sha256: str, model_anchor_commit: str) -> tuple[dict, dict]:
    phase_path = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-train-phase-anchor.json"
    phase = anchored(phase_path, train_phase_anchor_commit,
                     "s31-mixed-stage-cost-v1-phase-anchor")
    if (phase.get("split") != "train" or phase.get("protocol_sha256") != protocol_sha256 or
            phase.get("phase_root_sha256") != train_phase_root_sha256 or
            sha((train_out / "phase-root.json").read_bytes()) != train_phase_root_sha256):
        raise ValueError("train phase anchor does not bind this raw phase")
    from evidence import phase_root
    if (train_out / "phase-root.json").read_bytes() != canonical(
            phase_root(train_out, "train", protocol_sha256)):
        raise ValueError("training raw files differ from anchored phase root")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       train_phase_anchor_commit, model_anchor_commit], check=False).returncode:
        raise ValueError("model anchor does not descend from train phase anchor")
    model_path = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-model-freeze.json"
    anchor = anchored(model_path, model_anchor_commit, "s31-mixed-stage-cost-v1-model-freeze")
    audit_bytes = (train_out / "audit.json").read_bytes()
    corpus_bytes = (train_out / "corpus.json").read_bytes()
    model_bytes = (train_out / "model.json").read_bytes()
    if (anchor.get("protocol_sha256") != protocol_sha256 or
            anchor.get("train_phase_root_sha256") != train_phase_root_sha256 or
            anchor.get("train_phase_anchor_commit") != train_phase_anchor_commit or
            anchor.get("train_audit_sha256") != sha(audit_bytes) or
            anchor.get("train_corpus_sha256") != sha(corpus_bytes) or
            anchor.get("model_sha256") != model_sha256 or
            sha(model_bytes) != model_sha256):
        raise ValueError("model freeze does not bind audited training evidence")
    audit = json.loads(audit_bytes)
    corpus = json.loads(corpus_bytes)
    model = json.loads(model_bytes)
    if (audit.get("schema") != "s31-mixed-stage-cost-v1-audit" or
            audit.get("split") != "train" or
            audit.get("phase_root_sha256") != train_phase_root_sha256 or
            audit.get("corpus_sha256") != sha(corpus_bytes) or
            audit.get("native_verified_proofs") != 400 or
            audit.get("changed_input_and_result_rejected") is not True or
            audit.get("raw_build_and_process_endpoints_replayed") is not True or
            audit.get("source_assignment_statement_manifest_and_binary_hashes_replayed") is not True or
            corpus.get("schema") != "s31-mixed-stage-cost-v1-audited-corpus" or
            corpus.get("split") != "train" or
            corpus.get("protocol_sha256") != protocol_sha256 or
            corpus.get("phase_root_sha256") != train_phase_root_sha256):
        raise ValueError("training audit did not establish required native controls")
    reproduced = fit_model(corpus["records"], protocol_sha256, corpus["inventory_sha256"],
                           corpus["host"], corpus["compiler_sha256"],
                           corpus["engine_gitlink_commit"])
    if model_bytes != canonical(reproduced):
        raise ValueError("frozen model differs from deterministic training-only fit")
    admission = {
        "schema": "s31-mixed-stage-cost-v1-train-admission",
        "protocol_sha256": protocol_sha256,
        "train_phase_root_sha256": train_phase_root_sha256,
        "train_phase_anchor_commit": train_phase_anchor_commit,
        "train_audit_sha256": sha(audit_bytes),
        "train_corpus_sha256": sha(corpus_bytes),
        "model_sha256": model_sha256,
        "model_anchor_commit": model_anchor_commit,
    }
    return admission, model


def fit_train(train_out: Path, protocol_sha256: str, train_phase_root_sha256: str,
              train_phase_anchor_commit: str) -> str:
    phase_path = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-train-phase-anchor.json"
    phase = anchored(phase_path, train_phase_anchor_commit,
                     "s31-mixed-stage-cost-v1-phase-anchor")
    audit_bytes = (train_out / "audit.json").read_bytes()
    corpus_bytes = (train_out / "corpus.json").read_bytes()
    audit, corpus = json.loads(audit_bytes), json.loads(corpus_bytes)
    from evidence import phase_root
    if (phase.get("split") != "train" or phase.get("protocol_sha256") != protocol_sha256 or
            phase.get("phase_root_sha256") != train_phase_root_sha256 or
            sha((train_out / "phase-root.json").read_bytes()) != train_phase_root_sha256 or
            (train_out / "phase-root.json").read_bytes() != canonical(
                phase_root(train_out, "train", protocol_sha256)) or
            audit.get("corpus_sha256") != sha(corpus_bytes) or
            audit.get("phase_root_sha256") != train_phase_root_sha256 or
            audit.get("changed_input_and_result_rejected") is not True or
            corpus.get("phase_root_sha256") != train_phase_root_sha256):
        raise ValueError("cannot fit before anchored native train audit")
    model_path = train_out / "model.json"
    if model_path.exists():
        raise ValueError("training model already exists; do not refit in place")
    model = fit_model(corpus["records"], protocol_sha256, corpus["inventory_sha256"],
                      corpus["host"], corpus["compiler_sha256"],
                      corpus["engine_gitlink_commit"])
    model_path.write_bytes(canonical(model))
    return sha(model_path.read_bytes())


def evaluate_heldout(heldout_out: Path, model: dict, protocol_sha256: str,
                     expected_phase_root_sha256: str, phase_anchor_commit: str,
                     model_anchor_commit: str) -> dict:
    phase_path = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-heldout-phase-anchor.json"
    phase = anchored(phase_path, phase_anchor_commit,
                     "s31-mixed-stage-cost-v1-phase-anchor")
    if (phase.get("split") != "heldout" or
            phase.get("protocol_sha256") != protocol_sha256 or
            phase.get("phase_root_sha256") != expected_phase_root_sha256 or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            model_anchor_commit, phase_anchor_commit],
                           check=False).returncode):
        raise ValueError("held-out phase anchor does not descend from frozen model")
    audit_bytes = (heldout_out / "audit.json").read_bytes()
    corpus_bytes = (heldout_out / "corpus.json").read_bytes()
    audit, corpus = json.loads(audit_bytes), json.loads(corpus_bytes)
    if (audit.get("schema") != "s31-mixed-stage-cost-v1-audit" or
            audit.get("split") != "heldout" or
            audit.get("corpus_sha256") != sha(corpus_bytes) or
            audit.get("phase_root_sha256") != expected_phase_root_sha256 or
            audit.get("native_verified_proofs") != 400 or
            audit.get("changed_input_and_result_rejected") is not True or
            corpus.get("split") != "heldout" or
            corpus.get("protocol_sha256") != protocol_sha256):
        raise ValueError("held-out native audit did not pass")
    from evidence import phase_root
    if ((heldout_out / "phase-root.json").read_bytes() != canonical(
            phase_root(heldout_out, "heldout", protocol_sha256)) or
            sha((heldout_out / "phase-root.json").read_bytes()) !=
                expected_phase_root_sha256 or
            corpus.get("phase_root_sha256") != expected_phase_root_sha256):
        raise ValueError("held-out raw phase changed after native audit")
    result = evaluate(model, corpus["records"], protocol_sha256=protocol_sha256,
                      inventory_sha256=corpus["inventory_sha256"], host=corpus["host"],
                      compiler_sha256=corpus["compiler_sha256"],
                      engine_gitlink_commit=corpus["engine_gitlink_commit"])
    target = heldout_out / "evaluation.json"
    if target.exists():
        raise ValueError("held-out evaluation already exists; never re-evaluate in place")
    target.write_bytes(canonical(result))
    return result
