#!/usr/bin/env python3
"""Audit saved proof artifacts and pin the prospective cost model outcome."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path

from stage_aware_predictor_v1 import PROTOCOL, changed_claim_field, evaluate, fit_model


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit_corpus(path: Path, expected_split: str,
                 expected_schema: str = "s31-stage-aware-cost-corpus-v1") -> tuple[dict, dict]:
    corpus = json.loads(path.read_text())
    if corpus.get("schema") != expected_schema or corpus.get("split") != expected_split:
        raise ValueError(f"{path}: wrong stage-aware corpus split")
    base = path.parent
    controls = {"native_accepted": 0, "changed_claim_rejected": 0,
                "independent_oracle_passed": 0, "saved_proof_digest_matched": 0,
                "full_trial_report_matched": 0, "source_digest_matched": 0}
    for name, case in corpus["cases"].items():
        if file_hash(Path(case["source"])) != case["source_sha256"]:
            raise ValueError(f"{name}: source digest mismatch")
        controls["source_digest_matched"] += 1
        for index, compact in enumerate(case["trials"]):
            directory = base / name / "trials" / f"{index:02d}"
            proof = directory / "proof.bin"
            full = json.loads((directory / "trial-report.json").read_text())
            if proof.stat().st_size != compact["proof_bytes"] or file_hash(proof) != compact["proof_sha256"]:
                raise ValueError(f"{name}[{index}]: saved proof bytes mismatch")
            controls["saved_proof_digest_matched"] += 1
            if any(full.get(key) != value for key, value in compact.items()):
                raise ValueError(f"{name}[{index}]: compact trial differs from full report")
            controls["full_trial_report_matched"] += 1
            if compact["native_verifier_accepted"] is not True:
                raise ValueError(f"{name}[{index}]: native verifier rejected")
            controls["native_accepted"] += 1
            category, field = changed_claim_field(compact["changed_public_statement_rejected"])
            statement = json.loads((directory / "statement.json").read_text())
            changed = json.loads((directory / "changed-statement.json").read_text())
            try:
                original_value = statement[category][field][0]
                changed_value = changed[category][field][0]
            except (KeyError, IndexError, TypeError) as exc:
                raise ValueError(f"{name}[{index}]: changed public field is absent") from exc
            expected_changed = copy.deepcopy(statement)
            expected_changed[category][field][0] = changed_value
            if changed_value == original_value or changed != expected_changed:
                raise ValueError(f"{name}[{index}]: saved changed statement does not match control")
            controls["changed_claim_rejected"] += 1
            if compact["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}[{index}]: independent oracle failed")
            controls["independent_oracle_passed"] += 1
    return corpus, controls


def publish(train_path: Path, model_path: Path, validation_path: Path,
            evaluation_path: Path) -> dict:
    protocol_sha = file_hash(PROTOCOL)
    train, train_controls = audit_corpus(train_path, "train")
    validation, validation_controls = audit_corpus(validation_path, "validation")
    model = json.loads(model_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    protocol = json.loads(PROTOCOL.read_text())
    if train["protocol_sha256"] != protocol_sha or validation["protocol_sha256"] != protocol_sha:
        raise ValueError("corpus protocol digest mismatch")
    if model["training_corpus_sha256"] != file_hash(train_path):
        raise ValueError("model not bound to audited training corpus")
    if validation["frozen_model_sha256"] != file_hash(model_path):
        raise ValueError("validation not bound to frozen model")
    if evaluation["frozen_model_sha256"] != file_hash(model_path) or evaluation["validation_corpus_sha256"] != file_hash(validation_path):
        raise ValueError("evaluation not bound to frozen model and validation corpus")
    if model["compiler_sha256"] != evaluation["compiler_sha256"]:
        raise ValueError("model/evaluation compiler digest mismatch")
    if model["automatic_lowering_selection_enabled"] is not False or evaluation["automatic_lowering_selection_enabled"] is not False:
        raise ValueError("prospective evaluation must not enable lowering selection")
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("saved model differs from an independent refit on audited training corpus")
    reevaluated = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != reevaluated:
        raise ValueError("saved evaluation differs from an independent held-out replay")
    inventory = {}
    for split, corpus in (("train", train), ("validation", validation)):
        inventory[split] = {name: {
            "family": case["family"],
            "source_sha256": case["source_sha256"],
            "compiler_sha256": case["compiler_sha256"],
            "lowering": case["lowering"], "profile": case["profile"],
            "visible_fri": case["visible_fri"],
            "raw": case["raw"], "padded": case["padded"],
            "preprocessed_cells": case["preprocessed_cells"],
            "package_build": case["package_build"],
            "assignment_sha256": case["assignment_sha256"],
            "proof_sha256": [trial["proof_sha256"] for trial in case["trials"]],
        } for name, case in sorted(corpus["cases"].items())}
    return {
        "schema": "s31-stage-aware-cost-pinned-audit-v1",
        "protocol_sha256": protocol_sha,
        "training_corpus_sha256": file_hash(train_path),
        "frozen_model_sha256": file_hash(model_path),
        "validation_corpus_sha256": file_hash(validation_path),
        "evaluation_sha256": file_hash(evaluation_path),
        "host": train["host"], "compiler_sha256": model["compiler_sha256"],
        "training_programs": len(train["cases"]),
        "validation_programs": len(validation["cases"]),
        "training_controls": train_controls,
        "validation_controls": validation_controls,
        "program_inventory": inventory,
        "model": model,
        "accuracy": evaluation["accuracy"],
        "programs": evaluation["programs"],
        "local_accuracy_gate_pass": evaluation["local_accuracy_gate_pass"],
        "automatic_lowering_selection_enabled": False,
        "limitations": evaluation["interpretation"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("train", type=Path)
    parser.add_argument("model", type=Path)
    parser.add_argument("validation", type=Path)
    parser.add_argument("evaluation", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = publish(args.train, args.model, args.validation, args.evaluation)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
