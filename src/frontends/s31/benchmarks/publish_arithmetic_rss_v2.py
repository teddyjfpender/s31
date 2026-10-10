#!/usr/bin/env python3
"""Audit and pin the independent arithmetic RSS v2 result."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from arithmetic_rss_predictor_v2 import PROTOCOL, evaluate, fit_model
from publish_stage_aware_cost_v1 import audit_corpus, file_hash

SCHEMA = "s31-arithmetic-rss-corpus-v2"


def publish(train_path: Path, model_path: Path, validation_path: Path,
            evaluation_path: Path) -> dict:
    train, train_controls = audit_corpus(train_path, "train", SCHEMA)
    validation, validation_controls = audit_corpus(validation_path, "validation", SCHEMA)
    model = json.loads(model_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    protocol = json.loads(PROTOCOL.read_text())
    protocol_sha = file_hash(PROTOCOL)
    if train["protocol_sha256"] != protocol_sha or validation["protocol_sha256"] != protocol_sha:
        raise ValueError("protocol digest mismatch")
    if model["training_corpus_sha256"] != file_hash(train_path):
        raise ValueError("model not bound to audited training corpus")
    if validation["frozen_model_sha256"] != file_hash(model_path):
        raise ValueError("validation not bound to frozen model")
    if evaluation["frozen_model_sha256"] != file_hash(model_path) or evaluation["validation_corpus_sha256"] != file_hash(validation_path):
        raise ValueError("evaluation not bound to validation corpus and frozen model")
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("saved model differs from independent training refit")
    replay = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != replay:
        raise ValueError("saved held-out evaluation differs from independent replay")
    if model["automatic_lowering_selection_enabled"] is not False or evaluation["automatic_lowering_selection_enabled"] is not False:
        raise ValueError("RSS follow-up must not enable automatic lowering")
    inventory = {}
    for split, corpus in (("train", train), ("validation", validation)):
        inventory[split] = {name: {
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
        "schema": "s31-arithmetic-rss-pinned-audit-v2",
        "protocol_sha256": protocol_sha,
        "training_corpus_sha256": file_hash(train_path),
        "frozen_model_sha256": file_hash(model_path),
        "validation_corpus_sha256": file_hash(validation_path),
        "evaluation_sha256": file_hash(evaluation_path),
        "host": train["host"], "compiler_sha256": model["compiler_sha256"],
        "training_controls": train_controls,
        "validation_controls": validation_controls,
        "program_inventory": inventory,
        "model": model,
        "accuracy": evaluation["accuracy"],
        "programs": evaluation["programs"],
        "targeted_rss_accuracy_gate_pass": evaluation["targeted_rss_accuracy_gate_pass"],
        "automatic_lowering_selection_enabled": False,
        "limitations": evaluation["limitations"],
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
