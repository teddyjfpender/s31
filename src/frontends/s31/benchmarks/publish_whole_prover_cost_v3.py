#!/usr/bin/env python3
"""Audit native artifacts and pin the prospective whole-prover v3 result."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from benchmark_whole_prover_cost_v3 import chip_manifest_binding, s31
from publish_stage_aware_cost_v1 import audit_corpus, file_hash
from whole_prover_predictor_v3 import PROTOCOL, evaluate, fit_model


def publish(train_path: Path, model_path: Path, validation_path: Path,
            evaluation_path: Path) -> dict:
    train, train_controls = audit_corpus(train_path, "train", "s31-whole-prover-cost-corpus-v3.1")
    validation, validation_controls = audit_corpus(
        validation_path, "validation", "s31-whole-prover-cost-corpus-v3.1")
    model = json.loads(model_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    protocol = json.loads(PROTOCOL.read_text())
    protocol_sha = file_hash(PROTOCOL)
    if train["protocol_sha256"] != protocol_sha or validation["protocol_sha256"] != protocol_sha:
        raise ValueError("corpus/protocol digest mismatch")
    if model["training_corpus_sha256"] != file_hash(train_path):
        raise ValueError("frozen model does not bind audited training corpus")
    if validation["frozen_model_sha256"] != file_hash(model_path):
        raise ValueError("held-out corpus does not bind frozen model")
    if (evaluation["frozen_model_sha256"] != file_hash(model_path) or
        evaluation["validation_corpus_sha256"] != file_hash(validation_path)):
        raise ValueError("evaluation does not bind frozen model and held-out corpus")
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("frozen model differs from independent training refit")
    replay = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != replay:
        raise ValueError("evaluation differs from held-out replay")
    if model["automatic_lowering_selection_enabled"] is not False or evaluation["automatic_lowering_selection_enabled"] is not False:
        raise ValueError("cost audit must not enable automatic lowering")
    inventory = {}
    for split, corpus, corpus_path in (("train", train, train_path),
                                       ("validation", validation, validation_path)):
        inventory[split] = {}
        for name, case in sorted(corpus["cases"].items()):
            package = corpus_path.parent / name / "package"
            manifest = s31.verify_package(package)
            if manifest["compiler_sha256"] != case["compiler_sha256"]:
                raise ValueError(f"{name}: audited package compiler mismatch")
            binding = chip_manifest_binding(package) if case["family"] == "chip" else None
            if binding != case["chip_manifest_binding"]:
                raise ValueError(f"{name}: saved chip manifest binding mismatch")
            inventory[split][name] = {
                "family": case["family"], "source_sha256": case["source_sha256"],
                "compiler_sha256": case["compiler_sha256"],
                "lowering": case["lowering"], "profile": case["profile"],
                "visible_fri": case["visible_fri"],
                "raw": case["raw"], "padded": case["padded"],
                "preprocessed_cells": case["preprocessed_cells"],
                "package_build": case["package_build"],
                "chip_manifest_binding": binding,
                "assignment_sha256": case["assignment_sha256"],
                "proof_sha256": [trial["proof_sha256"] for trial in case["trials"]],
            }
    return {
        "schema": "s31-whole-prover-cost-pinned-audit-v3.1",
        "protocol_sha256": protocol_sha,
        "training_corpus_sha256": file_hash(train_path),
        "frozen_model_sha256": file_hash(model_path),
        "validation_corpus_sha256": file_hash(validation_path),
        "evaluation_sha256": file_hash(evaluation_path),
        "compiler_sha256": model["compiler_sha256"],
        "host": train["host"],
        "accuracy_gate": protocol["accuracy_gate"],
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
