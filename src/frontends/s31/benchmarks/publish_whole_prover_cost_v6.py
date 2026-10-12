#!/usr/bin/env python3
"""Independently replay and pin a frozen prospective v6 cost result."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from benchmark_whole_prover_cost_v3 import (
    chip_manifest_binding, measurement_tool_digest, s31,
)
from benchmark_whole_prover_cost_v6 import (
    TOOL_SOURCES, check_build_inventory, require_frozen_pins,
    require_model_anchor, require_protocol_anchor,
)
from publish_stage_aware_cost_v1 import audit_corpus, file_hash
from publish_whole_prover_cost_v3 import audit_case_artifacts
from whole_prover_predictor_v6 import PROTOCOL, evaluate, fit_model


def assert_build_case_binding(name: str, built: dict, case: dict) -> None:
    if (built["source_sha256"] != case["source_sha256"] or
        built["package_build"] != case["package_build"] or
        built.get("chip_manifest_binding") != case["chip_manifest_binding"]):
        raise ValueError(f"{name}: final corpus differs from saved build inventory")


def publish(train_path: Path, model_path: Path, validation_path: Path,
            evaluation_path: Path, externally_recorded_model_sha256: str,
            externally_recorded_protocol_sha256: str,
            protocol_anchor_commit: str, model_anchor_commit: str) -> dict:
    if not re.fullmatch(r"[0-9a-f]{64}", externally_recorded_model_sha256):
        raise ValueError("expected externally recorded model SHA-256")
    if not re.fullmatch(r"[0-9a-f]{64}", externally_recorded_protocol_sha256):
        raise ValueError("expected externally recorded protocol SHA-256")
    if file_hash(PROTOCOL) != externally_recorded_protocol_sha256:
        raise ValueError("protocol differs from externally recorded prebuild SHA")
    if file_hash(model_path) != externally_recorded_model_sha256:
        raise ValueError("frozen model differs from externally recorded pre-validation SHA")
    train, train_controls = audit_corpus(train_path, "train",
                                         "s31-whole-prover-cost-corpus-v6")
    validation, validation_controls = audit_corpus(
        validation_path, "validation", "s31-whole-prover-cost-corpus-v6")
    model = json.loads(model_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    protocol = json.loads(PROTOCOL.read_text())
    require_frozen_pins(protocol)
    protocol_anchor = require_protocol_anchor(
        protocol, externally_recorded_protocol_sha256, protocol_anchor_commit)
    model_anchor = require_model_anchor(
        model, externally_recorded_model_sha256,
        externally_recorded_protocol_sha256, model_anchor_commit,
        protocol_anchor_commit)
    protocol_sha = file_hash(PROTOCOL)
    if train["protocol_sha256"] != protocol_sha or validation["protocol_sha256"] != protocol_sha:
        raise ValueError("corpus/protocol digest mismatch")
    tool_sha = measurement_tool_digest(TOOL_SOURCES)
    if (model["compiler_sha256"] != protocol["compiler_sha256"] or
        tool_sha != protocol["measurement_tool_sha256"]):
        raise ValueError("frozen v6 source/tool pins do not match the audited model")
    if (train.get("measurement_tool_sha256") != tool_sha or
        validation.get("measurement_tool_sha256") != tool_sha):
        raise ValueError("saved corpus differs from pinned measurement tool bytes")
    if model["training_corpus_sha256"] != file_hash(train_path):
        raise ValueError("frozen model does not bind audited training corpus")
    if validation["frozen_model_sha256"] != externally_recorded_model_sha256:
        raise ValueError("held-out corpus does not bind frozen model")
    if (evaluation["frozen_model_sha256"] != externally_recorded_model_sha256 or
        evaluation["validation_corpus_sha256"] != file_hash(validation_path)):
        raise ValueError("evaluation does not bind frozen model and held-out corpus")
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("frozen model differs from independent training refit")
    replay = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != replay:
        raise ValueError("evaluation differs from held-out replay")
    if (model["automatic_lowering_selection_enabled"] is not False or
        evaluation["automatic_lowering_selection_enabled"] is not False):
        raise ValueError("cost audit must not enable automatic lowering")
    build_inventories = {
        "train": check_build_inventory(
            train_path.parent, "train", protocol, protocol_sha,
            protocol_anchor_commit=protocol_anchor_commit),
        "validation": check_build_inventory(
            validation_path.parent, "validation", protocol,
            protocol_sha, externally_recorded_model_sha256,
            protocol_anchor_commit, model_anchor_commit),
    }
    inventory = {}
    artifact_controls = {}
    for split, corpus, corpus_path in (("train", train, train_path),
                                       ("validation", validation, validation_path)):
        inventory[split] = {}
        artifact_controls[split] = {"saved_assignment_digest_matched": 0,
                                    "assignment_statement_matched": 0,
                                    "source_package_bound": 0}
        for name, case in sorted(corpus["cases"].items()):
            built = build_inventories[split]["programs"][name]
            assert_build_case_binding(name, built, case)
            package = corpus_path.parent / name / "package"
            manifest = s31.verify_package(package)
            if manifest["compiler_sha256"] != case["compiler_sha256"]:
                raise ValueError(f"{name}: audited package compiler mismatch")
            count = audit_case_artifacts(corpus_path.parent, name, case, manifest)
            artifact_controls[split]["saved_assignment_digest_matched"] += count
            artifact_controls[split]["assignment_statement_matched"] += count
            artifact_controls[split]["source_package_bound"] += 1
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
        "schema": "s31-whole-prover-cost-pinned-audit-v6",
        "protocol_sha256": protocol_sha,
        "externally_recorded_protocol_sha256": externally_recorded_protocol_sha256,
        "protocol_anchor_commit": protocol_anchor_commit,
        "protocol_anchor_recorded_at_utc": protocol_anchor["recorded_at_utc"],
        "model_anchor_commit": model_anchor_commit,
        "model_anchor_recorded_at_utc": model_anchor["recorded_at_utc"],
        "measurement_tool_sha256": tool_sha,
        "training_corpus_sha256": file_hash(train_path),
        "externally_recorded_frozen_model_sha256": externally_recorded_model_sha256,
        "validation_corpus_sha256": file_hash(validation_path),
        "evaluation_sha256": file_hash(evaluation_path),
        "compiler_sha256": model["compiler_sha256"],
        "host": train["host"],
        "accuracy_gate": protocol["accuracy_gate"],
        "training_controls": train_controls,
        "validation_controls": validation_controls,
        "artifact_controls": artifact_controls,
        "program_inventory": inventory,
        "model": model, "accuracy": evaluation["accuracy"],
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
    parser.add_argument("--expected-model-sha256", required=True)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--model-anchor-commit", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = publish(args.train, args.model, args.validation, args.evaluation,
                     args.expected_model_sha256, args.expected_protocol_sha256,
                     args.protocol_anchor_commit, args.model_anchor_commit)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
