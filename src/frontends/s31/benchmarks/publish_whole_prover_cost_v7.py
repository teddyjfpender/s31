#!/usr/bin/env python3
"""Read-only V7 artifact, oracle, model, and held-out gate replay."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "cost"))
sys.path.insert(0, str(HERE.parent / "python"))

from benchmark_whole_prover_cost_v3 import chip_manifest_binding, s31
from benchmark_whole_prover_cost_v7 import check_build_inventory
from independent_v7_gate import check_saved_evaluation
from oracle import evaluate_relation
from publish_stage_aware_cost_v1 import audit_corpus, file_hash
from publish_whole_prover_cost_v3 import audit_case_artifacts
from v7_protocol import (ROOT, check_case_cost_geometry, require_model,
                         require_protocol, tool_digest, tool_paths)
from whole_prover_predictor_v7 import evaluate, fit_model


def replay_trials(base: Path, name: str, case: dict, manifest: dict, native: bool) -> int:
    package = base / name / "package"
    relation = json.loads((package / "source.s31.json").read_bytes())
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key = package / "verification-key.json"
    for index, compact in enumerate(case["trials"]):
        trial = base / name / "trials" / f"{index:02d}"
        assignment = json.loads((base / name / "assignments" / f"{index:02d}.json").read_bytes())
        if compact["independent_value_oracle"]["computed_public_outputs"] != evaluate_relation(
            relation, assignment
        ):
            raise ValueError(f"{name}[{index}]: independent value oracle replay differs")
        report = json.loads((trial / "trial-report.json").read_bytes())
        provenance = report["independent_value_oracle_provenance"]["source_sha256"]
        for filename in ("oracle.py", "poseidon2_oracle.py"):
            source = HERE.parent / "python" / filename
            if provenance[str(source.relative_to(ROOT))] != file_hash(source):
                raise ValueError(f"{name}[{index}]: oracle source provenance differs")
        if native:
            for filename, expected in (("statement.json", True),
                                       ("changed-statement.json", False)):
                result = subprocess.run([str(verifier), str(trial / "proof.bin"),
                                         str(trial / filename), str(key)],
                                        capture_output=True, check=False)
                if (result.returncode == 0) is not expected:
                    raise ValueError(f"{name}[{index}]: native {filename} control differs")
    return len(case["trials"])


def publish(train_path: Path, model_path: Path, validation_path: Path,
            evaluation_path: Path, protocol_sha: str, protocol_anchor_commit: str,
            model_sha: str, model_anchor_commit: str, *, native: bool = False) -> dict:
    protocol = require_protocol(protocol_sha, protocol_anchor_commit, enforce_host=False)
    model = require_model(model_path, model_sha, model_anchor_commit,
                          protocol_sha, protocol_anchor_commit)
    train, train_controls = audit_corpus(train_path, "train",
                                         "s31-whole-prover-cost-corpus-v7")
    validation, validation_controls = audit_corpus(validation_path, "validation",
                                                   "s31-whole-prover-cost-corpus-v7")
    evaluation = json.loads(evaluation_path.read_bytes())
    if (train["protocol_sha256"] != protocol_sha or
        validation["protocol_sha256"] != protocol_sha or
        model["training_corpus_sha256"] != file_hash(train_path) or
        validation["frozen_model_sha256"] != model_sha or
        evaluation["frozen_model_sha256"] != model_sha or
        evaluation["validation_corpus_sha256"] != file_hash(validation_path) or
        train["host"] != validation["host"] or train["host"] != protocol["host"] or
        train["measurement_tool_sha256"] != protocol["measurement_tool_sha256"] or
        validation["measurement_tool_sha256"] != protocol["measurement_tool_sha256"] or
        tool_digest(tool_paths()) != protocol["measurement_tool_sha256"]):
        raise ValueError("V7 corpus/model/evaluation differs from frozen pins")
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("frozen model differs from read-only training refit")
    replay = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != replay:
        raise ValueError("held-out evaluation differs from read-only replay")
    second_source = check_saved_evaluation(model, validation, protocol, evaluation)
    controls = {}
    program_inventory = {}
    for split, corpus, corpus_path, frozen_sha, model_anchor in (
        ("train", train, train_path, None, None),
        ("validation", validation, validation_path, model_sha, model_anchor_commit),
    ):
        base = corpus_path.parent
        built = check_build_inventory(base, split, protocol, protocol_sha, frozen_sha,
                                      protocol_anchor_commit, model_anchor)
        controls[split] = {"packages": 0, "assignments_and_statements": 0,
                           "oracle_replays": 0, "native_replays": 0}
        program_inventory[split] = {}
        for name, case in sorted(corpus["cases"].items()):
            item = protocol["inventory"][split][name]
            if (case["source_sha256"] != item["source_sha256"] or
                case["assignment_sha256"] != item["assignment_sha256"] or
                case["package_build"] != built["programs"][name]["package_build"]):
                raise ValueError(f"{split}/{name}: corpus differs from frozen build inventory")
            package = base / name / "package"
            manifest = s31.verify_package(package)
            if manifest["compiler_sha256"] != protocol["compiler_sha256"]:
                raise ValueError(f"{split}/{name}: package compiler differs")
            check_case_cost_geometry(case,
                                     json.loads((package / "cost-report.json").read_bytes()),
                                     f"{split}/{name}")
            count = audit_case_artifacts(base, name, case, manifest)
            replay_trials(base, name, case, manifest, native)
            binding = chip_manifest_binding(package) if case["family"] == "chip" else None
            if binding != case["chip_manifest_binding"]:
                raise ValueError(f"{split}/{name}: sealed chip manifest differs")
            controls[split]["packages"] += 1
            controls[split]["assignments_and_statements"] += count
            controls[split]["oracle_replays"] += count
            controls[split]["native_replays"] += count if native else 0
            program_inventory[split][name] = {
                "family": case["family"], "source_sha256": case["source_sha256"],
                "assignment_sha256": case["assignment_sha256"],
                "proof_sha256": [trial["proof_sha256"] for trial in case["trials"]],
                "profile": case["profile"], "visible_fri": case["visible_fri"],
                "chip_manifest_binding": binding,
            }
    return {"schema": "s31-whole-prover-cost-pinned-audit-v7",
            "protocol_sha256": protocol_sha,
            "protocol_anchor_commit": protocol_anchor_commit,
            "model_sha256": model_sha, "model_anchor_commit": model_anchor_commit,
            "training_corpus_sha256": file_hash(train_path),
            "validation_corpus_sha256": file_hash(validation_path),
            "evaluation_sha256": file_hash(evaluation_path),
            "compiler_sha256": model["compiler_sha256"], "host": train["host"],
            "training_controls": train_controls,
            "validation_controls": validation_controls,
            "artifact_controls": controls, "program_inventory": program_inventory,
            "independent_held_out_gate_replay": second_source,
            "accuracy": evaluation["accuracy"], "programs": evaluation["programs"],
            "local_accuracy_gate_pass": evaluation["local_accuracy_gate_pass"],
            "automatic_lowering_selection_enabled": False,
            "limitations": "Local pinned-stack study; proof replay checks native acceptance and value-oracle agreement, not source-to-circuit soundness or cross-host transfer."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("train", "model", "validation", "evaluation"):
        parser.add_argument(name, type=Path)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-model-sha256", required=True)
    parser.add_argument("--model-anchor-commit", required=True)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = publish(args.train, args.model, args.validation, args.evaluation,
                     args.expected_protocol_sha256, args.protocol_anchor_commit,
                     args.expected_model_sha256, args.model_anchor_commit,
                     native=args.native)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
