#!/usr/bin/env python3
"""Read-only V7 replay after moving the content-addressed evidence directory."""

from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(BENCH.parent / "python"))

from benchmark_whole_prover_cost_v3 import chip_manifest_binding, s31
from benchmark_whole_prover_cost_v7 import check_build_inventory
from independent_v7_gate import check_saved_evaluation
from portable_v7 import verify as verify_manifest
from publish_whole_prover_cost_v7 import replay_trials
from v7_protocol import (MODEL, check_case_cost_geometry, require_model,
                         require_protocol)
from whole_prover_predictor_v7 import evaluate, fit_model

CHANGED = re.compile(r"(public_inputs|public_outputs)\.([A-Za-z_][A-Za-z0-9_]*)\[0\]\Z")


def suffix(path: str, parts: tuple[str, ...], label: str) -> None:
    parsed = Path(path)
    if not parsed.is_absolute() or parsed.parts[-len(parts):] != parts or ".." in parsed.parts:
        raise ValueError(f"{label}: original absolute path has wrong relative suffix")


def check_statement(assignment: dict, directory: Path, changed_field: str) -> None:
    public = {name: assignment[name] for name in ("public_inputs", "public_outputs")}
    statement = json.loads((directory / "statement.json").read_bytes())
    changed = json.loads((directory / "changed-statement.json").read_bytes())
    if statement != public:
        raise ValueError("saved public statement differs from assignment")
    match = CHANGED.fullmatch(changed_field)
    if match is None:
        raise ValueError("changed public field is not canonical")
    category, name = match.groups()
    try:
        before = statement[category][name][0]
        after = changed[category][name][0]
    except (KeyError, IndexError, TypeError) as error:
        raise ValueError("changed public field is missing") from error
    expected = copy.deepcopy(statement)
    expected[category][name][0] = after
    if before == after or expected != changed:
        raise ValueError("changed public statement modifies the wrong fields")


def audit_split(root: Path, split: str, corpus: dict, protocol: dict,
                protocol_sha: str, protocol_anchor_commit: str,
                model_sha: str | None, model_anchor_commit: str | None,
                native: bool) -> dict:
    base = root / split
    if (corpus.get("schema") != "s31-whole-prover-cost-corpus-v7" or
        corpus.get("split") != split or corpus.get("protocol_sha256") != protocol_sha or
        corpus.get("measurement_tool_sha256") != protocol["measurement_tool_sha256"] or
        corpus.get("host") != protocol["host"] or
        corpus.get("frozen_model_sha256") != model_sha):
        raise ValueError(f"{split}: corpus differs from frozen split, source, or model")
    inventory = protocol["inventory"][split]
    if corpus.get("cases", {}).keys() != inventory.keys():
        raise ValueError(f"{split}: program roster differs from frozen inventory")
    built = check_build_inventory(base, split, protocol, protocol_sha, model_sha,
                                  protocol_anchor_commit, model_anchor_commit)
    controls = {"packages": 0, "assignments": 0, "proofs": 0,
                "oracle_replays": 0, "native_controls": 0}
    for name, case in corpus["cases"].items():
        frozen = inventory[name]
        if (case["family"] != frozen["family"] or
            case["lowering"] != frozen["lowering"] or
            case["source_sha256"] != frozen["source_sha256"] or
            case["assignment_sha256"] != frozen["assignment_sha256"] or
            case["package_build"] != built["programs"][name]["package_build"]):
            raise ValueError(f"{split}/{name}: case differs from frozen workload")
        source_name = f"{name}.s31" if case["family"] == "fixed_width" else f"{name}.s31.json"
        source = base / "generated-sources" / source_name
        suffix(case["source"], ("generated-sources", source_name), f"{name} source")
        if s31.file_hash(source) != case["source_sha256"]:
            raise ValueError(f"{split}/{name}: source digest differs")
        package = base / name / "package"
        manifest = s31.verify_package(package)
        if (manifest["compiler_sha256"] != protocol["compiler_sha256"] or
            manifest["lowering"] != case["lowering"]):
            raise ValueError(f"{split}/{name}: native package differs from frozen stack")
        check_case_cost_geometry(case,
                                 json.loads((package / "cost-report.json").read_bytes()),
                                 f"{split}/{name}")
        if source_name.endswith(".s31"):
            if (manifest.get("source_text_sha256") != case["source_sha256"] or
                source.read_bytes() != (package / "source.s31").read_bytes()):
                raise ValueError(f"{split}/{name}: text source differs from sealed package")
        elif source.read_bytes() != (package / "source.s31.json").read_bytes():
            raise ValueError(f"{split}/{name}: JSON source differs from sealed package")
        binding = chip_manifest_binding(package) if case["family"] == "chip" else None
        if binding != case["chip_manifest_binding"]:
            raise ValueError(f"{split}/{name}: sealed component manifest differs")
        if len(case["trials"]) != protocol["samples_per_program"]:
            raise ValueError(f"{split}/{name}: wrong trial count")
        for index, compact in enumerate(case["trials"]):
            filename = f"{index:02d}.json"
            assignment_path = base / name / "assignments" / filename
            assignment = json.loads(assignment_path.read_bytes())
            if s31.assignment_digest(assignment_path) != case["assignment_sha256"][index]:
                raise ValueError(f"{split}/{name}[{index}]: assignment digest differs")
            directory = base / name / "trials" / f"{index:02d}"
            full = json.loads((directory / "trial-report.json").read_bytes())
            suffix(full["assignment"], (name, "assignments", filename),
                   f"{name}[{index}] assignment")
            suffix(full["package"], (name, "package"), f"{name}[{index}] package")
            if (full["schema"] != "s31-trial-v1" or
                full["program"] != manifest["name"] or
                full["program_sha256"] != manifest["program_sha256"] or
                full["canonical_ir_sha256"] != manifest["canonical_ir_sha256"] or
                full["lowering"] != case["lowering"] or
                full["profile"] != case["profile"] or
                any(full.get(key) != value for key, value in compact.items())):
                raise ValueError(f"{split}/{name}[{index}]: full trial report differs")
            proof = directory / "proof.bin"
            if (proof.stat().st_size != compact["proof_bytes"] or
                s31.file_hash(proof) != compact["proof_sha256"] or
                compact["native_verifier_accepted"] is not True or
                compact["independent_value_oracle"]["status"] != "passed"):
                raise ValueError(f"{split}/{name}[{index}]: proof or control differs")
            check_statement(assignment, directory,
                            compact["changed_public_statement_rejected"])
            controls["assignments"] += 1
            controls["proofs"] += 1
        replay_trials(base, name, case, manifest, native)
        controls["packages"] += 1
        controls["oracle_replays"] += len(case["trials"])
        controls["native_controls"] += 2 * len(case["trials"]) if native else 0
    return controls


def replay(root: Path, expected_manifest_sha: str, protocol_sha: str,
           protocol_anchor_commit: str, model_sha: str,
           model_anchor_commit: str, *, native: bool = False) -> dict:
    bundle = verify_manifest(root, expected_manifest_sha)
    if (bundle["protocol_sha256"] != protocol_sha or
        bundle["model_sha256"] != model_sha):
        raise ValueError("portable bundle differs from freeze identities")
    protocol = require_protocol(protocol_sha, protocol_anchor_commit, enforce_host=False)
    model = require_model(MODEL, model_sha, model_anchor_commit,
                          protocol_sha, protocol_anchor_commit)
    train_path = root / "train" / "whole-prover-corpus.json"
    validation_path = root / "validation" / "whole-prover-corpus.json"
    evaluation_path = root / "validation" / "evaluation.json"
    train = json.loads(train_path.read_bytes())
    validation = json.loads(validation_path.read_bytes())
    evaluation = json.loads(evaluation_path.read_bytes())
    if (model["training_corpus_sha256"] != s31.file_hash(train_path) or
        validation["frozen_model_sha256"] != model_sha or
        evaluation["frozen_model_sha256"] != model_sha or
        evaluation["validation_corpus_sha256"] != s31.file_hash(validation_path)):
        raise ValueError("portable corpus/model/evaluation hash binding differs")
    controls = {
        "train": audit_split(root, "train", train, protocol, protocol_sha,
                             protocol_anchor_commit, None, None, native),
        "validation": audit_split(root, "validation", validation, protocol,
                                  protocol_sha, protocol_anchor_commit,
                                  model_sha, model_anchor_commit, native),
    }
    refit = fit_model(train, protocol)
    if {key: value for key, value in model.items() if key != "training_corpus_sha256"} != refit:
        raise ValueError("frozen model differs from portable training refit")
    official = evaluate(model, validation, protocol)
    if {key: value for key, value in evaluation.items()
        if key not in ("frozen_model_sha256", "validation_corpus_sha256")} != official:
        raise ValueError("portable evaluation differs from predictor replay")
    second_source = check_saved_evaluation(model, validation, protocol, evaluation)
    return {"schema": "s31-whole-prover-v7-portable-replay-v1",
            "portable_manifest_sha256": expected_manifest_sha,
            "protocol_sha256": protocol_sha,
            "model_sha256": model_sha,
            "files_checked": len(bundle["files"]),
            "controls": controls,
            "independent_held_out_gate_replay": second_source,
            "local_accuracy_gate_pass": evaluation["local_accuracy_gate_pass"],
            "automatic_lowering_selection_enabled": False,
            "native_original_and_changed_replayed": native}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-model-sha256", required=True)
    parser.add_argument("--model-anchor-commit", required=True)
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    result = replay(args.root.resolve(), args.expected_manifest_sha256,
                    args.expected_protocol_sha256, args.protocol_anchor_commit,
                    args.expected_model_sha256, args.model_anchor_commit,
                    native=args.native)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
