#!/usr/bin/env python3
"""Collect the prospective V7 whole-prover corpus on one pinned stack.

Protocol and model anchors must be committed and externally recorded before
the respective training and validation native package builds.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "cost"))

from benchmark_whole_prover_cost_v3 import chip_manifest_binding, run_corpus, s31
from v7_protocol import (MIN_FREE_BYTES, PROTOCOL, inventory, require_model,
                         require_protocol, tool_paths, workloads)


def workload_cases(split: str, output: Path, samples: int, protocol: dict) -> list[dict]:
    return workloads(split, output, samples, protocol["splits"][split])


def check_build_inventory(output: Path, split: str, protocol: dict,
                          protocol_sha: str, model_sha: str | None,
                          protocol_anchor_commit: str,
                          model_anchor_commit: str | None) -> dict:
    saved = json.loads((output / "whole-prover-build-inventory.json").read_bytes())
    if (saved.get("schema") != "s31-whole-prover-build-inventory-v7" or
        saved.get("split") != split or saved.get("protocol_sha256") != protocol_sha or
        saved.get("compiler_sha256") != protocol["compiler_sha256"] or
        saved.get("measurement_tool_sha256") != protocol["measurement_tool_sha256"] or
        saved.get("frozen_model_sha256") != model_sha or
        saved.get("protocol_anchor_commit") != protocol_anchor_commit or
        saved.get("model_anchor_commit") != model_anchor_commit):
        raise ValueError("V7 build inventory differs from committed freeze pins")
    expected = protocol["inventory"][split]
    if saved.get("programs", {}).keys() != expected.keys():
        raise ValueError("V7 build inventory program roster differs from freeze")
    for name, item in expected.items():
        record = saved["programs"][name]
        source = next((path for path in (
            output / "generated-sources" / f"{name}.s31",
            output / "generated-sources" / f"{name}.s31.json") if path.is_file()), None)
        if source is None or s31.file_hash(source) != item["source_sha256"]:
            raise ValueError(f"{name}: source differs from frozen inventory")
        actual_assignments = [s31.assignment_digest(
            output / name / "assignments" / f"{index:02d}.json")
            for index in range(protocol["samples_per_program"])]
        if actual_assignments != item["assignment_sha256"]:
            raise ValueError(f"{name}: assignments differ from frozen inventory")
        package = output / name / "package"
        manifest = s31.verify_package(package)
        cost = json.loads((package / "cost-report.json").read_bytes())
        if (manifest["compiler_sha256"] != protocol["compiler_sha256"] or
            manifest["lowering"] != item["lowering"] or
            manifest["optimize"] != "ReleaseFast" or
            manifest["fri_fold_step"] != 1 or
            cost["profile"] != protocol["profile_by_family"][item["family"]] or
            s31.visible_fri(cost, item["lowering"]) != protocol["visible_fri"] or
            record.get("source_sha256") != item["source_sha256"] or
            record["package_build"].get("package_reused") is not False):
            raise ValueError(f"{name}: package/build record differs from freeze")
        expected_chip = chip_manifest_binding(package) if item["family"] == "chip" else None
        if record.get("chip_manifest_binding") != expected_chip:
            raise ValueError(f"{name}: sealed chip component manifest differs")
        build = json.loads((output / name / "package-build-record.json").read_bytes())
        if (build["source_sha256"] != item["source_sha256"] or
            build["compiler_sha256"] != protocol["compiler_sha256"] or
            build["measurement_tool_sha256"] != protocol["measurement_tool_sha256"] or
            build["package_build"] != record["package_build"]):
            raise ValueError(f"{name}: package build record differs")
    return saved


def run(args: argparse.Namespace) -> None:
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Regenerate both splits in a disposable directory. The saved evidence is
    # never repaired or overwritten by this admission check.
    with tempfile.TemporaryDirectory(prefix="s31-v7-preflight-") as directory:
        protocol = require_protocol(args.expected_protocol_sha256,
                                    args.protocol_anchor_commit, Path(directory))
    if shutil.disk_usage(output).free < MIN_FREE_BYTES:
        raise ValueError("V7 native phase needs at least 8 GiB of available disk")
    model_sha = args.expected_model_sha256
    if args.split == "validation":
        if args.model is None or args.model_anchor_commit is None or model_sha is None:
            raise ValueError("held-out native work requires the committed frozen model anchor")
        model = require_model(args.model, model_sha, args.model_anchor_commit,
                              args.expected_protocol_sha256, args.protocol_anchor_commit)
        if (model["protocol_sha256"] != args.expected_protocol_sha256 or
            model["compiler_sha256"] != protocol["compiler_sha256"] or
            model["measurement_tool_sha256"] != protocol["measurement_tool_sha256"] or
            model["training_host"] != protocol["host"]):
            raise ValueError("frozen V7 model differs from protocol stack")
    elif args.model is not None or model_sha is not None or args.model_anchor_commit is not None:
        raise ValueError("training phase cannot consume a held-out model")
    if args.phase == "prove":
        check_build_inventory(output, args.split, protocol, args.expected_protocol_sha256,
                              model_sha, args.protocol_anchor_commit,
                              args.model_anchor_commit)
    run_corpus(args, protocol_path=PROTOCOL, protocol_schema="s31-whole-prover-cost-protocol-v7",
               model_schema="s31-whole-prover-cost-model-v7",
               corpus_schema="s31-whole-prover-cost-corpus-v7",
               build_schema="s31-whole-prover-build-inventory-v7",
               workloads=workload_cases, tool_sources=tuple(tool_paths()))
    if args.phase == "build":
        path = output / "whole-prover-build-inventory.json"
        built = json.loads(path.read_bytes())
        built["protocol_anchor_commit"] = args.protocol_anchor_commit
        built["model_anchor_commit"] = args.model_anchor_commit
        built["frozen_model_sha256"] = model_sha
        s31.write_json(path, built)
        check_build_inventory(output, args.split, protocol, args.expected_protocol_sha256,
                              model_sha, args.protocol_anchor_commit,
                              args.model_anchor_commit)
    else:
        corpus = json.loads((output / "whole-prover-corpus.json").read_bytes())
        if (corpus.get("protocol_sha256") != args.expected_protocol_sha256 or
            corpus.get("frozen_model_sha256") != model_sha):
            raise ValueError("V7 corpus differs from frozen protocol or model")
        for name, case in corpus["cases"].items():
            item = protocol["inventory"][args.split][name]
            if (case["source_sha256"] != item["source_sha256"] or
                case["assignment_sha256"] != item["assignment_sha256"]):
                raise ValueError(f"{name}: native corpus differs from frozen inputs")
        print("V7 corpus SHA-256:", hashlib.sha256(
            (output / "whole-prover-corpus.json").read_bytes()).hexdigest())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove"), required=True)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-model-sha256")
    parser.add_argument("--model-anchor-commit")
    parser.add_argument("--model", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    run(parser.parse_args())


if __name__ == "__main__":
    main()
