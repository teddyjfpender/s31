#!/usr/bin/env python3
"""Collect fresh v6 packages only after explicit source/tool fingerprint freeze."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from benchmark_whole_prover_cost_v3 import (
    HERE, ROOT, chip_manifest_binding, hash_assignment, hash_program,
    measurement_tool_digest,
    quotient_source, recurrence_assignment, recurrence_program, run_corpus,
    s31, signed_assignment,
)
from whole_prover_predictor_v3 import expected_names

PROTOCOL = HERE.parents[2] / "design/s31/measurements/whole-prover-cost-v6.json"
PROTOCOL_ANCHOR = ROOT / "design/s31/measurements/language/whole-prover-cost-v6-protocol-freeze.json"
MODEL_ANCHOR = ROOT / "design/s31/measurements/language/whole-prover-cost-v6-model-freeze.json"
TOOL_SOURCES = (tuple(sorted((HERE / "benchmarks").glob("*.py"))) +
                tuple(sorted((HERE / "python").rglob("*.py"))))


def tool_source_inventory() -> list[str]:
    return [path.relative_to(ROOT).as_posix() for path in TOOL_SOURCES]


def checked_sha(path: Path, expected: str, description: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{64}", expected or ""):
        raise ValueError(f"v6 requires a full externally recorded {description} SHA-256")
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError(f"v6 {description} differs from externally recorded SHA")


def committed_anchor(path: Path, commit: str, schema: str) -> dict:
    """Require the anchor's exact current bytes to exist in an ancestor commit."""
    if not re.fullmatch(r"[0-9a-f]{40}", commit or ""):
        raise ValueError("v6 requires the full externally recorded anchor commit")
    relative = path.relative_to(ROOT).as_posix()
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       commit, "HEAD"], check=False).returncode != 0:
        raise ValueError("v6 freeze-anchor commit is not an ancestor of this checkout")
    try:
        committed = subprocess.check_output(
            ["git", "-C", str(ROOT), "show", f"{commit}:{relative}"])
        current = path.read_bytes()
    except (subprocess.CalledProcessError, FileNotFoundError) as error:
        raise ValueError("v6 committed freeze anchor is unavailable") from error
    if current != committed:
        raise ValueError("v6 freeze anchor differs from its recorded commit")
    anchor = json.loads(current)
    if anchor.get("schema") != schema:
        raise ValueError("v6 freeze anchor has wrong schema")
    try:
        recorded = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError("v6 freeze anchor lacks a valid timestamp") from error
    if recorded.tzinfo is None or recorded > datetime.now(timezone.utc):
        raise ValueError("v6 freeze anchor timestamp must be aware and not future")
    return anchor


def require_protocol_anchor(protocol: dict, expected_sha: str,
                            anchor_commit: str) -> dict:
    anchor = committed_anchor(PROTOCOL_ANCHOR, anchor_commit,
                              "s31-whole-prover-v6-protocol-freeze")
    expected = {"protocol_sha256": expected_sha,
                "source_base_commit": protocol["source_base_commit"],
                "engine_gitlink_commit": protocol["engine_gitlink_commit"],
                "compiler_sha256": protocol["compiler_sha256"],
                "measurement_tool_sha256": protocol["measurement_tool_sha256"]}
    if any(anchor.get(key) != value for key, value in expected.items()):
        raise ValueError("v6 committed protocol anchor differs from frozen pins")
    return anchor


def require_model_anchor(model: dict, expected_model_sha: str,
                         expected_protocol_sha: str, model_anchor_commit: str,
                         protocol_anchor_commit: str) -> dict:
    if model_anchor_commit == protocol_anchor_commit or subprocess.run(
        ["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
         protocol_anchor_commit, model_anchor_commit], check=False
    ).returncode != 0:
        raise ValueError("v6 model anchor must descend the protocol anchor")
    anchor = committed_anchor(MODEL_ANCHOR, model_anchor_commit,
                              "s31-whole-prover-v6-model-freeze")
    expected = {"protocol_sha256": expected_protocol_sha,
                "frozen_model_sha256": expected_model_sha,
                "training_corpus_sha256": model["training_corpus_sha256"]}
    if any(anchor.get(key) != value for key, value in expected.items()):
        raise ValueError("v6 committed model anchor differs from frozen model")
    return anchor


def div_rem_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_div_rem_cost_v6(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {2 * count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    let result = std::array::concat(std::int::limbs(quotient), "
            f"std::int::limbs(remainder));\n"
            f"    result\n"
            f"}}\n")


def remainder_source(width: int) -> str:
    count = (width + 15) // 16
    return (f"use std@1;\n\n"
            f"circuit i{width}_remainder_cost_v6(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    let result = std::int::limbs(remainder);\n"
            f"    result\n"
            f"}}\n")


def remainder_assignment(width: int, index: int, output_name: str) -> dict:
    assignment = signed_assignment(width, index, False, output_name)
    count = (width + 15) // 16
    assignment["public_outputs"][output_name] = assignment["public_outputs"][output_name][count:]
    return assignment


def require_frozen_pins(protocol: dict) -> None:
    """Refuse native observation while the prospective source/tool pin is draft."""
    for key in ("source_base_commit", "engine_gitlink_commit", "compiler_sha256",
                "measurement_tool_sha256"):
        if not re.fullmatch(r"[0-9a-f]{40}" if key.endswith("commit") else
                            r"[0-9a-f]{64}", protocol.get(key) or ""):
            raise ValueError(f"v6 {key} must be pinned before a native build or trial")
    if protocol.get("status") != "frozen-before-any-v6-native-observation":
        raise ValueError("v6 protocol status must record the prospective native freeze")
    if protocol.get("measurement_tool_paths") != tool_source_inventory():
        raise ValueError("v6 pinned measurement tool path inventory differs from checkout")
    if protocol["measurement_tool_sha256"] != measurement_tool_digest(TOOL_SOURCES):
        raise ValueError("v6 pinned measurement tool digest differs from source bytes")
    if protocol["compiler_sha256"] != s31.compiler_fingerprint():
        raise ValueError("v6 pinned compiler digest differs from source bytes")
    engine = subprocess.check_output(
        ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
        text=True).strip()
    if engine != protocol["engine_gitlink_commit"]:
        raise ValueError("v6 pinned engine gitlink differs from checkout")
    source_base = subprocess.run(
        ["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
         protocol["source_base_commit"], "HEAD"], check=False)
    if source_base.returncode != 0:
        raise ValueError("v6 pinned S31 source base is not an ancestor of this checkout")


def check_build_inventory(output: Path, split: str, protocol: dict,
                          expected_protocol_sha256: str,
                          expected_model_sha256: str | None = None,
                          protocol_anchor_commit: str | None = None,
                          model_anchor_commit: str | None = None) -> None:
    path = output / "whole-prover-build-inventory.json"
    inventory = json.loads(path.read_text())
    if (inventory.get("schema") != "s31-whole-prover-build-inventory-v6" or
        inventory.get("split") != split or
        inventory.get("protocol_sha256") != expected_protocol_sha256):
        raise ValueError("v6 build inventory protocol SHA or split mismatch")
    if (inventory.get("compiler_sha256") != protocol["compiler_sha256"] or
        inventory.get("measurement_tool_sha256") != protocol["measurement_tool_sha256"]):
        raise ValueError("v6 build inventory compiler/tool SHA mismatch")
    if inventory.get("frozen_model_sha256") != expected_model_sha256:
        raise ValueError("v6 build inventory frozen model SHA mismatch")
    if (inventory.get("protocol_anchor_commit") != protocol_anchor_commit or
        inventory.get("model_anchor_commit") != model_anchor_commit):
        raise ValueError("v6 build inventory freeze-anchor commit mismatch")
    programs = inventory.get("programs")
    if not isinstance(programs, dict) or set(programs) != expected_names(split, protocol):
        raise ValueError("v6 build inventory program set mismatch")
    for name, record in sorted(programs.items()):
        if record["package_build"].get("package_reused") is not False:
            raise ValueError("v6 proof phase requires fresh package builds")
        build_record = json.loads((output / name / "package-build-record.json").read_text())
        if (record.get("source_sha256") != build_record.get("source_sha256") or
            record["package_build"] != build_record.get("package_build") or
            build_record.get("compiler_sha256") != protocol["compiler_sha256"] or
            build_record.get("measurement_tool_sha256") !=
            protocol["measurement_tool_sha256"]):
            raise ValueError(f"{name}: build inventory differs from package build record")
        sources = [path for path in (
            output / "generated-sources" / f"{name}.s31",
            output / "generated-sources" / f"{name}.s31.json",
        ) if path.is_file()]
        if len(sources) != 1 or s31.file_hash(sources[0]) != record["source_sha256"]:
            raise ValueError(f"{name}: build inventory differs from generated source")
        expected_chip = (chip_manifest_binding(output / name / "package")
                         if name.startswith("chip_") else None)
        if record.get("chip_manifest_binding") != expected_chip:
            raise ValueError(f"{name}: build inventory differs from chip package binding")
    return inventory


def workload_cases(split: str, output: Path, samples: int, protocol: dict) -> list[dict]:
    spec = protocol["splits"][split]
    source_dir = output / "generated-sources"
    source_dir.mkdir(parents=True, exist_ok=True)
    seed = spec["assignment_index_base"]
    workloads = []
    for family, key, lowering, offset in (
        ("arithmetic", "arithmetic_rounds", "direct-gate", 0),
        ("chip", "chip_rounds", "direct-chip", 100000),
    ):
        for rounds in spec[key]:
            if family == "chip" and (rounds < 16 or rounds > 32768 or
                                     rounds & (rounds - 1)):
                raise ValueError("direct-chip rounds must be powers of two from 16 to 32768")
            name = f"{family}_{rounds}"
            source = source_dir / f"{name}.s31.json"
            body = [{"op": "square"}, {"op": "add_const",
                                       "constant": spec[f"{family}_constant"]}]
            s31.write_json(source, recurrence_program(name, rounds, body))
            workloads.append({"name": name, "family": family, "source": source,
                              "lowering": lowering,
                              "assignments": [recurrence_assignment(rounds, body, seed + offset + i)
                                              for i in range(samples)]})
    for depth in spec["hash_depths"]:
        name = f"hash_{depth}"
        source = source_dir / f"{name}.s31.json"
        relation = hash_program(depth)
        relation["name"] = f"blake_chain_v6_{depth}"
        s31.write_json(source, relation)
        workloads.append({"name": name, "family": "hash", "source": source,
                          "lowering": "gate",
                          "assignments": [hash_assignment(depth, seed + i)
                                          for i in range(samples)]})
    for width in spec["signed_widths"]:
        kind = (spec["signed_128_output"] if width == 128 else
                "quotient" if split == "validation" else "div_rem")
        name = f"signed_{kind}_{width}"
        source = source_dir / f"{name}.s31"
        if kind == "quotient":
            source.write_text(quotient_source(width).replace("_cost_v1", "_cost_v6"))
        elif kind == "remainder":
            source.write_text(remainder_source(width))
        else:
            source.write_text(div_rem_source(width))
        from package.context import lower_text

        relation, _, _ = lower_text(source)
        if len(relation["public_outputs"]) != 1:
            raise ValueError(f"{name}: expected one public output")
        output_name = relation["public_outputs"][0]
        workloads.append({"name": name, "family": "fixed_width", "source": source,
                          "lowering": "direct-gate",
                          "assignments": [(remainder_assignment(width, seed + i, output_name)
                                           if kind == "remainder" else
                                           signed_assignment(width, seed + i,
                                                             kind == "quotient", output_name))
                                          for i in range(samples)]})
    return workloads


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "validation"), required=True)
    parser.add_argument("--phase", choices=("build", "prove"), required=True)
    parser.add_argument("--expected-protocol-sha256", required=True,
                        help="full digest recorded externally before the first V6 build")
    parser.add_argument("--protocol-anchor-commit", required=True,
                        help="committed protocol freeze JSON recorded before the first V6 build")
    parser.add_argument("--expected-model-sha256",
                        help="full digest recorded externally before held-out builds")
    parser.add_argument("--model-anchor-commit",
                        help="committed model freeze JSON recorded before held-out builds")
    parser.add_argument("--model", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    checked_sha(PROTOCOL, args.expected_protocol_sha256, "protocol")
    protocol_bytes = PROTOCOL.read_bytes()
    protocol = json.loads(protocol_bytes)
    require_frozen_pins(protocol)
    require_protocol_anchor(protocol, args.expected_protocol_sha256,
                            args.protocol_anchor_commit)
    if args.split == "validation":
        if (args.model is None or
            not re.fullmatch(r"[0-9a-f]{64}", args.expected_model_sha256 or "") or
            args.model_anchor_commit is None):
            raise ValueError("v6 validation requires an externally recorded full model SHA")
        checked_sha(args.model, args.expected_model_sha256, "model")
        require_model_anchor(json.loads(args.model.read_text()),
                             args.expected_model_sha256, args.expected_protocol_sha256,
                             args.model_anchor_commit, args.protocol_anchor_commit)
    elif (args.model is not None or args.expected_model_sha256 is not None or
          args.model_anchor_commit is not None):
        raise ValueError("v6 train phase must not accept a validation model")
    if shutil.disk_usage(ROOT).free < protocol["minimum_available_disk_bytes_before_native_phase"]:
        raise ValueError("v6 native phase needs at least eight GiB of free artifact space")
    if args.phase == "prove":
        check_build_inventory(args.out.resolve(), args.split, protocol,
                              args.expected_protocol_sha256,
                              args.expected_model_sha256,
                              args.protocol_anchor_commit,
                              args.model_anchor_commit)
    run_corpus(args, protocol_path=PROTOCOL,
               protocol_schema="s31-whole-prover-cost-protocol-v6",
               model_schema="s31-whole-prover-cost-model-v6",
               corpus_schema="s31-whole-prover-cost-corpus-v6",
               build_schema="s31-whole-prover-build-inventory-v6",
               workloads=workload_cases, tool_sources=TOOL_SOURCES)
    if args.phase == "build":
        path = args.out.resolve() / "whole-prover-build-inventory.json"
        inventory = json.loads(path.read_text())
        inventory["protocol_anchor_commit"] = args.protocol_anchor_commit
        inventory["model_anchor_commit"] = args.model_anchor_commit
        inventory["frozen_model_sha256"] = args.expected_model_sha256
        s31.write_json(path, inventory)


if __name__ == "__main__":
    main()
