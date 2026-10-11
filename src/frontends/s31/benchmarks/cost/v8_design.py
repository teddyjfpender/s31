#!/usr/bin/env python3
"""Static, pre-freeze V8 workload inventory. This module cannot run native work.

The committed design fixes fresh split choices before observation. A later
runner must seal generated digests, source/tool/engine/host pins, and anchors.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
S31_DIR = BENCH.parent
ROOT = S31_DIR.parents[2]
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(S31_DIR / "python"))

import s31
import v7_protocol as v7
from benchmark_arithmetic_rss_v2 import assignment as recurrence_assignment
from benchmark_arithmetic_rss_v2 import program as recurrence_program
from benchmark_whole_prover_cost_v3 import signed_assignment
from benchmark_whole_prover_cost_v6 import remainder_assignment
from benchmark_whole_prover_multiscale import hash_assignment, hash_program

DESIGN = ROOT / "design/s31/measurements/language/whole-prover-cost-v8-prospective.json"
V7R1_PROTOCOL = v7.PROTOCOL
V7R1_AUDIT = ROOT / "design/s31/measurements/language/whole-prover-cost-v7r1-audit.json"
FAMILIES = ("arithmetic", "chip", "hash", "fixed_width")


def read_design() -> dict:
    design = json.loads(DESIGN.read_bytes())
    validate_design(design)
    return design


def validate_design(design: dict) -> None:
    if (design.get("schema") != "s31-whole-prover-cost-v8-prospective-design" or
        design.get("status") != "designed-not-frozen-no-native-observations" or
        design.get("automatic_lowering_selection_enabled") is not False):
        raise ValueError("V8 prospective design must remain pre-freeze")
    if set(design.get("prefreeze_pins", {})) != {
        "source_base_commit", "compiler_sha256", "engine_gitlink_commit",
        "measurement_tool_sha256", "host_identity", "generated_inventory_sha256",
        "admitted_general_mixed_manifest_sha256",
    } or any(value is not None for value in design["prefreeze_pins"].values()):
        raise ValueError("V8 prefreeze design must not masquerade as a pinned protocol")
    if (design.get("historical_v7r1_protocol_sha256") != s31.file_hash(V7R1_PROTOCOL) or
        design.get("historical_v7r1_audit_sha256") != s31.file_hash(V7R1_AUDIT)):
        raise ValueError("V7r1 disclosure hash differs from committed evidence")
    if design.get("samples_per_program") != 100 or design.get("predictive_accuracy_gate") != v7.GATES:
        raise ValueError("V8 must preserve the predeclared V7 accuracy thresholds")
    uncertainty = design.get("rss_uncertainty", {})
    if (uncertainty.get("fixed_absolute_floor_bytes") != 2 * 1024**2 or
        uncertainty.get("selected_before_v8_native_observation") is not True):
        raise ValueError("V8 RSS calibration design changed")
    splits = design.get("splits", {})
    if set(splits) != {"train", "validation"}:
        raise ValueError("V8 needs separate train and validation splits")
    for name, split in splits.items():
        for key in ("arithmetic_rounds", "chip_rounds", "hash_depths", "signed_widths"):
            values = split.get(key, [])
            if (len(values) < 5 or len(values) != len(set(values)) or
                any(type(value) is not int or value <= 0 for value in values)):
                raise ValueError(f"invalid {name}/{key} menu")
        if any(value < 16 or value > 32768 or value & (value - 1)
               for value in split["chip_rounds"]):
            raise ValueError(f"unsupported {name} direct-chip geometry")
        if (split["signed_widths"] != [8, 16, 32, 64, 128] or
            split["fixed_width_result"] != "div_rem_below_128" or
            split["signed_128_result"] != ("quotient" if name == "train" else "remainder")):
            raise ValueError("V8 fixed-width ABI changed")
        if type(split.get("assignment_index_base")) is not int or split["assignment_index_base"] <= 3_000_000:
            raise ValueError("V8 assignment seed must be fresh")
    for key in ("arithmetic_rounds", "chip_rounds", "hash_depths"):
        if set(splits["train"][key]) & set(splits["validation"][key]):
            raise ValueError(f"V8 train/validation {key} shapes overlap")
    if abs(splits["train"]["assignment_index_base"] -
           splits["validation"]["assignment_index_base"]) < 400_000:
        raise ValueError("V8 assignment index ranges overlap")
    paired = design.get("paired_mixed_vs_generic", {})
    if (paired.get("status") != "blocked-until-general-mixed-profile-admitted-and-packaged" or
        sorted(paired.get("train_call_counts", []) + paired.get("validation_call_counts", [])) != list(range(1, 9)) or
        paired.get("assignments_per_pair") != 100 or
        paired.get("automatic_lowering_selection_enabled") is not False):
        raise ValueError("V8 mixed pairing is not yet admissible")


def fixed_source(width: int, kind: str, split: str) -> str:
    count = (width + 15) // 16
    expression = ("std::array::concat(std::int::limbs(quotient), std::int::limbs(remainder))"
                  if kind == "div_rem" else f"std::int::limbs({kind})")
    output_count = 2 * count if kind == "div_rem" else count
    return (f"use std@1;\n\n"
            f"circuit i{width}_{kind}_cost_v8_{split}(private numerator: i{width}, "
            f"private divisor: i{width}) -> public [u16; {output_count}] {{\n"
            f"    let (quotient, remainder) = std::int::div_rem(numerator, divisor);\n"
            f"    {expression}\n"
            f"}}\n")


def workloads(split: str, output: Path, design: dict) -> list[dict]:
    """Generate deterministic sources and witnesses; never build packages."""
    validate_design(design)
    if split not in ("train", "validation"):
        raise ValueError("unknown V8 split")
    spec = design["splits"][split]
    seed = spec["assignment_index_base"]
    sources = output / "generated-sources"
    sources.mkdir(parents=True, exist_ok=True)
    entries = []
    for family, key, offset in (("arithmetic", "arithmetic_rounds", 0),
                                ("chip", "chip_rounds", 100_000)):
        for rounds in spec[key]:
            name = f"{family}_{rounds}"
            body = [{"op": "square"}, {"op": "add_const",
                                        "constant": spec[f"{family}_constant"]}]
            source = sources / f"{name}.s31.json"
            s31.write_json(source, recurrence_program(f"v8_{split}_{name}", rounds, body))
            entries.append({"name": name, "family": family, "source": source,
                            "lowering": "direct-chip" if family == "chip" else "direct-gate",
                            "assignments": [recurrence_assignment(rounds, body, seed + offset + i)
                                            for i in range(design["samples_per_program"])]})
    for depth in spec["hash_depths"]:
        name = f"hash_{depth}"
        source = sources / f"{name}.s31.json"
        relation = hash_program(depth)
        relation["name"] = f"v8_{split}_blake_chain_{depth}"
        s31.write_json(source, relation)
        entries.append({"name": name, "family": "hash", "source": source,
                        "lowering": "gate",
                        "assignments": [hash_assignment(depth, seed + 200_000 + i)
                                        for i in range(design["samples_per_program"])]})
    for width in spec["signed_widths"]:
        kind = spec["signed_128_result"] if width == 128 else "div_rem"
        name = f"signed_{kind}_{width}"
        source = sources / f"{name}.s31"
        source.write_text(fixed_source(width, kind, split))
        from package.context import lower_text
        relation, _, _ = lower_text(source)
        if len(relation["public_outputs"]) != 1:
            raise ValueError(f"{name}: expected one public output")
        output_name = relation["public_outputs"][0]
        entries.append({"name": name, "family": "fixed_width", "source": source,
                        "lowering": "direct-gate",
                        "assignments": [(remainder_assignment(width, seed + 300_000 + i,
                                                              output_name) if kind == "remainder" else
                                         signed_assignment(width, seed + 300_000 + i,
                                                           kind == "quotient", output_name))
                                        for i in range(design["samples_per_program"])]})
    return entries


def historical_digests() -> tuple[set[str], set[str]]:
    sources, assignments = v7.historical_digests()
    for path in (v7.SUPERSEDED_PROTOCOL, V7R1_PROTOCOL):
        protocol = json.loads(path.read_bytes())
        for split in ("train", "validation"):
            for item in protocol["inventory"][split].values():
                sources.add(item["source_sha256"])
                assignments.update(item["assignment_sha256"])
    return sources, assignments


def inventory(output: Path, design: dict) -> dict:
    """Check source/assignment byte disjointness against V6, transfer, V7, V7r1."""
    old_sources, old_assignments = historical_digests()
    seen_sources, seen_assignments = set(), set()
    result = {}
    for split in ("train", "validation"):
        result[split] = {}
        for item in workloads(split, output / split, design):
            name = item["name"]
            source_sha = s31.file_hash(item["source"])
            if source_sha in old_sources | seen_sources:
                raise ValueError(f"{split}/{name}: historical or intra-V8 source overlap")
            seen_sources.add(source_sha)
            assignments = []
            for index, assignment in enumerate(item["assignments"]):
                path = output / split / name / "assignments" / f"{index:02d}.json"
                path.parent.mkdir(parents=True, exist_ok=True)
                s31.write_json(path, assignment)
                digest = s31.assignment_digest(path)
                if digest in old_assignments | seen_assignments:
                    raise ValueError(f"{split}/{name}: historical or intra-V8 assignment overlap")
                assignments.append(digest)
                seen_assignments.add(digest)
            result[split][name] = {"family": item["family"],
                                   "lowering": item["lowering"],
                                   "source_sha256": source_sha,
                                   "assignment_sha256": assignments}
    return result


def inventory_sha256(found: dict) -> str:
    encoded = json.dumps(found, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-inventory", type=Path,
                        help="write only generated source and assignment files here")
    args = parser.parse_args()
    design = read_design()
    if args.check_inventory is None:
        print("V8 prospective design valid; native measurement remains disabled")
    else:
        output = args.check_inventory.resolve()
        found = inventory(output, design)
        counts = {split: len(rows) for split, rows in found.items()}
        print(f"V8 prospective inventory disjoint: {counts}; "
              f"preview SHA-256 {inventory_sha256(found)}; no native measurement")


if __name__ == "__main__":
    main()
