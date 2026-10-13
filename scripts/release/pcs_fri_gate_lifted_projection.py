#!/usr/bin/env python3
"""Describe every lifted PCS column index for a locally trusted gate package.

Package artifacts are not modified. This executes the package's native
`check-key` binary through the gate geometry diagnostic; package hashes do not
authenticate binary provenance. The global P03 oracle relation remains open.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_final_domain import ROOT, extract_gate
from scripts.s31_formal_lib.pcs_fri_projection import (
    PROJECTION_SOURCE_FILES, check_projection_sources, tree_query_position,
)

SOURCES = PROJECTION_SOURCE_FILES + (
    "scripts/s31_formal_lib/pcs_fri_projection.py",
    "scripts/release/pcs_fri_gate_lifted_projection.py",
)


def gate_tree_groups(roster: dict, geometry: dict) -> list[dict]:
    """Expand exact tree/column counts into compact consecutive groups."""
    height = geometry["gate_final_domain"]["fri_input_domain_log"]
    blowup = geometry["fri"]["log_blowup_factor"]
    components = roster.get("components")
    fixed = roster.get("preprocessed_columns")
    if not isinstance(components, list) or not isinstance(fixed, list):
        raise ValueError("gate roster lacks column lists")
    if len(components) != len(geometry["components"]) or len(fixed) != len(geometry["preprocessed_columns"]):
        raise ValueError("gate roster column lists differ from verified geometry")

    trees = [
        {"tree_index": 0, "name": "preprocessed", "groups": []},
        {"tree_index": 1, "name": "main_trace", "groups": []},
        {"tree_index": 2, "name": "interaction_trace", "groups": []},
        {"tree_index": 3, "name": "composition", "groups": []},
    ]

    def add(tree: dict, source: str, count: int, column_log: int) -> None:
        if type(count) is not int or not 0 < count <= 100000:
            raise ValueError("invalid gate column width")
        if type(column_log) is not int or not 0 < column_log <= height:
            raise ValueError("column exceeds lifted tree height")
        start = sum(group["count"] for group in tree["groups"])
        if start + count > 100000:
            raise ValueError("gate column count exceeds diagnostic limit")
        tree["groups"].append({"source": source, "column_start": start,
                               "count": count, "extended_column_log": column_log,
                               "query_index_formula":
                               f"2 * (q // 2**({height}-{column_log}+1)) + q % 2"})

    for parsed, source in zip(geometry["preprocessed_columns"], fixed, strict=True):
        if parsed["id"] != source.get("id") or parsed["log_size"] != source.get("log_size"):
            raise ValueError("preprocessed roster differs from verified geometry")
        add(trees[0], parsed["id"], 1, parsed["log_size"] + blowup)

    for parsed, source in zip(geometry["components"], components, strict=True):
        if parsed["name"] != source.get("name") or parsed["trace_log_size"] != source.get("trace_log_size"):
            raise ValueError("component roster differs from verified geometry")
        for tree, width_field in ((trees[1], "base_trace_columns"),
                                  (trees[2], "interaction_trace_columns")):
            add(tree, parsed["name"], source.get(width_field),
                parsed["trace_log_size"] + blowup)

    split = geometry["gate_final_domain"]["composition_split_depth"]
    if split != 1:
        raise ValueError("unreviewed composition split")
    # compositionColumnCount(split, QM31.SECURE_EXTENSION_DEGREE) = 2^1 * 4.
    add(trees[3], "split_composition_QM31", 8,
        geometry["gate_final_domain"]["committed_composition_column_log_size"] + blowup)
    for tree in trees:
        natural = max(group["extended_column_log"] for group in tree["groups"])
        tree["natural_column_height_log"] = natural
        tree["explicit_lifted_tree_height_log"] = height
        tree["column_count"] = sum(group["count"] for group in tree["groups"])
        column_logs = [group["extended_column_log"]
                       for group in tree["groups"] for _ in range(group["count"])]
        # Both prover and verifier sort by log size, breaking ties with the
        # original column index before absorbing the row into the leaf hash.
        tree["leaf_hash_column_order"] = sorted(
            range(len(column_logs)), key=lambda index: (column_logs[index], index))
        if natural > height:
            raise ValueError("natural tree exceeds explicit height")
    return trees


def check_group_projection(trees: list[dict], raw_positions: list[int]) -> None:
    """Check every group against the two-stage native map and direct Lean map."""
    for tree in trees:
        height = tree["explicit_lifted_tree_height_log"]
        natural = tree["natural_column_height_log"]
        for q in raw_positions:
            if type(q) is not int or not 0 <= q < 1 << height:
                raise ValueError("raw query outside lifted domain")
            tree_q = tree_query_position(q, height, height)
            natural_q = tree_query_position(tree_q, height, natural)
            for group in tree["groups"]:
                column_log = group["extended_column_log"]
                two_stage = tree_query_position(natural_q, natural, column_log)
                direct = tree_query_position(q, height, column_log)
                if two_stage != direct or direct >= 1 << column_log or direct % 2 != q % 2:
                    raise ValueError("lifted tree/column projection mismatch")


def extract_projection(package: Path, root: Path = ROOT) -> dict:
    geometry = extract_gate(package, root)
    if geometry["fri"]["fold_step"] != 1:
        raise ValueError("only the fold-step-1 gate profile is reviewed")
    check_projection_sources(root)
    roster = json.loads((package / "gate-component-roster.json").read_text())
    trees = gate_tree_groups(roster, geometry)
    height = geometry["gate_final_domain"]["fri_input_domain_log"]
    samples = sorted({0, 1, 7, (1 << height) - 2, (1 << height) - 1})
    check_group_projection(trees, samples)
    return {
        "schema": "s31-gate-lifted-pcs-projection-v1",
        "status": "conditional_source_bound_geometry",
        "p03_global_oracle_relation_proved": False,
        "proof_package_manifest_sha256": geometry["package_checks"]["package_manifest_sha256"],
        "verification_key_sha256": geometry["package_checks"]["verification_key_sha256"],
        "engine_gitlink": geometry["source_binding"]["engine_gitlink"],
        "source_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                          for name in SOURCES},
        "lifted_height_log": height,
        "raw_query_domain_rows": 1 << height,
        "sampled_raw_positions": samples,
        "trees": trees,
        "remaining_premises": [
            "installed verifier binary corresponds to the pinned source",
            "Zig success extracts each modeled tree/column query value and path",
            "fixed committed oracles have the modeled projected rows",
            "Merkle collision bound and cross-domain IOP/proximity theorem",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--require-p03", action="store_true",
                        help="exit 2 while the global P03 oracle relation is open")
    args = parser.parse_args(argv)
    try:
        report = extract_projection(args.package.resolve())
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"gate lifted PCS projection rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_p03 else 0


if __name__ == "__main__":
    raise SystemExit(main())
