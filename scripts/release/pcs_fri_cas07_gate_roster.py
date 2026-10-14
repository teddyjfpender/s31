#!/usr/bin/env python3
"""Audit one sealed Gate package against the experimental CAS07 source shape.

This is a metadata comparison, not a proof conversion or PCS admission. The
package checker runs its locally trusted native check-key binary. The CAS07
checkout must be the exact reviewed draft commit and source bytes below.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_final_domain import extract_gate

DRAFT_COMMIT = "859409aa1e00a71a21a0f240b7f9f5c5a64fd3f8"
CAS07_SOURCE_SHA256 = {
    "src/core/pcs/transposed_merkle_sparse_heights_experimental.zig": "268e0b0e55e82e97671fab3d0583d6a266f749a3502ee22549f8ce5e0d0a9627",
    "src/core/pcs/paired_sparse_cascade_heights_experimental.zig": "636918588bd0d0779732e5d2f8a8f1fefe5d3ead0fd6e702be7fe88a5e08fead",
    "src/core/pcs/transposed_paired_sparse_heights_experimental.zig": "f3ab1fdf5b14f26525724269645e9c41059c4e2f2f755b7751bf022cd04d371f",
    "src/core/pcs/paired_sparse_cascade_heights_wire.zig": "da0d5cefd9fc088da4537622e04e36d8d5f143f835357dd805cb9694f27c8595",
    "src/prover/pcs/transposed_sparse_heights_experimental.zig": "fa6fdeed91cee02a048d85dcb332eb11bb3a0b1246d45dd4d537bf6ba3b93e63",
    "src/prover/pcs/paired_sparse_cascade_heights_experimental.zig": "02627a407d52d73fc28484d009720a23af1db5a9e0b1bbcfd063520ffcd6dcd3",
    "src/core/pcs/transposed_merkle_cascade.zig": "7bc0793234e902ae37080e2c8b90d4df87120fd3a87c441d669c928fcb85bb92",
    "src/core/pcs/transposed_merkle.zig": "5424b43ed4088dc5583437182984a741348bdf6dd58b6906f94130a062651063",
}


def check_candidate_source(engine: Path) -> dict[str, object]:
    commit = subprocess.check_output(
        ["git", "-C", str(engine), "rev-parse", "HEAD"], text=True
    ).strip()
    if commit != DRAFT_COMMIT:
        raise ValueError("CAS07 candidate commit differs from reviewed draft")
    dirty = subprocess.check_output(
        ["git", "-C", str(engine), "status", "--porcelain", "--untracked-files=no"],
        text=True,
    )
    if dirty:
        raise ValueError("CAS07 candidate tracked source is dirty")
    observed = {name: hashlib.sha256((engine / name).read_bytes()).hexdigest()
                for name in CAS07_SOURCE_SHA256}
    if observed != CAS07_SOURCE_SHA256:
        changed = sorted(name for name in observed if observed[name] != CAS07_SOURCE_SHA256[name])
        raise ValueError("CAS07 candidate source differs from reviewed draft: " + ", ".join(changed))
    return {"draft_commit": commit, "reviewed_source_sha256": observed}


def _uint(value: object, label: str, maximum: int) -> int:
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError(f"invalid {label}")
    return value


def derive_candidate_roster(report: dict, *, beta: int = 2, queries: int = 232) -> dict:
    """Derive ordered source slots from a checked Gate geometry report.

    The order is a candidate XDM05 layout, not the three existing Gate trees.
    No source values, OOD claims, composition columns, or proof are converted.
    """
    if (report.get("lowering"), report.get("key_schema"), report.get("profile")) != (
            "gate", "s31-verification-key-gate-roster-v1", "circuit-v1"):
        raise ValueError("only the sealed Gate key is reviewed")
    if report.get("package_checks", {}).get("native_check_key") != "accepted":
        raise ValueError("Gate native check-key did not accept")
    geometry = report.get("gate_trace_and_fri_schedule")
    if not isinstance(geometry, dict) or geometry.get("status") != "conditional_source_bound_geometry":
        raise ValueError("missing source-bound Gate schedule")
    k = _uint(report.get("max_trace_log_size"), "largest log size", 22)
    beta = _uint(beta, "candidate blowup log", 22)
    queries = _uint(queries, "illustrative query count", 1 << 14)
    if (k, beta, queries) != (20, 2, 232):
        raise ValueError("only the reviewed Gate-shaped CAS07 pilot is inventoried")
    fixed, tables = geometry.get("preprocessed_columns"), geometry.get("tables")
    trees = geometry.get("pcs_commitment_trees")
    if not isinstance(fixed, list) or not isinstance(tables, list) or not isinstance(trees, list):
        raise ValueError("missing Gate source trees")
    if len(fixed) != 45 or len(tables) != 11 or len(trees) != 4:
        raise ValueError("Gate source roster count changed")
    widths = tuple(_uint(tree.get("column_count"), "tree width", 100_000)
                   for tree in trees if isinstance(tree, dict))
    if widths != (45, 114, 152, 8):
        raise ValueError("Gate commitment widths differ from reviewed profile")
    if tuple(tree.get("kind") for tree in trees) != (
            "preprocessed", "main", "interaction", "composition"):
        raise ValueError("Gate commitment order changed")

    by_log: dict[int, list[dict]] = {}
    def add(log: int, kind: str, name: str, width: int, tree: int) -> None:
        if log > k or width < 1:
            raise ValueError("invalid Gate source height or width")
        by_log.setdefault(log, []).append({"tree_index": tree, "kind": kind,
                                            "name": name, "width": width})

    for index, column in enumerate(fixed):
        if not isinstance(column, dict) or _uint(column.get("commitment_index"), "fixed order", 100_000) != index:
            raise ValueError("fixed column order changed")
        if not isinstance(column.get("id"), str) or not column["id"]:
            raise ValueError("invalid fixed column ID")
        add(_uint(column.get("log_size"), "fixed log size", k),
            "preprocessed", column["id"], 1, 0)
    for kind, key, tree in (("main", "main_trace_columns", 1),
                            ("interaction", "interaction_trace_columns", 2)):
        for index, table in enumerate(tables):
            if not isinstance(table, dict) or _uint(table.get("proof_index"), "table order", 100_000) != index:
                raise ValueError("table proof order changed")
            if not isinstance(table.get("name"), str) or not table["name"]:
                raise ValueError("invalid table name")
            add(_uint(table.get("trace_log_size"), "table log size", k), kind,
                table["name"], _uint(table.get(key), "table width", 100_000), tree)
    if (sum(part["width"] for parts in by_log.values() for part in parts) != 311 or
            sum(part["width"] for parts in by_log.values() for part in parts if part["tree_index"] == 0) != 45):
        raise ValueError("flattened Gate source width changed")
    occupied = sorted(by_log, reverse=True)
    if occupied != [20, 18, 16, 14, 9, 8, 4]:
        raise ValueError("Gate occupied heights changed")
    H = k - min(occupied) + 1
    counts = [sum(part["width"] for part in by_log.get(k - height, [])) for height in range(H)]
    if counts != [51, 0, 8, 0, 15, 0, 8, 0, 0, 0, 0, 28, 8, 0, 0, 0, 193]:
        raise ValueError("Gate CAS07 column profile changed")
    # Reviewed XDM05 v5 and CAS07 v7 caps. Check with integer arithmetic;
    # these visible caps do not supply a theorem or a whole-prover memory cap.
    source_words = sum(count << (k - height) for height, count in enumerate(counts))
    tree_bytes = ((1 << (k + 1)) - 1) * 32
    source_tree_bytes = source_words * 4 + tree_bytes
    fixed_wire_bytes = queries * (4 + sum(8 * count for count in counts))
    if (not 1 <= H <= 20 or k < H + 2 or any(count > 256 for count in counts) or
            fixed_wire_bytes > 64 * 1024 * 1024 - 128 or
            source_tree_bytes > 384 * 1024 * 1024 or k < H + beta):
        raise ValueError("reviewed CAS07 visible profile cap failed")
    slots = [{"height": i, "source_log_size": k - i, "column_count": count,
              "segments": by_log.get(k - i, [])} for i, count in enumerate(counts)]
    binding = {
        "cas07_draft_commit": DRAFT_COMMIT,
        "gate_engine_gitlink": report["source_binding"]["engine_gitlink"],
        "gate_geometry_source_sha256": report["gate_final_domain"]["source_sha256"],
        "gate_package_manifest_sha256": report["package_checks"]["package_manifest_sha256"],
        "gate_verification_key_sha256": report["package_checks"]["verification_key_sha256"],
        "gate_air_bundle_sha256": report["gate_final_domain"]["air_bundle_sha256"],
        "candidate_profile": {"k": k, "H": H, "beta": beta, "queries": queries,
                              "columns_by_height": counts},
        "ordered_source_slots": slots,
    }
    digest = hashlib.sha256(b"S31-CAS07-GATE-ROSTER-AUDIT-V1\x00" +
                            json.dumps(binding, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    # Conditional Protocol-4 arithmetic only. No native-to-paper identification
    # of M, N, B, or the batch epoch follows from tree width.
    q4 = ((1 << 31) - 1) ** 4
    target = Fraction(1, 1 << 96)
    hypothetical = {}
    for width in (152, 311, 319):
        term = Fraction((width - 1) * (1 << k) * (1 << (2 * beta)), q4)
        hypothetical[str(width)] = {
            "exact_term": f"{term.numerator}/{term.denominator}",
            "term_exceeds_2_pow_minus_96": term > target,
        }
    return {
        "schema": "s31-cas07-gate-roster-audit-v1",
        "status": "candidate_metadata_only",
        "native_proven_security_bits": None,
        "production_equivalent": False,
        "selected_target": {"metric": "paper_work_factor_epsilon_over_T",
                            "bits": 96, "T_hash_queries": 1 << 64},
        "candidate_roster_sha256": digest,
        "binding": binding,
        "source_words": source_words,
        "source_plus_tree_estimated_bytes": source_tree_bytes,
        "source_query_payload_bytes_before_hash_witness": fixed_wire_bytes,
        "candidate_terminal_coefficients": 1 << (k - H - beta),
        "production_commitment_widths": list(widths),
        "production_commitment_epochs": [
            "preprocessed root before public/circuit values",
            "main root before lookup challenge",
            "interaction root after lookup challenge and claimed sums",
            "composition root after AIR random coefficients",
        ],
        "unmapped_composition_columns": widths[3],
        "hypothetical_paper_batching_term_if_M_equals_width": hypothetical,
        "published_batch_width_M_for_actual_proof": None,
        "row_custody": None,
        "required_before_admission": [
            "trusted installed key reconstructs the exact roster and ordered row values",
            "multi-epoch commitment protocol and theorem, or proved transcript-preserving adapter",
            "composition columns and AIR/OOD claims bound at their actual transcript epoch",
            "XDM05 empty-height hash-upper, H=1, and source-row authentication refinement",
            "native two-point degree/correlated-agreement and conservative PCS/FRI bound",
            "derive published batch width M from the actual original/quotient/composition ensemble",
        ],
    }


def require_production_equivalence(report: dict) -> None:
    if report.get("production_equivalent") is not True or report.get("required_before_admission"):
        raise ValueError("CAS07 Gate metadata does not establish production equivalence")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed Gate package")
    parser.add_argument("candidate_engine", type=Path, help="exact CAS07 draft checkout")
    parser.add_argument("--require-production-equivalent", action="store_true")
    args = parser.parse_args(argv)
    try:
        candidate = check_candidate_source(args.candidate_engine.resolve())
        report = derive_candidate_roster(extract_gate(args.package.resolve()))
        report["candidate_source_binding"] = candidate
        if args.require_production_equivalent:
            require_production_equivalence(report)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"CAS07 Gate roster audit rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
