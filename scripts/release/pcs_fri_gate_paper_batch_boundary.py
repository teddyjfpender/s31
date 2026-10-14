#!/usr/bin/env python3
"""Source-bound Gate roster and conditional paper batch-width arithmetic.

The installed legacy Gate PCS uses one quotient-only FRI oracle. Consequently
its paper Protocol-4 ensemble width M is *not defined by this diagnostic*.
The counterfactual calculations below are certificate-feasibility checks, not
attack probabilities or a native soundness bound.
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

ROOT = Path(__file__).resolve().parents[2]
ENGINE_COMMIT = "59e1f115250b8af01712b9bf3d71616e53094964"
ENGINE_SHA256 = {
    "deps/stwo-zig/src/core/fri.zig": "5f84501d1ffbaf5d33d6f7063bea7e6fd88a4cb65140ff360b75cb11f812121f",
    "deps/stwo-zig/src/core/verifier.zig": "85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381",
    "deps/stwo-zig/src/core/pcs/verifier.zig": "e119335172e17db5fd1345f476c7f6ad7fdf67e394a5b18d5c2085e892ffe3d5",
    "deps/stwo-zig/src/core/pcs/quotients.zig": "f7fa34f327650f6c20ddac73fe7dba2477ecc22e0c2ea2359aaa9021eff97aa6",
    "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig": "5280b74c1762860fad733066a40d96dada813908532e3b8854e0a3f02f182181",
    "deps/stwo-zig/src/core/pcs/quotients/row_evaluation.zig": "30e9e8768b083ca3d218b9d4903d7e3805b4219971e7d92847303d9de5778442",
    "deps/stwo-zig/src/core/pcs/quotients/samples.zig": "18848c2e180236b0d6807a4d2863f127a8830366ac1df038f5042359e9401e2e",
    "deps/stwo-zig/src/prover/fri.zig": "22acc5c7af16cc06fa646e5eedfe9a9a5bee95a273b53dbac83a599576f3e609",
    "deps/stwo-zig/src/prover/pcs/scheme.zig": "88ab21970d32dda383a191ce5f12c329ce127f2829712a99068dd369d147e93f",
    "deps/stwo-zig/src/prover/pcs/quotients/lazy_provider.zig": "7d8c02ad443bba0941f10a8d22ecb1ef81e77b9837c3e1f561445fe31d0e728e",
}
Q = (1 << 31) - 1
F = Q**4
T = 1 << 64
TARGET = Fraction(1, 1 << 96)


def checked_engine_sources(root: Path = ROOT) -> dict[str, str]:
    observed = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                for name in ENGINE_SHA256}
    if observed != ENGINE_SHA256:
        changed = sorted(name for name in ENGINE_SHA256 if observed[name] != ENGINE_SHA256[name])
        raise ValueError("reviewed PCS/FRI source changed: " + ", ".join(changed))
    return observed


def integer(value: object, label: str, *, maximum: int = 1 << 30) -> int:
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError(f"invalid {label}")
    return value


def exact(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def batching_term(m: int, n: int, b: int) -> Fraction:
    if m < 1 or n < 1 or b < 1:
        raise ValueError("positive M, N, B required")
    return Fraction((m - 1) * n * b * b, F)


def derive_boundary(report: dict, source_hashes: dict[str, str]) -> dict:
    """Classify observed native columns; leave the published ensemble unmapped."""
    if (report.get("lowering"), report.get("key_schema"), report.get("profile")) != (
            "gate", "s31-verification-key-gate-roster-v1", "circuit-v1"):
        raise ValueError("only legacy ordinary Gate is reviewed")
    if report.get("package_checks", {}).get("native_check_key") != "accepted":
        raise ValueError("native check-key did not accept")
    if report.get("source_binding", {}).get("engine_gitlink") != ENGINE_COMMIT:
        raise ValueError("engine gitlink changed")
    if source_hashes != ENGINE_SHA256:
        raise ValueError("reviewed PCS/FRI source hashes changed")
    geometry = report.get("gate_trace_and_fri_schedule")
    final = report.get("gate_final_domain")
    fri = report.get("fri")
    if not all(isinstance(value, dict) for value in (geometry, final, fri)):
        raise ValueError("missing checked Gate geometry")
    if (geometry.get("status"), final.get("status")) != (
            "conditional_source_bound_geometry", "conditional_source_bound_geometry"):
        raise ValueError("Gate geometry was not source bound")
    if (integer(fri.get("log_blowup_factor"), "blowup log") != 1 or
            integer(fri.get("fold_step"), "fold step") != 1 or
            integer(fri.get("raw_queries"), "raw query count") != 70):
        raise ValueError("unreviewed legacy Gate FRI schedule")
    max_log = integer(report.get("max_trace_log_size"), "maximum trace log", maximum=28)
    native_domain_log = integer(final.get("fri_input_domain_log"), "native FRI domain log", maximum=30)
    composition_log = integer(final.get("committed_composition_column_log_size"),
                              "composition column log", maximum=max_log)
    if native_domain_log != max_log + 1:
        raise ValueError("native lifted FRI domain changed")
    fixed, tables, trees = (geometry.get("preprocessed_columns"), geometry.get("tables"),
                             geometry.get("pcs_commitment_trees"))
    if not isinstance(fixed, list) or not isinstance(tables, list) or not isinstance(trees, list):
        raise ValueError("missing checked four-tree roster")
    if (len(trees) != 4 or any(not isinstance(tree, dict) for tree in trees) or
            tuple(tree.get("kind") for tree in trees) != (
            "preprocessed", "main", "interaction", "composition")):
        raise ValueError("production commitment order changed")
    widths = tuple(integer(tree.get("column_count"), "tree width") for tree in trees)
    if widths != (45, 114, 152, 8):
        raise ValueError("reviewed production tree widths changed")
    by_log: dict[int, list[int]] = {}

    def add(log: object, tree: int, width: int) -> None:
        log = integer(log, "source column log", maximum=max_log)
        by_log.setdefault(log, [0, 0, 0, 0])[tree] += width

    if len(fixed) != widths[0] or len(tables) != 11:
        raise ValueError("reviewed fixed or component count changed")
    for index, column in enumerate(fixed):
        if not isinstance(column, dict):
            raise ValueError("invalid fixed column")
        if integer(column.get("commitment_index"), "fixed order") != index:
            raise ValueError("fixed commitment order changed")
        add(column.get("log_size"), 0, 1)
    for index, table in enumerate(tables):
        if not isinstance(table, dict):
            raise ValueError("invalid component table")
        if integer(table.get("proof_index"), "table proof order") != index:
            raise ValueError("table proof order changed")
        add(table.get("trace_log_size"), 1,
            integer(table.get("main_trace_columns"), "main width"))
        add(table.get("trace_log_size"), 2,
            integer(table.get("interaction_trace_columns"), "interaction width"))
    add(composition_log, 3, widths[3])
    if tuple(sum(counts[i] for counts in by_log.values()) for i in range(4)) != widths:
        raise ValueError("source-height grouping disagrees with tree widths")

    n, b = 1 << max_log, 1 << fri["log_blowup_factor"]
    paper_d0 = n * b * b
    if paper_d0 > 1 << 30:
        raise ValueError("conditional paper D0 exceeds circle-domain cap")
    # Necessary numerical limit for this *one* quoted batching term. R>=1
    # makes (T+R)/T > 1; all omitted theorem errors are nonnegative.
    limit = TARGET * F * T / ((T + 1) * paper_d0)
    max_m = limit.numerator // limit.denominator + 1
    if batching_term(max_m, n, b) * Fraction(T + 1, T) > TARGET:
        raise AssertionError("batching cap arithmetic failed")
    if batching_term(max_m + 1, n, b) * Fraction(T + 1, T) <= TARGET:
        raise AssertionError("batching cap was not maximal")
    candidates = {}
    for label, m in (("next_integer_over_cap", max_m + 1),
                     ("largest_single_native_height", max(sum(v) for v in by_log.values())),
                     ("all_native_source_columns", sum(widths)),
                     ("one_original_plus_one_quotient_per_largest_height",
                      2 * max(sum(v) for v in by_log.values()))):
        term = batching_term(m, n, b)
        candidates[label] = {
            "assumed_M": m, "paper_batch_term_exact": exact(term),
            "single_term_BCS_work_factor_with_R_at_least_1_exceeds_target":
                term * Fraction(T + 1, T) > TARGET,
        }
    binding = {
        "engine_gitlink": ENGINE_COMMIT,
        "engine_source_sha256": source_hashes,
        "package_manifest_sha256": report["package_checks"]["package_manifest_sha256"],
        "verification_key_sha256": report["package_checks"]["verification_key_sha256"],
        "air_bundle_sha256": final["air_bundle_sha256"],
        "gate_source_sha256": final["source_sha256"],
        "native_roster_by_log": [{"source_log_size": log, "tree_columns": counts,
                                   "total": sum(counts)}
                                  for log, counts in sorted(by_log.items(), reverse=True)],
    }
    digest = hashlib.sha256(b"S31-GATE-PAPER-BATCH-BOUNDARY-V1\x00" + json.dumps(
        binding, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {
        "schema": "s31-gate-paper-batch-boundary-v1",
        "status": "native_roster_observed_paper_ensemble_unmapped",
        "native_proven_security_bits": None,
        "published_batch_width_M_for_actual_proof": None,
        "published_N_B_for_actual_proof": None,
        "paper_protocol_refinement_proved": False,
        "release_gate_admissible": False,
        "selected_target": {"metric": "paper_work_factor_epsilon_over_T",
                            "bits": 96, "T_hash_queries": T},
        "binding_sha256": digest,
        "binding": binding,
        "native_commitment_widths": list(widths),
        "native_source_columns_total": sum(widths),
        "native_first_fri_domain_size": 1 << native_domain_log,
        "conditional_paper_geometry_if_N_is_max_gate_trace_and_B_is_native_blowup": {
            "N": n, "B": b, "D0_NB_squared": paper_d0,
            "field_size": F,
            "batching_term": "(M-1)*N*B^2/field_size",
            "largest_M_whose_batching_term_with_R_at_least_1_fits_target": max_m,
            "next_M_exceeds_target": max_m + 1,
            "counterfactual_M_values": candidates,
        },
        "unmapped_reasons": [
            "native FRI receives one accumulated quotient oracle, not the paper's original-plus-own-quotient ensemble",
            "native four roots have distinct challenge-dependent commitment epochs",
            "native first FRI domain has size N*B, while the paper degree-corrected ensemble starts at N*B^2",
            "tree width and source-height occupancy alone do not define the theorem's ensemble width M",
            "two-point native quotient and native query/BCS laws lack an implementation-matched theorem",
        ],
    }


def require_paper_mapping(report: dict) -> None:
    if (report.get("published_batch_width_M_for_actual_proof") is None or
            report.get("paper_protocol_refinement_proved") is not True or
            report.get("release_gate_admissible") is not True):
        raise ValueError("native Gate has no proved paper ensemble mapping")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed legacy Gate package")
    parser.add_argument("--require-paper-mapping", action="store_true")
    args = parser.parse_args(argv)
    try:
        hashes = checked_engine_sources()
        report = derive_boundary(extract_gate(args.package.resolve()), hashes)
        if args.require_paper_mapping:
            require_paper_mapping(report)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"Gate paper batch boundary rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
