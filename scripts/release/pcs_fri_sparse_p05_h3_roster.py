#!/usr/bin/env python3
"""Derive a candidate H3 paired roster from one accepted sparse Gate proof.

The input is the output of pcs_fri_sparse_p05_accepted_geometry.py. This tool
maps source columns and actual OOD claims to proposed independent tracks; it
does not test their degree or identify the paper's padded batch width M.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from pcs_fri_sparse_p05_accepted_geometry import ordered_claim_slices


REPO = Path(__file__).resolve().parents[2]
EVIDENCE = REPO / "design/s31/security/evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json"
OUTPUT = REPO / "design/s31/security/evidence/sparse-gate-p05-h3-candidate-roster-2026-10-14.json"
LEAN = REPO / "formal/s31/S31/Gadgets/PcsFri/SparseP05AcceptedH3Data.lean"
KEY_SHA256 = "7d4cdaab4e446aaa2c357e28f077e469412f45a17c660e8d4434cca216dccfc7"
PROOF_SHA256 = "04eaca23d8a6c7fc977b24a3d925aaabcbb727fa4fa30f30c81864e24a158e39"
ROOT_ORDER = ("fixed", "main", "interaction", "composition")
HEIGHTS = (17, 11, 5)
ROW_ADAPTER = REPO / "formal/s31/tests/lib/p05_own_quotient_rows.zig"


def canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def derive(evidence: dict[str, object]) -> dict[str, object]:
    if (evidence.get("schema") != "s31-p05-sparse-gate-accepted-geometry-v1" or
            evidence.get("status") != "accepted_native_proof_experimental_geometry_only" or
            evidence.get("native_to_paper_batch_width_M") is not None or
            evidence.get("native_proven_security_bits") is not None or
            evidence.get("proven_release_admissible") is not False):
        raise ValueError("expected an accepted, still-open sparse P05 report")
    checks = evidence["package_checks"]
    if (checks["key_sha256"] != KEY_SHA256 or
            checks["proof_sha256"] != PROOF_SHA256 or
            checks["native_proof"] != "accepted_before_geometry_inspection"):
        raise ValueError("accepted key/proof identity changed")
    shape = evidence["accepted_capture"]
    claims = shape["claims"]
    claim_digest = hashlib.sha256(json.dumps(
        claims, sort_keys=True, separators=(",", ":")
    ).encode()).hexdigest()
    if claim_digest != evidence["accepted_ood_claim_map_sha256"]:
        raise ValueError("accepted claim map digest mismatch")
    if (shape["root_columns"] != [12, 17, 24, 8] or
            shape["root_ood_claims"] != [12, 17, 36, 8] or
            len(shape["columns"]) != 61 or len(claims) != 73 or
            shape["composition_log_split"] != 1):
        raise ValueError("unexpected accepted sparse Gate geometry")

    buckets = {height: {
        "extended_log_size": height,
        "committed_input_log_size": height - 1,
        "original_source_refs": [],
        "own_quotient_claim_refs": [],
        "legacy_periodicity_source_refs": [],
    } for height in HEIGHTS}
    next_column = [0] * 4
    for column, owned in ordered_claim_slices(shape):
        root = column["root_index"]
        index = column["column_index"]
        height = column["extended_log_size"]
        if (type(root) is not int or not 0 <= root < 4 or
                type(index) is not int or index != next_column[root] or
                height not in buckets or len(owned) not in (1, 2)):
            raise ValueError("source column order or H3 height changed")
        next_column[root] += 1
        bucket = buckets[height]
        bucket["original_source_refs"].append([root, index])
        for sample, claim in enumerate(owned):
            claim_index = column["first_claim_index"] + sample
            if (claim["root_index"] != root or claim["column_index"] != index or
                    claim["sample_index"] != sample or
                    claim["extended_log_size"] != height):
                raise ValueError("claim source reference changed")
            bucket["own_quotient_claim_refs"].append([claim_index, root, index, sample])
        if len(owned) == 2:
            # Native row-evaluation also inserts one periodicity relation word
            # for a two-sample column. Its exact shifted point belongs to a
            # later oracle/theorem map, not to the 73 explicit OOD claims.
            bucket["legacy_periodicity_source_refs"].append([root, index])
    if next_column != shape["root_columns"]:
        raise ValueError("missing source column")

    heights = [buckets[height] for height in HEIGHTS]
    for bucket, accepted in zip(heights, shape["heights"], strict=True):
        originals = len(bucket["original_source_refs"])
        quotients = len(bucket["own_quotient_claim_refs"])
        periodic = len(bucket["legacy_periodicity_source_refs"])
        if (accepted["extended_log_size"] != bucket["extended_log_size"] or
                accepted["source_columns"] != originals or
                accepted["ood_claims"] != quotients or
                accepted["required_original_tracks_if_paired"] != originals or
                accepted["required_own_quotient_tracks_if_paired"] != quotients):
            raise ValueError("accepted height counts disagree with candidate map")
        bucket["candidate_direct_track_width"] = originals + quotients
        bucket["candidate_width_if_periodicity_is_separate"] = originals + quotients + periodic
    all_sources = [(root, index) for bucket in heights
                   for root, index in bucket["original_source_refs"]]
    all_claims = [ref[0] for bucket in heights
                  for ref in bucket["own_quotient_claim_refs"]]
    if (len(all_sources) != len(set(all_sources)) or
            set(all_sources) != {(root, index) for root, count in enumerate(next_column)
                                 for index in range(count)} or
            sorted(all_claims) != list(range(len(claims)))):
        raise ValueError("candidate tracks omit or repeat an accepted source/claim")
    direct_sizes = [bucket["candidate_direct_track_width"] for bucket in heights]
    with_periodicity = [bucket["candidate_width_if_periodicity_is_separate"]
                        for bucket in heights]
    if direct_sizes != [32, 60, 42] or with_periodicity != [36, 64, 46]:
        raise ValueError("candidate batch sizes changed")
    return {
        "schema": "s31-p05-sparse-h3-candidate-roster-v1",
        "status": "accepted_proof_derived_candidate_not_degree_tested",
        "accepted_key_sha256": checks["key_sha256"],
        "accepted_proof_sha256": checks["proof_sha256"],
        "accepted_ood_claim_map_sha256": claim_digest,
        "legacy_row_adapter_source_sha256": hashlib.sha256(ROW_ADAPTER.read_bytes()).hexdigest(),
        "root_order": list(ROOT_ORDER),
        "heights": heights,
        "total_original_source_columns": len(all_sources),
        "total_direct_own_quotient_claims": len(all_claims),
        "total_legacy_periodicity_relation_words": sum(
            len(bucket["legacy_periodicity_source_refs"]) for bucket in heights),
        "conditional_paper_mapping": {
            "premise": "one paper-domain function per listed candidate track, no compression or extra functions",
            "direct_batch_sizes_if_premise": direct_sizes,
            "direct_common_padded_M_if_premise": max(direct_sizes),
            "batch_sizes_if_periodicity_is_separate": with_periodicity,
            "common_padded_M_if_periodicity_is_separate": max(with_periodicity),
            "native_to_paper_batch_width_M": None,
            "certified_batch_grinding_credit": 0,
            "full_paper_error_bound": None,
        },
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
    }


def lean_data(evidence: dict[str, object]) -> str:
    shape = evidence["accepted_capture"]
    rows = [
        f"  ⟨{c['root_index']}, {c['column_index']}, {c['extended_log_size']}, "
        f"{c['first_claim_index']}, {c['ood_claims']}⟩"
        for c in shape["columns"]
    ]
    return "\n".join([
        "import Mathlib.Data.List.Basic",
        "",
        "/-! Generated by scripts/release/pcs_fri_sparse_p05_h3_roster.py.",
        "Source-bound finite data only; this file does not prove native admission. -/",
        "namespace S31.PcsFri.SparseP05AcceptedH3Data",
        "",
        "structure Column where",
        "  root : Nat",
        "  index : Nat",
        "  extendedLog : Nat",
        "  firstClaim : Nat",
        "  claimCount : Nat",
        "  deriving DecidableEq, Repr",
        "",
        f'def keySha256 : String := "{evidence["package_checks"]["key_sha256"]}"',
        f'def proofSha256 : String := "{evidence["package_checks"]["proof_sha256"]}"',
        f'def claimMapSha256 : String := "{evidence["accepted_ood_claim_map_sha256"]}"',
        "",
        "def columns : List Column := [",
        ",\n".join(rows),
        "]",
        "",
        "end S31.PcsFri.SparseP05AcceptedH3Data",
        "",
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=EVIDENCE)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    evidence = json.loads(args.evidence.read_text())
    output = canonical_json(derive(evidence))
    lean = lean_data(evidence)
    if args.write:
        OUTPUT.write_text(output)
        LEAN.write_text(lean)
        print(f"wrote {OUTPUT.relative_to(REPO)} and {LEAN.relative_to(REPO)}")
    elif OUTPUT.read_text() != output or LEAN.read_text() != lean:
        raise SystemExit("stale sparse H3 candidate roster or Lean data")
    else:
        print("checked accepted sparse H3 candidate roster and Lean data")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
