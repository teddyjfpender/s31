#!/usr/bin/env python3
"""Classify accepted sparse H3 claims into conditional Protocol-3/4 batches.

This is a source-bound occupancy map, not a native-to-paper refinement. In
particular, Protocol 4 states one common OOD point; its Section 4.5 remarks
on a conjugate two-point zeroifier, while the accepted proof has two distinct
OOD points, each with a conjugate quotient.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from pcs_fri_sparse_p05_accepted_geometry import ordered_claim_slices
from pcs_fri_sparse_p05_h3_roster import EVIDENCE, HEIGHTS, canonical_json, derive as derive_roster


REPO = Path(__file__).resolve().parents[2]
OUTPUT = REPO / "design/s31/security/evidence/sparse-gate-p05-paper-ensemble-2026-10-14.json"
SOURCE_PATHS = (
    "src/frontends/s31/runtime/native_verifier.zig",
    "deps/stwo-zig/src/prover/pcs/sampled_values.zig",
    "deps/stwo-zig/src/prover/pcs/sampled_coefficient_plans.zig",
    "deps/stwo-zig/src/core/pcs/quotients/samples.zig",
    "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig",
)


def point(claim: dict[str, object]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return tuple(claim["point_x_limbs"]), tuple(claim["point_y_limbs"])


def original(root: int, column: int, claim_index: int) -> str:
    return f"f/{root}/{column}/{claim_index}"


def quotient(root: int, column: int, claim_index: int) -> str:
    return f"q/{root}/{column}/{claim_index}"


def ensemble(words: dict[int, list[str]]) -> dict[str, object]:
    domains = [{"native_extended_log_size": height, "words": words[height],
                "conditional_M_i": len(words[height])} for height in HEIGHTS]
    return {"mapping_status": "conditional_occupancy_not_native_to_paper_refinement",
            "domains": domains,
            "conditional_common_padded_M": max(len(words[height]) for height in HEIGHTS)}


def derive(evidence: dict[str, object]) -> dict[str, object]:
    # This first validates accepted key/proof, the canonical 73-claim digest,
    # contiguous claim ownership, source order and all three native heights.
    roster = derive_roster(evidence)
    shape = evidence["accepted_capture"]
    base = (tuple(shape["oods_point_x_limbs"]), tuple(shape["oods_point_y_limbs"]))
    shifted = None
    base_words = {height: [] for height in HEIGHTS}
    shifted_words = {height: [] for height in HEIGHTS}
    joint_repeated_words = {height: [] for height in HEIGHTS}
    joint_dedup_words = {height: [] for height in HEIGHTS}
    base_claims: list[int] = []
    shifted_claims: list[int] = []

    for column, owned in ordered_claim_slices(shape):
        root, index, height = (column["root_index"], column["column_index"],
                               column["extended_log_size"])
        if len(owned) not in (1, 2):
            raise ValueError("accepted column has unsupported OOD arity")
        if point(owned[-1]) != base:
            raise ValueError("last OOD claim of each source column must be at base Q")
        if len(owned) == 2:
            candidate = point(owned[0])
            if candidate == base or (shifted is not None and candidate != shifted):
                raise ValueError("accepted shifted OOD point is not unique")
            shifted = candidate
        base_index = column["first_claim_index"] + len(owned) - 1
        base_claims.append(base_index)
        base_words[height].extend((original(root, index, base_index),
                                   quotient(root, index, base_index)))
        joint_dedup_words[height].append(original(root, index, base_index))
        for offset, claim in enumerate(owned):
            claim_index = column["first_claim_index"] + offset
            if point(claim) != (base if offset == len(owned) - 1 else shifted):
                raise ValueError("accepted OOD point assignment changed")
            joint_repeated_words[height].extend((original(root, index, claim_index),
                                                 quotient(root, index, claim_index)))
            joint_dedup_words[height].append(quotient(root, index, claim_index))
            if offset == 0 and len(owned) == 2:
                shifted_claims.append(claim_index)
                shifted_words[height].extend((original(root, index, claim_index),
                                              quotient(root, index, claim_index)))

    if shifted is None or len(base_claims) != 61 or len(shifted_claims) != 12:
        raise ValueError("accepted two-point claim partition changed")
    if sorted(base_claims + shifted_claims) != list(range(73)):
        raise ValueError("single-point subsets omit or duplicate an OOD claim")
    proposed = {
        "base_single_Q": ensemble(base_words),
        "shifted_single_Q": ensemble(shifted_words),
        "joint_multi_Q_repeated_original": ensemble(joint_repeated_words),
        "joint_multi_Q_deduplicated_original": ensemble(joint_dedup_words),
    }
    expected = {
        "base_single_Q": [28, 56, 38],
        "shifted_single_Q": [8, 8, 8],
        "joint_multi_Q_repeated_original": [36, 64, 46],
        "joint_multi_Q_deduplicated_original": [32, 60, 42],
    }
    for name, sizes in expected.items():
        if [d["conditional_M_i"] for d in proposed[name]["domains"]] != sizes:
            raise ValueError(f"accepted {name} width changed")
    if [len(h["legacy_periodicity_source_refs"]) for h in roster["heights"]] != [4, 4, 4]:
        raise ValueError("accepted periodicity relation count changed")
    return {
        "schema": "s31-p05-sparse-paper-ensemble-conditional-v1",
        "status": "accepted_source_bound_occupancy_only_no_paper_refinement",
        "accepted_key_sha256": roster["accepted_key_sha256"],
        "accepted_proof_sha256": roster["accepted_proof_sha256"],
        "accepted_ood_claim_map_sha256": roster["accepted_ood_claim_map_sha256"],
        "reviewed_native_source_sha256": {
            path: hashlib.sha256((REPO / path).read_bytes()).hexdigest()
            for path in SOURCE_PATHS
        },
        "paper_definition": {
            "protocol_3": "Section 4.2 Eq. (66): per-domain M_i functions; pad to M=max_i M_i",
            "protocol_4": "Section 4.4 pp. 34-36 Eq. (77): at one common Q, pair every f with (f-v)/v_Q; multiple-Q generalization left to reader",
            "conjugate_note": "Section 4.5 p. 37: Q and Frobenius conjugate quotient; details omitted, soundness said to carry over; Q excluded from C(CM31)",
            "paper_url": "https://eprint.iacr.org/2026/532.pdf",
        },
        "word_ref_encoding": "f/root/column/paired_claim_index or q/root/column/claim_index; q is a candidate native own quotient, not Eq. (77) admission",
        "accepted_point_partition": {
            "base_point_x_limbs": list(base[0]),
            "base_point_y_limbs": list(base[1]),
            "shifted_point_x_limbs": list(shifted[0]),
            "shifted_point_y_limbs": list(shifted[1]),
            "base_claim_indices": base_claims,
            "shifted_claim_indices": shifted_claims,
        },
        "native_source_point_projection": {
            "captured_lifted_log_size": shape["trace_lifting_log_size"],
            "rule": "for each captured top OOD point P, source-height point P_h = repeatedDouble(P, 17-h)",
            "by_native_extended_log_size": [
                {"height": height, "doublings": shape["trace_lifting_log_size"] - height}
                for height in HEIGHTS
            ],
            "paper_common_Q_equivalence_proven": False,
        },
        "conditional_ensembles": proposed,
        "conditional_paper_D0_size_N_times_B_squared": evidence[
            "candidate_paper_parameters"]["D0_conditionally_N_times_B_squared"],
        "native_largest_extended_source_domain_size": 1 << HEIGHTS[0],
        "additional_native_periodicity_relation_words_by_height": [4, 4, 4],
        "legacy_native_quotient_contributions": {
            "explicit_ood": 73,
            "periodicity": 12,
            "total_accumulated": 85,
            "independently_degree_tested": False,
            "lifted_log17_periodicity_duplicates_sample1_at_height17": 4,
            "height_local_periodicity_duplicates_sample1_at_all_heights": 12,
            "coefficient_compression_theorem_proven": False,
        },
        "conditional_joint_width_if_periodicity_independent": {
            "repeated_original": [40, 68, 50],
            "deduplicated_original": [36, 64, 46],
        },
        "native_to_paper_batch_width_M": None,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "unproved_mapping": [
            "Protocol 4's one common Q does not jointly cover the two accepted OOD points",
            "native conjugate two-point quotient needs the omitted Section 4.5 construction and degree/domain refinement, even though the paper says soundness carries over",
            "native LDE heights 17/11/5 and paper's D0=N*B^2 need a degree/domain map",
            "four source commitment epochs and candidate quotient oracles need whole-oracle custody",
            "two separate single-Q proofs need a joint soundness/BCS composition and shared-source binding",
            "periodicity relation words may require additional independent function tracks",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=EVIDENCE)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = canonical_json(derive(json.loads(args.evidence.read_text())))
    if args.write:
        OUTPUT.write_text(rendered)
        print(f"wrote {OUTPUT.relative_to(REPO)}")
    elif OUTPUT.read_text() != rendered:
        raise SystemExit("stale sparse H3 paper ensemble")
    else:
        print("checked accepted sparse H3 conditional paper ensemble")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
