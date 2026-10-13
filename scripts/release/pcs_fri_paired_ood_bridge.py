#!/usr/bin/env python3
"""Exact OOD-support sensitivity for the experimental paired PCS/FRI design.

The paper-protocol input is checked by pcs_fri_stwo_udr.  This tool changes
only the OOD denominator to the conditional image of the native CAS05 guard,
as a *hypothetical sensitivity calculation*.  The paper theorem has not been
proved for that distribution or for CAS05's transcript and oracle protocol.
No output field is a native security certificate.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_stwo_udr import F, PAPER_OOD_POINTS, Q, scenario_arithmetic

PAPER = "https://eprint.iacr.org/2026/532.pdf"
THEOREM_MAP = "https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md"
ACCEPTED_OOD_SEEDS = (Q * Q - 1) ** 2
REJECTED_Y_C1_ZERO_REGULAR = 2 * Q * Q - 3


def exact(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def candidate_cas05_geometry(paper_inputs: dict, height_count: int) -> dict:
    """Compare an explicitly hypothetical CAS05 short cascade to Protocol 3."""
    if type(height_count) is not int or not 2 <= height_count <= 8:
        raise ValueError("CAS05 height_count must be an integer in 2..8")
    d0 = paper_inputs["D0_with_composition_quotient"]
    blowup = paper_inputs["B"]
    k = d0.bit_length() - 1
    beta = blowup.bit_length() - 1
    if 1 << k != d0 or 1 << beta != blowup or k < height_count + beta:
        raise ValueError("CAS05 candidate has invalid domain or terminal geometry")
    full_folds = len(paper_inputs["fri_fold_domain_sizes"])
    if full_folds != k - beta:
        raise ValueError("paper full FRI fold roster changed")
    return {
        "assumed_largest_log_size": k,
        "assumed_height_count": height_count,
        "assumed_log_blowup": beta,
        "initial_domain_rows": d0,
        "source_rows_by_height": [d0 >> height for height in range(height_count)],
        "terminal_domain_rows": d0 >> height_count,
        "terminal_QM31_coefficient_words": 1 << (k - height_count - beta),
        "paper_full_single_fold_rounds": full_folds,
        "cas05_committed_fold_rounds": height_count,
        "paper_folds_without_a_matching_cas05_round": full_folds - height_count,
        "published_full_cascade_refinement_established": False,
        "qualification": ("CAS05 directly checks a high-degree terminal polynomial. "
                          "A shortened-cascade soundness theorem and BCS round count "
                          "must be derived; the full-cascade formula does not apply verbatim."),
    }


def sensitivity(scenario: dict, target_bits: int = 96,
                candidate_height_count: int | None = None) -> dict:
    """Inspect a valid idealized paper scenario, with all native joins open."""
    paper = scenario_arithmetic(scenario, target_bits)
    if F - 2 - REJECTED_Y_C1_ZERO_REGULAR != ACCEPTED_OOD_SEEDS:
        raise ValueError("OOD accepted-support identity changed")
    if not 0 < ACCEPTED_OOD_SEEDS < PAPER_OOD_POINTS < F:
        raise ValueError("OOD support inclusion arithmetic changed")
    inputs = paper["paper_inputs"]
    numerator = 1 + (inputs["B"] + 2) * inputs["N"]
    paper_ood = Fraction(numerator, PAPER_OOD_POINTS)
    if Fraction(paper["published_round_error_bounds"]["air_ood"]) != paper_ood:
        raise ValueError("paper OOD formula changed; review correction")
    candidate_ood = Fraction(numerator, ACCEPTED_OOD_SEEDS)
    factor = Fraction(PAPER_OOD_POINTS, ACCEPTED_OOD_SEEDS)
    errors = {name: Fraction(value) for name, value in
              paper["published_round_error_bounds"].items()}
    errors["air_ood"] = candidate_ood
    candidate_max = max(errors.values())
    t, rounds = inputs["T"], inputs["R"]
    collision = Fraction(paper["BCS_collision_term"])
    candidate_total = (t + rounds) * candidate_max + collision
    target = Fraction(1, 1 << target_bits)
    geometry = (candidate_cas05_geometry(inputs, candidate_height_count)
                if candidate_height_count is not None else None)
    return {
        "schema": "s31-paired-ood-theorem-sensitivity-v1",
        "status": "conditional_arithmetic_only_native_theorem_join_open",
        "published_sources": {"whitepaper": PAPER, "official_theorem_map": THEOREM_MAP},
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "target_bits": target_bits,
        "support": {
            "qm31_seed_count": F,
            "regular_seed_count": F - 2,
            "rejected_regular_y_c1_zero_count": REJECTED_Y_C1_ZERO_REGULAR,
            "accepted_seed_count_if_uniform_and_guarded": ACCEPTED_OOD_SEEDS,
            "paper_ood_point_count": PAPER_OOD_POINTS,
            "paper_minus_accepted_count": PAPER_OOD_POINTS - ACCEPTED_OOD_SEEDS,
            "conditional_uniform_accepted_fraction_of_all_seeds":
                exact(Fraction(ACCEPTED_OOD_SEEDS, F)),
            "paper_to_accepted_bad_event_mass_factor": exact(factor),
            "factor_less_than_one_plus_2pow_minus_60": factor < 1 + Fraction(1, 1 << 60),
            "lean_arithmetic_theorem":
                "S31.Gadgets.PcsFri.OodAcceptedSupport.conditioning_factor_lt_one_plus_2pow_neg60",
        },
        "paper_idealized_scenario": paper,
        "hypothetical_cas05_geometry": geometry,
        "candidate_same_bad_set_numerator_only": {
            "published_ood_upper_bound_expression": exact(paper_ood),
            "accepted_support_ood_expression": exact(candidate_ood),
            "published_full_BCS_expression": paper["BCS_total_formula"],
            "substituted_full_BCS_expression": exact(candidate_total),
            "substituted_absolute_expression_meets_target": candidate_total <= target,
            "substituted_work_factor_expression_meets_target": candidate_total <= t * target,
            "interpretation": ("Only a sensitivity calculation. Replacing a denominator "
                               "in a published proof is not itself a proof; the native "
                               "bad-set degree numerator and conditional protocol reduction "
                               "must be established independently."),
        },
        "unproved_native_joins": [
            "the actual CAS05 verifier and host prover are accepted by production dispatch",
            "every CAS05 source and line opening authenticates the exact paper projection trace",
            "the CAS05 original-plus-quotient ensemble meets the paper's degree-corrected relation",
            "the paper's OOD bad-set degree numerator applies to the guarded support",
            "the native Fiat-Shamir seed is ideal-uniform at each relevant adaptive transcript state",
            "abort on exceptional or y.c1-zero seed has the modeled schedule and cost",
            "the native masked raw-query law, duplicate queries, and line-pair checks refine the theorem query",
            "CAS05's short high-degree terminal refines a stated shortened-FRI theorem",
            "the BLAKE2s Merkle/transcript/PoW protocol has a quantified BCS reduction for T and R",
            "the reported paper scenario matches a source-pinned installed binary and key",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scenario", type=Path,
                        help="explicit hypothetical paper-protocol scenario JSON")
    parser.add_argument("--target-bits", type=int, default=96)
    parser.add_argument("--candidate-cas05-height-count", type=int,
                        help="hypothetical CAS05 height count (2..8); not native evidence")
    parser.add_argument("--require-proven", action="store_true",
                        help="fail closed until native theorem correspondence is complete")
    args = parser.parse_args(argv)
    try:
        result = sensitivity(json.loads(args.scenario.read_text()), args.target_bits,
                             args.candidate_cas05_height_count)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"paired OOD theorem bridge rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
