#!/usr/bin/env python3
"""Exact OOD-support sensitivity for the experimental paired PCS/FRI design.

The paper-protocol input is checked by pcs_fri_stwo_udr. This tool changes
only the *single-point Protocol-4* OOD denominator to the conditional image
of the native CAS05 guard, as a hypothetical sensitivity calculation. CAS05
uses a conjugate two-point quotient whose Section-4.5 OOD universe and
bad-set theorem differ; substituting this denominator does not model that
theorem. Nor has the paper theorem been proved for CAS05's transcript and
oracle protocol. No output field is a native security certificate.
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
    """Map the short terminal to Protocol 3's *variable-r* idealized shape."""
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
    short_folds = paper_inputs["fri_fold_domain_sizes"][:height_count]
    if short_folds != [d0 >> (i + 1) for i in range(height_count)]:
        raise ValueError("paper short FRI fold roster changed")
    paper_n = k - beta
    paper_r = height_count - 1
    if not 0 <= paper_r < paper_n:
        raise ValueError("paper Protocol 3 requires 0 <= r < n")
    terminal_words = 1 << (paper_n - 1 - paper_r)
    terminal_rows = d0 >> height_count
    if terminal_words * blowup != terminal_rows:
        raise ValueError("short terminal degree/rate geometry changed")
    query_count = paper_inputs["queries"]
    # Source-level caps inspected at native draft commit 9cd3f2989. The
    # sparse verifier's profile was widened independently of the host
    # prover, which still constructs a dense XDM03 source commitment.
    sparse_scalar_caps = (k <= 22 and k >= height_count + 2 and
                          query_count <= (1 << 14))
    host_scalar_caps = (k <= 16 and k >= height_count + 2 and
                        query_count * (1 << height_count) <= (1 << 16))
    return {
        "assumed_largest_log_size": k,
        "assumed_height_count": height_count,
        "assumed_log_blowup": beta,
        "initial_domain_rows": d0,
        "source_rows_by_height": [d0 >> height for height in range(height_count)],
        "terminal_domain_rows": terminal_rows,
        "terminal_QM31_coefficient_words": terminal_words,
        "published_protocol3_n": paper_n,
        "published_protocol3_r": paper_r,
        "published_protocol3_variable_r_hypothesis_satisfied": True,
        "published_terminal_space": f"F[x]_{{<2^({paper_n}-1-{paper_r})}}",
        "published_short_fold_domain_sizes": short_folds,
        "published_short_fold_error_bounds_unique_decoding": [
            exact(Fraction(3 * size, F)) for size in short_folds],
        "minimum_idealized_BCS_round_count": 3 + 1 + height_count + 1,
        "native_draft_source_caps_at_commit_9cd3f2989": {
            "sparse_verifier_visible_log_height_query_caps_pass": sparse_scalar_caps,
            "dense_host_prover_visible_log_height_query_caps_pass": host_scalar_caps,
            "sparse_verifier_max_log_size": 22,
            "dense_host_prover_max_log_size": 16,
            "both_require_nonzero_columns_at_each_height": True,
            "full_profile_or_proof_admissible": False,
        },
        "paper_full_single_fold_rounds": full_folds,
        "cas05_committed_fold_rounds": height_count,
        "full_roster_folds_elided_by_early_terminal": full_folds - height_count,
        "native_protocol3_refinement_established": False,
        "qualification": ("S-two Protocol 3 and Theorem 4 already permit variable r "
                          "and a directly checked higher-degree terminal polynomial. "
                          "The idealized short roster uses only the listed folds; "
                          "native CAS05 still needs a verifier-to-Protocol-3 refinement, "
                          "a scalable host prover, OOD and BCS reductions, and a "
                          "source-derived round count."),
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
    short_formula = None
    if geometry is not None:
        short_errors = {name: value for name, value in errors.items()
                        if not name.startswith("fri_fold_") or
                        int(name.removeprefix("fri_fold_")) < candidate_height_count}
        # Keep the scenario's explicit R. It may overcount a short idealized
        # transcript, but native R has not been measured or reduced to BCS.
        if rounds < geometry["minimum_idealized_BCS_round_count"]:
            raise ValueError("scenario R undercounts the short idealized protocol")
        short_max = max(short_errors.values())
        short_total = (t + rounds) * short_max + collision
        short_formula = {
            "status": "idealized_variable_r_paper_formula_only",
            "fold_error_roster": {name: exact(value) for name, value in short_errors.items()
                                  if name.startswith("fri_fold_")},
            "explicit_scenario_R_used": rounds,
            "minimum_idealized_R": geometry["minimum_idealized_BCS_round_count"],
            "largest_round_bound_with_hypothetical_guarded_OOD": exact(short_max),
            "BCS_expression_with_hypothetical_guarded_OOD": exact(short_total),
            "work_factor_expression_meets_target": short_total <= t * target,
            "absolute_expression_meets_target": short_total <= target,
            "native_security_bits": None,
        }
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
        "hypothetical_short_protocol3_formula": short_formula,
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
            "native CAS05's high-degree terminal, line domains, and all folds refine variable-r Protocol 3",
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
