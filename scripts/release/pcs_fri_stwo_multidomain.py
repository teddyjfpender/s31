#!/usr/bin/env python3
"""Exact, fail-closed S-two 2026 multi-domain FRI theorem arithmetic.

This measures *published proof envelopes*, never the probability of a native
attack. The paper-to-native protocol identification is currently unproved.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from fractions import Fraction
from math import isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_error_ledger import ledger_from_gate
from scripts.release.pcs_fri_gate_final_domain import extract_gate

PAPER = "https://eprint.iacr.org/2026/532.pdf"
MAP = "https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md"
Q = 2**31 - 1
F_ORDER = Q**4
DOMAIN_CAP = 2**30


def ratio(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def sqrt_upper(value: Fraction, scale_bits: int = 32) -> Fraction:
    """A dyadic upper bound, calculated with integers only (no float rounding)."""
    if value <= 0 or not 1 <= scale_bits <= 128:
        raise ValueError("invalid rational square-root input")
    scale = 1 << scale_bits
    square = value.numerator * scale * scale
    root = isqrt(square // value.denominator)
    if root * root * value.denominator < square:
        root += 1
    return Fraction(root, scale)


def sqrt_lower(value: Fraction, scale_bits: int = 32) -> Fraction:
    """A dyadic lower bound, calculated with integers only."""
    if value <= 0 or not 1 <= scale_bits <= 128:
        raise ValueError("invalid rational square-root input")
    scale = 1 << scale_bits
    root = isqrt(value.numerator * scale * scale // value.denominator)
    return Fraction(root, scale)


def johnson_minimum_m(blowup: int) -> int:
    """Least paper GS multiplicity for theta >= delta/2, certified by intervals."""
    if blowup < 2 or blowup & (blowup - 1):
        raise ValueError("invalid Johnson blowup")
    rho = Fraction(1, blowup)
    alpha_max = (1 + rho) / 2
    for bits in (32, 64, 128):
        low, high = sqrt_lower(rho, bits), sqrt_upper(rho, bits)
        if not 0 < low <= high < alpha_max:
            continue
        def ceil_ratio(root: Fraction) -> int:
            value = root / (2 * (alpha_max - root))
            return -(-value.numerator // value.denominator)
        lower_m, upper_m = max(3, ceil_ratio(low)), max(3, ceil_ratio(high))
        if lower_m == upper_m:
            return lower_m
    raise ValueError("GS multiplicity interval straddles an integer boundary")


def remark15_first_fold_floor(n: int, blowup: int) -> Fraction:
    """Floor on Appendix A Remark 15's tighter first-fold upper bound.

    At theta >= delta/2, m(theta) is at least johnson_minimum_m(B).  Its
    GS list size uses the *circle* code rate rho=1/B, as in Remark 15.
    """
    if type(n) is not int or n < 1 or blowup < 2 or blowup & (blowup - 1):
        raise ValueError("invalid candidate theorem geometry")
    rho = Fraction(1, blowup)
    ell_floor = Fraction(johnson_minimum_m(blowup) + 1, 2) / sqrt_upper(rho)
    s0 = n * blowup // 2
    return ell_floor * (2 * ell_floor**4 / (3 * rho) + 1) * s0 / F_ORDER


def first_fold_johnson_floor(n: int, blowup: int) -> Fraction:
    """Lower floor on Theorem 4's *upper-bound expression*, with m >= 3.

    The line-code rate is rho + 1/|S_0|, |S_0| = N*B/2.  The paper's
    Guruswami-Sudan list bound is (m+1)/(2 sqrt(rate)); m >= 3 gives
    ell >= 2/sqrt(rate).  We deliberately omit the positive +3*ell term.
    """
    if (type(n) is not int or type(blowup) is not int or n < 1 or
            blowup < 2 or blowup & (blowup - 1) or n * blowup % 2):
        raise ValueError("invalid candidate theorem geometry")
    s0 = n * blowup // 2
    rate_line = Fraction(1, blowup) + Fraction(1, s0)
    ell_floor = Fraction(2, 1) / sqrt_upper(rate_line)
    return 2 * ell_floor**5 * s0 / (rate_line * F_ORDER)


def minimum_udr_queries(blowup: int, target_bits: int) -> int:
    """Necessary count at the *excluded* unique-decoding boundary theta=delta/2.

    Strict theta<delta/2 makes every actual query error larger than this
    boundary value, so equality at the target does not suffice.
    """
    if blowup < 2 or blowup & (blowup - 1) or target_bits < 1:
        raise ValueError("invalid unique-decoding parameters")
    alpha_limit = (Fraction(1) + Fraction(1, blowup)) / 2
    target = Fraction(1, 1 << target_bits)
    draws = 1
    while alpha_limit**draws >= target:
        draws += 1
    return draws


def multidomain_from_gate(report: dict, target_bits: int = 96,
                          adversary_hash_queries: int = 1 << 32) -> dict:
    """Project theorem arithmetic onto the reviewed Gate geometry, conditionally."""
    if type(target_bits) is not int or not 1 <= target_bits <= 256:
        raise ValueError("target_bits must be an integer in 1..256")
    if (type(adversary_hash_queries) is not int or
            not 1 <= adversary_hash_queries <= 1 << 64):
        raise ValueError("adversary_hash_queries must be an integer in 1..2^64")
    source = ledger_from_gate(report)
    observed = source["source_bound_observations"]
    n = observed["candidate_max_trace_rows"]
    native_b = 1 << observed["log_blowup_factor"]
    draws = observed["raw_query_draws"]
    target = Fraction(1, 1 << target_bits)
    candidates = []
    b = 2
    while n * b * b <= DOMAIN_CAP:
        s0 = n * b // 2
        line_rate = Fraction(1, b) + Fraction(1, s0)
        johnson_floor = first_fold_johnson_floor(n, b)
        improved_floor = remark15_first_fold_floor(n, b)
        udr_fold = Fraction(3 * s0, F_ORDER)
        # BCS has (T+R)*max_i epsilon_i.  R>=1, while all other terms are
        # omitted.  Therefore this is a *necessary* test for use of the
        # paper's quoted UDR fold bound, never a full security estimate.
        udr_bcs_floor = (adversary_hash_queries + 1) * udr_fold
        johnson_query_floor = Fraction(1, b) ** (draws // 2) if draws % 2 == 0 else None
        candidates.append({
            "hypothetical_blowup": b,
            "native_configured": b == native_b,
            "native_supported_or_admissible": None,
            "candidate_D0_rows": n * b,
            "candidate_S0_rows": s0,
            "candidate_first_line_code_rate": ratio(line_rate),
            "johnson_first_fold_published_envelope_strictly_above": ratio(johnson_floor),
            "johnson_first_fold_envelope_exceeds_target": johnson_floor > target,
            "johnson_minimum_GS_multiplicity_at_theta_delta_over_2": johnson_minimum_m(b),
            "johnson_remark15_tighter_first_fold_envelope_strictly_above":
                ratio(improved_floor),
            "johnson_remark15_tighter_first_fold_envelope_exceeds_target":
                improved_floor > target,
            "johnson_query_lower_floor_for_70_draws": (
                ratio(johnson_query_floor) if johnson_query_floor is not None else None),
            "johnson_query_lower_floor_exceeds_target": (
                johnson_query_floor >= target if johnson_query_floor is not None else None),
            "udr_first_fold_published_bound": ratio(udr_fold),
            "udr_first_fold_bound_meets_target_alone": udr_fold <= target,
            "udr_minimum_queries_at_excluded_boundary": minimum_udr_queries(b, target_bits),
            "udr_bcs_first_fold_contribution_with_R_at_least_1": ratio(udr_bcs_floor),
            "udr_bcs_first_fold_contribution_exceeds_target": udr_bcs_floor > target,
            "udr_necessary_max_T_if_R_at_least_1_other_terms_ignored":
                max(0, int(target // udr_fold) - 1),
        })
        b *= 2

    # For N>=2^20, B>=2, S0=N*B/2>=2^20 and
    # rho_line=1/B+1/S0 <= 1/2+1/2^20 <9/16. Therefore ell>=8/3.
    # The Lean theorem checks this floor at F=(2^31-1)^4.
    universal_floor = 2 * Fraction(8, 3)**5 * (1 << 20) / (
        Fraction(9, 16) * F_ORDER)
    if n != 1 << 20 or universal_floor <= Fraction(1, 1 << 96):
        raise ValueError("reviewed universal Johnson obstruction changed")

    return {
        "schema": "s31-stwo-2026-multidomain-gate-ledger-v1",
        "status": "published_envelope_obstruction_and_native_refinement_open",
        "target_bits": target_bits,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "sources": {"paper": PAPER, "official_theorem_map": MAP,
                    "paper_theorem": "Theorem 4, Remark 9, Theorem 5, Theorem 6; Appendix A Theorem 11"},
        "conditional_native_observations": {
            "gate_trace_rows": n,
            "fri_input_rows": observed["fri_input_domain_rows"],
            "blowup": native_b,
            "raw_query_draws": draws,
            "fold_step": observed["fold_step"],
            "configured_pow_bits_without_automatic_credit": observed["pow_bits"],
            "verification_key_sha256": observed["verification_key_sha256"],
        },
        "hypothetical_adversary_hash_queries_T": adversary_hash_queries,
        "field_order_if_native_QM31_matches_paper_F": F_ORDER,
        "theorem4_general_johnson_first_fold_envelope_lower_floor_for_N_at_least_2pow20_B_at_least_2":
            ratio(universal_floor),
        "theorem4_general_johnson_floor_exceeds_96_bit_target":
            universal_floor > Fraction(1, 1 << 96),
        "candidate_theorem_arithmetic": candidates,
        "theorem_hypotheses_not_dischargeable_from_geometry": [
            "native D0, S0, per-domain polynomial rates and exact FRI round schedule equal Protocol 3",
            "cross-domain lifted agreement, source/interaction AIR and OOD ensemble realize Protocols 1 and 4",
            "non-quotient degree correction or a reviewed proof for native quotient-only relation",
            "the native query sampler, including non-squaring-consistent circle points, has the chosen regime's proof",
            "actual batch width M, all AIR round counts, list sizes and small-table conditions are extracted",
            "exact BLAKE2s/Merkle/PoW transform admits a quantified ROM/BCS reduction and collision budget",
        ],
        "unbound_published_terms": {
            "logup": None, "composition": None, "OOD": None,
            "cross_domain_batching": None, "all_FRI_folds": None,
            "native_query_distribution": None, "BCS_round_count_R": None,
            "native_Merkle_and_hash_binding": None, "native_refinement": None,
        },
        "scope": ("A lower floor on a published *upper-bound expression* only. "
                  "It is not an attack lower bound; all changed-B rows are hypothetical. "
                  "The UDR candidate is a separate theorem regime and its other errors remain unbound."),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed Gate package")
    parser.add_argument("--target-bits", type=int, default=96)
    parser.add_argument("--adversary-hash-queries", type=int, default=1 << 32)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = multidomain_from_gate(extract_gate(args.package.resolve()),
                                       args.target_bits, args.adversary_hash_queries)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"S-two multi-domain theorem ledger rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
