#!/usr/bin/env python3
"""Fail-closed query feasibility for a sealed gate in the *proven* Johnson regime.

This checks necessary arithmetic for published theorem envelopes, not actual
native security. The locally trusted package verifier runs ``check-key``; its
manifest hashes do not authenticate that executable or a successful proof.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_error_ledger import ledger_from_gate
from scripts.release.pcs_fri_gate_final_domain import extract_gate
from scripts.release.pcs_fri_proven_preflight import (
    Candidate, minimum_ideal_m31_masked_queries, minimum_queries,
    query_meets, remark26_leading_interval,
)

CIRCLE = "https://eprint.iacr.org/2024/278.pdf"
STWO = "https://eprint.iacr.org/2026/532.pdf"


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def minimum_johnson_draws(blowup_log: int, target_bits: int, hypothetical_credit: int = 0) -> int:
    """Necessary count from strict 1-theta > sqrt(2^-blowup_log).

    A nonnegative hypothetical credit is allowed only to ask what *could* fit
    after an independently proved query-phase grinding reduction. It is never
    treated as a native security contribution here.
    """
    if blowup_log < 1 or target_bits < 1 or not 0 <= hypothetical_credit <= target_bits:
        raise ValueError("invalid Johnson feasibility parameters")
    return (2 * (target_bits - hypothetical_credit)) // blowup_log + 1


def candidate_query_bits(candidate: Candidate) -> int:
    """Largest integer b for which only the candidate Circle query term <=2^-b."""
    bits = 0
    while query_meets(candidate, bits + 1, candidate.raw_queries):
        bits += 1
    return bits


def feasibility_from_gate(report: dict, target_bits: int = 96) -> dict:
    """Evaluate arithmetic only after the reviewed gate ledger rejects wrong geometry."""
    if type(target_bits) is not int or not 1 <= target_bits <= 512:
        raise ValueError("target_bits must be an integer in 1..512")
    ledger = ledger_from_gate(report)
    observed = ledger["source_bound_observations"]
    n = observed["candidate_max_trace_rows"]
    d = observed["fri_input_domain_rows"]
    blowup_log = observed["log_blowup_factor"]
    blowup = 1 << blowup_log
    draws = observed["raw_query_draws"]
    pow_bits = observed["pow_bits"]
    if d != n * blowup:
        raise ValueError("unreviewed gate feasibility geometry or target")

    def circle(m: int, b: int = blowup, bits: int = target_bits) -> Candidate:
        candidate = Candidate(n, b, draws, m, 1, target_bits=bits)
        candidate.validate()
        return candidate

    m_min, m_max = 3, n // 2
    low_m = circle(m_min)
    high_m = circle(m_max)
    leading_lower, leading_upper = remark26_leading_interval(low_m)
    target = Fraction(1, 1 << target_bits)
    potential_credit = min(pow_bits, target_bits)
    query_ruled_out = draws < minimum_johnson_draws(blowup_log, target_bits, potential_credit)
    design_space = []
    candidate_b = 2
    while n * candidate_b * candidate_b <= 1 << 30:
        beta = candidate_b.bit_length() - 1
        design_space.append({
            "hypothetical_blowup": candidate_b,
            "native_supported_or_admissible": None,
            "minimum_draws_at_johnson_limit_without_grinding":
                minimum_johnson_draws(beta, target_bits),
            "minimum_draws_at_johnson_limit_with_full_hypothetical_query_credit":
                minimum_johnson_draws(beta, target_bits, potential_credit),
            "circle_m3_minimum_ungrinded_draws_if_N_D_map":
                minimum_queries(circle(m_min, candidate_b)),
        })
        candidate_b *= 2

    return {
        "schema": "s31-pcs-fri-gate-conservative-feasibility-v1",
        "status": ("published_proven_johnson_envelope_fails_target" if query_ruled_out
                   else "query_necessity_not_excluded_but_native_mapping_open"),
        "target_bits": target_bits,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "source_bound_gate": {
            "conditional_trace_rows": n,
            "conditional_fri_input_rows": d,
            "blowup_factor": blowup,
            "raw_query_draws": draws,
            "configured_pow_bits": pow_bits,
            "engine_gitlink": observed["engine_gitlink"],
            "verification_key_sha256": observed["verification_key_sha256"],
            "air_bundle_sha256": observed["air_bundle_sha256"],
        },
        "stwo_proven_johnson_query_necessity": {
            "theorem": STWO,
            "premise": "if this native oracle maps to rate rho=1/B, theta < 1-sqrt(rho)",
            "strict_inequality": "(1-theta)^s > B^(-s/2)",
            "without_grinding_query_exponent_strictly_below":
                fraction_text(Fraction(blowup_log * draws, 2)),
            "even_if_full_pow_were_query_credit_exponent_strictly_below":
                fraction_text(Fraction(blowup_log * draws, 2) + potential_credit),
            "minimum_draws_at_johnson_limit_without_grinding":
                minimum_johnson_draws(blowup_log, target_bits),
            "minimum_draws_at_johnson_limit_with_full_hypothetical_query_credit":
                minimum_johnson_draws(blowup_log, target_bits, potential_credit),
            "current_draws_cannot_meet_target_even_with_full_hypothetical_query_credit":
                query_ruled_out,
            "pow_credit_status": "hypothetical favorable upper limit only; native grinding reduction unproved",
        },
        "circle_single_domain_candidate": {
            "theorem": CIRCLE + "#appendix-B",
            "premise": "only if Circle N and standard-position D identify this gate's native oracle",
            "candidate_rate": fraction_text(Fraction(n + 1, d)),
            "m3_minimum_ungrinded_draws": minimum_queries(low_m),
            "m3_minimum_draws_with_full_hypothetical_query_credit":
                minimum_queries(circle(m_min, bits=target_bits - potential_credit))
                if target_bits > potential_credit else 1,
            "largest_allowed_m": m_max,
            "largest_m_minimum_ungrinded_draws": minimum_queries(high_m),
            "largest_m_minimum_draws_with_full_hypothetical_query_credit":
                minimum_queries(circle(m_max, bits=target_bits - potential_credit))
                if target_bits > potential_credit else 1,
            "m3_candidate_query_term_integer_bits": candidate_query_bits(low_m),
            "largest_m_candidate_query_term_integer_bits": candidate_query_bits(high_m),
            "largest_m_minimum_ideal_masked_draws_if_independent_raw_words":
                minimum_ideal_m31_masked_queries(high_m),
            "favorable_remark26_leading_upper_envelope_L1_m3_lower_endpoint":
                fraction_text(leading_lower),
            "favorable_remark26_leading_upper_envelope_L1_m3_upper_endpoint":
                fraction_text(leading_upper),
            "favorable_remark26_leading_upper_envelope_alone_exceeds_target":
                leading_lower > target,
            "extrema_warning": "m=3 minimizes this leading commitment envelope; m=N/2 minimizes the query envelope. They are incompatible choices, and L=1 is not the extracted native batch width.",
        },
        "hypothetical_query_only_design_space": design_space,
        "blocking_premises": [
            "prove native binary/source correspondence and successful verification for this exact package",
            "prove emitted multi-domain AIR/PCS/FRI protocol refines the published theorem relation",
            "extract actual C, d, batch widths, multiplicities, small-table conditions and every round error",
            "prove exact native transcript, 26-bit grinding and Merkle binding reduction with adversary budget",
            "only then choose and test a changed native FRI tuple; this diagnostic never modifies it",
        ],
        "interpretation": "A lower bound on a published proof envelope is not a lower bound on attack success; no native security level follows.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed gate package")
    parser.add_argument("--target-bits", type=int, default=96)
    parser.add_argument("--require-proven", action="store_true",
                        help="fail closed while native theorem premises remain open")
    args = parser.parse_args(argv)
    try:
        result = feasibility_from_gate(extract_gate(args.package.resolve()), args.target_bits)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"PCS/FRI gate conservative feasibility rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
