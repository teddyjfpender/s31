#!/usr/bin/env python3
"""Exact S-two 2026 unique-decoding theorem arithmetic; no native certificate.

The published IOP/BCS formulas are evaluated only for explicitly hypothetical
parameters. Gate observations remain separate and all native proof terms stay
unbound until a protocol correspondence and ROM reduction are proved.
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

PAPER = "https://eprint.iacr.org/2026/532.pdf"
Q = 2**31 - 1
F = Q**4
# q == 3 (mod 4), while q^4 == 1 (mod 4): the respective circles have
# q+1 and q^4-1 affine points. Protocol 1 samples outside C(F_q).
PAPER_OOD_POINTS = (F - 1) - (Q + 1)
DOMAIN_CAP = 2**30


def exact(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def integer(value: object, label: str, lower: int = 0, upper: int = 1 << 64) -> int:
    if type(value) is not int or not lower <= value <= upper:
        raise ValueError(f"{label} must be an integer in {lower}..{upper}")
    return value


def power_of_two(value: int, label: str) -> int:
    if value < 1 or value & (value - 1):
        raise ValueError(f"{label} must be a power of two")
    return value


MAX_QUERIES = 100000


def minimum_query_draws(alpha: Fraction, multiplier: int,
                        collision: Fraction, target: Fraction) -> int | None:
    """Least supported s meeting the query term, using exact binary search."""
    if not 0 < alpha < 1 or multiplier < 1 or not 0 <= collision < target:
        raise ValueError("query target unavailable")
    lo, hi = 1, 1
    while multiplier * alpha**hi + collision > target and hi < MAX_QUERIES:
        lo = hi + 1
        hi = min(2 * hi, MAX_QUERIES)
    if multiplier * alpha**hi + collision > target:
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if multiplier * alpha**mid + collision <= target:
            hi = mid
        else:
            lo = mid + 1
    return lo


def udr_boundary_minimum_draws(blowup: int, multiplier: int,
                               collision: Fraction, target: Fraction) -> int | None:
    """Necessary count at excluded theta=delta/2, so equality is insufficient."""
    rho = Fraction(1, blowup)
    alpha_limit = (1 + rho) / 2
    draws = minimum_query_draws(alpha_limit, multiplier, collision, target)
    if draws is None:
        return None
    if multiplier * alpha_limit**draws + collision == target:
        draws += 1
    return draws if draws <= MAX_QUERIES else None


def circle_fold_sizes(n: int, blowup: int) -> list[int]:
    """Protocol-4 full ensemble: D0=N*B², then line domains through B."""
    size = n * blowup * blowup // 2
    values = []
    while size >= blowup:
        values.append(size)
        size //= 2
    return values


def scenario_arithmetic(scenario: dict, target_bits: int = 96) -> dict:
    """Evaluate *all quoted terms* for a supplied paper-protocol scenario.

    No input field is accepted as evidence of native verifier correspondence.
    In particular, a numerical pass never sets native_proven_security_bits.
    """
    if not isinstance(scenario, dict):
        raise ValueError("scenario must be an object")
    if scenario.get("paper_protocol_variant") != "idealized_protocols_1_3_4_degree_corrected":
        raise ValueError("scenario must name the paper's degree-corrected protocol variant")
    if scenario.get("grinding_bits") != 0:
        raise ValueError("this conservative ledger assigns zero grinding credit")
    target_bits = integer(target_bits, "target bits", 1, 256)
    target = Fraction(1, 1 << target_bits)
    n = power_of_two(integer(scenario.get("N"), "N", 2, 1 << 30), "N")
    b = power_of_two(integer(scenario.get("B"), "B", 2, 1 << 30), "B")
    if n * b * b > DOMAIN_CAP:
        raise ValueError("published circle domain capacity N*B^2 <= 2^30 fails")
    rho = Fraction(1, b)
    theta = Fraction(integer(scenario.get("theta_numerator"), "theta numerator", 1),
                     integer(scenario.get("theta_denominator"), "theta denominator", 1))
    if not 0 < theta < (1 - rho) / 2:
        raise ValueError("theta must be strictly inside unique-decoding regime")
    alpha = 1 - theta
    s = integer(scenario.get("queries"), "query count", 1, MAX_QUERIES)
    t = integer(scenario.get("T"), "adversary hash-query budget T", 1)
    rounds = integer(scenario.get("R"), "BCS round count R", 1, 100000)
    hash_bits = integer(scenario.get("lambda_bits"), "ROM output bits lambda", 1, 512)
    if hash_bits != 256:
        raise ValueError("only the paper's 256-bit BLAKE2s candidate is modeled")
    degree = integer(scenario.get("air_degree"), "AIR degree", 1, 100000)
    if degree > b + 1:
        raise ValueError("published AIR degree cap fails")
    max_message_dim = integer(scenario.get("max_message_dimension"), "r", 1, 100000)
    inputs = integer(scenario.get("public_input_messages"), "k_in", 0, 100000)
    outputs = integer(scenario.get("public_output_messages"), "k_out", 0, 100000)
    width = integer(scenario.get("fri_batch_max_width"), "FRI batch width M", 1, 1000000)
    tables = scenario.get("tables")
    if not isinstance(tables, list) or not tables:
        raise ValueError("at least one explicit table is required")
    parsed = []
    for index, table in enumerate(tables):
        if not isinstance(table, dict):
            raise ValueError("table must be an object")
        row = power_of_two(integer(table.get("rows"), f"table {index} rows", 2, n),
                           f"table {index} rows")
        constraints = integer(table.get("air_constraints"),
                              f"table {index} AIR constraints k_t", 1, 1000000)
        uses = integer(table.get("uses"), f"table {index} uses", 0, 1000000)
        yields = integer(table.get("yields"), f"table {index} yields", 0, 1000000)
        multiplicity = integer(table.get("max_use_multiplicity"),
                               f"table {index} use multiplicity", 0, Q - 1)
        if alpha <= rho * (1 + Fraction(2, row)):
            raise ValueError("paper's small-table OOD condition fails")
        parsed.append((row, constraints, uses, yields, multiplicity))
    if max(row for row, *_ in parsed) != n:
        raise ValueError("N must equal the maximum nonzero table height")
    folds = scenario.get("fri_fold_domain_sizes")
    expected_folds = circle_fold_sizes(n, b)
    if folds != expected_folds:
        raise ValueError("hypothetical Protocol-3 single-fold domain list differs")
    min_rounds = 3 + 1 + len(folds) + 1
    if rounds < min_rounds:
        raise ValueError("R undercounts AIR, FRI batching, folds or query phase")

    # Appendix A.4 Lemmas 5–7 with list size ell=1 by Remark 8. Theorem 3
    # displays a different composition numerator from Lemma 6 and Table 4;
    # keep both and use their maximum. Lemma 7's OOD numerator also exceeds
    # Theorem 3's displayed 1+deg(A)*N under the paper's deg(A)<=B+1 cap.
    logup_numerator = max_message_dim * (
        inputs + outputs + sum((uses + yields) * row for row, _, uses, yields, _ in parsed))
    composition_appendix_numerator = sum(constraints + uses + yields
                                         for _, constraints, uses, yields, _ in parsed)
    composition_theorem3_numerator = 2 + max(constraints + uses + yields
                                             for _, constraints, uses, yields, _ in parsed)
    composition_numerator = max(composition_appendix_numerator,
                                composition_theorem3_numerator)
    alternative_bounds = {
        "air_composition_theorem3_displayed": Fraction(composition_theorem3_numerator, F),
        "air_composition_appendix_lemma6_table4": Fraction(composition_appendix_numerator, F),
        "air_ood_theorem3_displayed": Fraction(1 + degree * n, PAPER_OOD_POINTS),
        "air_ood_appendix_lemma7": Fraction(1 + (b + 2) * n, PAPER_OOD_POINTS),
    }
    errors = {
        "air_logup": Fraction(logup_numerator, F),
        "air_composition": Fraction(composition_numerator, F),
        "air_ood": Fraction(1 + (b + 2) * n, PAPER_OOD_POINTS),
        "fri_cross_domain_batching": Fraction((width - 1) * n * b * b, F),
        "fri_query": alpha**s,
    }
    fold_errors = [Fraction(3 * size, F) for size in folds]
    for i, value in enumerate(fold_errors):
        errors[f"fri_fold_{i}"] = value
    max_error = max(errors.values())
    collision = Fraction(3 * (t * t + 1), 1 << hash_bits)
    bcs = (t + rounds) * max_error + collision
    work_factor = bcs / t
    nonquery_max = max(value for name, value in errors.items() if name != "fri_query")
    absolute_query_budget = (target - collision) / (t + rounds)
    work_query_budget = (t * target - collision) / (t + rounds)
    absolute_queries = (minimum_query_draws(alpha, t + rounds, collision, target)
                        if collision < target else None)
    work_queries = (minimum_query_draws(alpha, t + rounds, collision, t * target)
                    if collision < t * target else None)
    absolute_nonquery_fits = (t + rounds) * nonquery_max + collision <= target
    work_nonquery_fits = (t + rounds) * nonquery_max + collision <= t * target
    return {
        "schema": "s31-stwo-2026-udr-hypothetical-formula-v1",
        "status": "hypothetical_paper_arithmetic_only",
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "target_bits": target_bits,
        "conditional_absolute_error_meets_target": bcs <= target,
        "conditional_paper_work_factor_meets_target": work_factor <= target,
        "paper_inputs": {"N": n, "B": b, "D0_with_composition_quotient": n * b * b,
                         "rho": exact(rho), "theta": exact(theta),
                         "alpha": exact(alpha), "queries": s, "T": t, "R": rounds,
                         "lambda_bits": hash_bits, "air_degree": degree,
                         "paper_protocol_variant": scenario["paper_protocol_variant"],
                         "grinding_bits": 0,
                         "max_message_dimension": max_message_dim,
                         "public_input_messages": inputs, "public_output_messages": outputs,
                         "fri_batch_max_width": width,
                         "fri_fold_domain_sizes": folds,
                         "tables": [{"rows": row, "air_constraints": constraints,
                                     "uses": uses, "yields": yields,
                                     "max_use_multiplicity": multiplicity}
                                    for row, constraints, uses, yields, multiplicity in parsed]},
        "published_round_error_bounds": {key: exact(value) for key, value in errors.items()},
        "published_formula_discrepancy_bounds": {
            key: exact(value) for key, value in alternative_bounds.items()},
        "conservative_formula_selection": {
            "air_composition": "maximum of Theorem 3 display and Appendix Lemma 6/Table 4",
            "air_ood": "Appendix Lemma 7; dominates Theorem 3 display under deg(A)<=B+1",
            "fri_batching_and_folds": "full Protocol 4 ensemble includes q at D0=N*B^2",
        },
        "largest_round_bound": exact(max_error),
        "nonquery_largest_round_bound": exact(nonquery_max),
        "BCS_collision_term": exact(collision),
        "BCS_total_formula": exact(bcs),
        "BCS_total_over_T_paper_security_measure": exact(work_factor),
        "absolute_query_budget_after_BCS": exact(absolute_query_budget),
        "paper_work_factor_query_budget_after_BCS": exact(work_query_budget),
        "minimum_queries_for_absolute_target_if_other_rounds_fit": absolute_queries,
        "minimum_queries_for_paper_work_factor_target_if_other_rounds_fit": work_queries,
        "other_rounds_fit_absolute_target": absolute_nonquery_fits,
        "other_rounds_fit_paper_work_factor_target": work_nonquery_fits,
        "native_mapping_and_cryptographic_unknowns": [
            "native executable, key and committed columns instantiate all scenario table and batch widths",
            "source AIR and logUp constraints instantiate the published flat-AIR relation",
            "native lifted openings, FRI insertion/folds and quotient ensemble instantiate Protocols 3 and 4",
            "exact native query sampler matches the theorem's query distribution and projection model",
            "native OOD sampler and conjugate quotient use the paper's claimed cardinality and degree bound",
            "native BLAKE2s transcript, Merkle paths and grinding instantiate the BCS/ROM theorem",
            "T and R are justified for the chosen adversary and the actual transcript",
        ],
    }


def necessary_tradeoffs(n: int, target_bits: int, t: int,
                        lambda_bits: int = 256) -> list[dict]:
    """Necessary UDR tradeoffs at a given candidate height, not a profile search."""
    n = power_of_two(integer(n, "N", 2, 1 << 30), "N")
    target_bits = integer(target_bits, "target bits", 1, 256)
    t = integer(t, "adversary hash-query budget T", 1)
    if lambda_bits != 256:
        raise ValueError("only lambda=256 is modeled")
    target = Fraction(1, 1 << target_bits)
    b = 2
    out = []
    while n * b * b <= DOMAIN_CAP:
        folds = circle_fold_sizes(n, b)
        r_min = 3 + 1 + len(folds) + 1
        multiplier = t + r_min
        collision = Fraction(3 * (t * t + 1), 1 << lambda_bits)
        ood = Fraction(1 + (b + 2) * n, PAPER_OOD_POINTS)
        first_fold = Fraction(3 * n * b * b // 2, F)
        floor = multiplier * max(ood, first_fold) + collision
        absolute_query_only = (udr_boundary_minimum_draws(b, multiplier, collision, target)
                               if collision < target else None)
        work_query_only = (udr_boundary_minimum_draws(b, multiplier, collision, t * target)
                           if collision < t * target else None)
        out.append({
            "hypothetical_B": b,
            "candidate_D0": n * b * b,
            "minimal_paper_rounds_R": r_min,
            "OOD_published_bound": exact(ood),
            "first_FRI_fold_published_bound": exact(first_fold),
            "BCS_necessary_nonquery_envelope": exact(floor),
            "BCS_necessary_nonquery_envelope_over_T": exact(floor / t),
            "nonquery_envelope_exceeds_absolute_target": floor > target,
            "nonquery_envelope_exceeds_paper_work_factor_target": floor > t * target,
            "minimum_queries_at_excluded_udr_boundary_for_absolute_target": absolute_query_only,
            "minimum_queries_at_excluded_udr_boundary_for_paper_work_factor_target": work_query_only,
            "native_supported_or_admissible": None,
        })
        b *= 2
    return out


def gate_udr_ledger(report: dict, target_bits: int = 96, t: int = 1 << 32,
                    scenario: dict | None = None) -> dict:
    source = ledger_from_gate(report)
    observed = source["source_bound_observations"]
    n = observed["candidate_max_trace_rows"]
    native_b = 1 << observed["log_blowup_factor"]
    rows = necessary_tradeoffs(n, target_bits, t)
    native_row = next((row for row in rows if row["hypothetical_B"] == native_b), None)
    if native_row is None:
        raise ValueError("native Gate N/B is outside the paper's N*B^2 domain capacity")
    candidate = scenario_arithmetic(scenario, target_bits) if scenario is not None else None
    target = Fraction(1, 1 << target_bits)
    # Independently of N/B, Lemma 7 contains a positive numerator >=1,
    # while |C(F)\C(F_q)| < |F| < 2^124. Theorem 6 has T+R >= T.
    universal_ood_floor = Fraction(t, F)
    return {
        "schema": "s31-stwo-2026-udr-gate-ledger-v1",
        "status": "native_theorem_premises_open",
        "proven_release_admissible": False,
        "native_proven_security_bits": None,
        "published_anchor": PAPER,
        "target_bits": target_bits,
        "hypothetical_T": t,
        "native_source_observations": {
            "candidate_N": n, "configured_B": native_b,
            "configured_raw_queries": observed["raw_query_draws"],
            "configured_pow_bits_without_credit": observed["pow_bits"],
            "configured_fold_step": observed["fold_step"],
            "key_sha256": observed["verification_key_sha256"],
        },
        "QM31_universal_absolute_BCS_OOD_floor_if_paper_applies": exact(universal_ood_floor),
        "QM31_universal_absolute_OOD_floor_exceeds_target": universal_ood_floor > target,
        "QM31_universal_paper_work_factor_OOD_floor_if_paper_applies": exact(Fraction(1, F)),
        "QM31_universal_paper_work_factor_OOD_floor_exceeds_target": Fraction(1, F) > target,
        "native_geometry_necessary_row": native_row,
        "all_hypothetical_blowup_rows": rows,
        "unbound_native_theorem_terms": {
            "air_logup": None, "air_composition": None, "air_ood": None,
            "fri_cross_domain_batching": None, "fri_fold_each": None,
            "fri_query": None, "BCS_round_count_R": None,
            "BCS_collision_and_Merkle": None, "native_to_paper_refinement": None,
        },
        "hypothetical_complete_formula": candidate,
        "release_gate": "closed even if hypothetical formula passes; exact native protocol and ROM premises are unproved",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed Gate package")
    parser.add_argument("--target-bits", type=int, default=96)
    parser.add_argument("--adversary-hash-queries", type=int, default=1 << 32)
    parser.add_argument("--hypothetical-scenario", type=Path)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args(argv)
    try:
        scenario = (json.loads(args.hypothetical_scenario.read_text())
                    if args.hypothetical_scenario else None)
        result = gate_udr_ledger(extract_gate(args.package.resolve()),
                                 args.target_bits, args.adversary_hash_queries, scenario)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"S-two UDR ledger rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
