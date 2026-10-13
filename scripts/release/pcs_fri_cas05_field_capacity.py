#!/usr/bin/env python3
"""Exact paper-only capacity check for a short CAS05-shaped FRI cascade.

This compares *single-point Protocol-4 upper-bound expressions* from the
S-two unique-decoding theorem. CAS05 instead uses a conjugate two-point
quotient; its Section-4.5 bad-set and Eq.-80 uniqueness arguments must be
derived before these expressions can inform a native bound. This tool does
not establish that CAS05 implements the paper's protocol or that an extension
field, BCS transcript, or OOD sampler exists in native code. No security bits
are assigned to the native verifier.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_paired_ood_bridge import candidate_cas05_geometry
from scripts.release.pcs_fri_stwo_udr import (
    F, Q, exact, minimum_query_draws, scenario_arithmetic,
)


def field_rows(scenario: dict, height_count: int, target_bits: int = 96,
               short_rounds: int | None = None,
               degrees: tuple[int, ...] = (2, 4, 6, 8)) -> dict:
    """Re-evaluate the quoted UDR expressions over hypothetical even degrees.

    The input is an explicit, validated *full* idealized paper scenario. The
    short cascade keeps the first ``height_count`` folds. ``short_rounds``
    is an independently supplied hypothetical BCS count, never extracted
    from native source. Zero grinding credit is inherited from the validator.
    """
    paper = scenario_arithmetic(scenario, target_bits)
    inputs = paper["paper_inputs"]
    geometry = candidate_cas05_geometry(inputs, height_count)
    minimum_rounds = geometry["minimum_idealized_BCS_round_count"]
    rounds = inputs["R"] if short_rounds is None else short_rounds
    if type(rounds) is not int or rounds < minimum_rounds:
        raise ValueError("short R undercounts the idealized batch/fold/query phases")
    if not degrees or len(set(degrees)) != len(degrees) or any(
            type(degree) is not int or degree < 2 or degree > 16 or degree % 2
            for degree in degrees):
        raise ValueError("field degrees must be distinct even integers in 2..16")

    t = inputs["T"]
    alpha = Fraction(inputs["alpha"])
    target = Fraction(1, 1 << target_bits)
    collision = Fraction(paper["BCS_collision_term"])
    errors_q4 = {name: Fraction(value) for name, value in
                 paper["published_round_error_bounds"].items()}
    source_nonquery = {name: value for name, value in errors_q4.items()
                       if name != "fri_query" and
                       (not name.startswith("fri_fold_") or
                        int(name.removeprefix("fri_fold_")) < height_count)}
    if len([name for name in source_nonquery if name.startswith("fri_fold_")]) != height_count:
        raise ValueError("short fold roster does not match paper scenario")

    out = []
    for degree in degrees:
        cardinality = Q ** degree
        # For even degree, -1 is square in F_(q^degree): its affine circle
        # has q^degree-1 points. Remove the q+1 base-circle points.
        ood_points = cardinality - Q - 2
        if ood_points <= 0:
            raise ValueError("candidate OOD domain is empty")
        errors = {name: value * F / cardinality for name, value in source_nonquery.items()
                  if name != "air_ood"}
        ood_numerator = 1 + (inputs["B"] + 2) * inputs["N"]
        errors["air_ood"] = Fraction(ood_numerator, ood_points)
        if degree == 4 and errors != source_nonquery:
            raise ValueError("QM31 source formula changed during field scaling")
        nonquery_max = max(errors.values())
        multiplier = t + rounds
        nonquery_total = multiplier * nonquery_max + collision
        query_absolute = (minimum_query_draws(alpha, multiplier, collision, target)
                          if collision < target else None)
        query_work = (minimum_query_draws(alpha, multiplier, collision, t * target)
                      if collision < t * target else None)
        actual_query = alpha ** inputs["queries"]
        total = multiplier * max(nonquery_max, actual_query) + collision
        out.append({
            "extension_degree_over_M31": degree,
            "contains_CM31_as_subfield": True,
            "hypothetical_field_cardinality": cardinality,
            "paper_ood_point_count": ood_points,
            "largest_nonquery_paper_round": max(errors, key=errors.get),
            "largest_nonquery_paper_bound": exact(nonquery_max),
            "nonquery_BCS_expression": exact(nonquery_total),
            "nonquery_fits_absolute_target": nonquery_total <= target,
            "nonquery_fits_paper_work_factor_target": nonquery_total <= t * target,
            "minimum_queries_for_absolute_target_if_nonquery_fits": (
                query_absolute if nonquery_total <= target else None),
            "minimum_queries_for_paper_work_factor_target_if_nonquery_fits": (
                query_work if nonquery_total <= t * target else None),
            "given_scenario_query_count": inputs["queries"],
            "given_scenario_full_BCS_expression": exact(total),
            "given_scenario_fits_absolute_target": total <= target,
            "given_scenario_fits_paper_work_factor_target": total <= t * target,
            "native_field_implemented_or_admissible": False,
        })
    return {
        "schema": "s31-cas05-short-field-capacity-v1",
        "status": "hypothetical_paper_arithmetic_only",
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "target_bits": target_bits,
        "target_meanings": {
            "absolute": "epsilon(T) <= 2^-target_bits",
            "paper_work_factor": "epsilon(T)/T <= 2^-target_bits",
        },
        "hypothetical_inputs": {
            "N": inputs["N"], "B": inputs["B"], "D0": inputs["D0_with_composition_quotient"],
            "height_count": height_count, "short_R": rounds,
            "minimum_idealized_short_R": minimum_rounds, "T": t,
            "theta": inputs["theta"], "queries": inputs["queries"],
            "lambda_bits": inputs["lambda_bits"], "grinding_bits": 0,
        },
        "field_rows": out,
        "native_correspondence_required": [
            "a concrete extension field and native prover/verifier for that field",
            "source-bound AIR, original-plus-quotient, and variable-r Protocol-3 correspondence",
            "native OOD support and bad-set bound for the selected extension field",
            "native independent query law, Merkle/BCS/ROM reduction, and source-derived R and T",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scenario", type=Path, help="explicit idealized full paper scenario JSON")
    parser.add_argument("--height-count", type=int, required=True)
    parser.add_argument("--short-rounds", type=int,
                        help="hypothetical BCS R for the short variant")
    parser.add_argument("--target-bits", type=int, default=96)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = field_rows(json.loads(args.scenario.read_text()), args.height_count,
                            args.target_bits, args.short_rounds)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"CAS05 field capacity rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
