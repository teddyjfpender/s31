#!/usr/bin/env python3
"""Exact *conditional* P05 Gate batching floor, never native security bits.

The S-two Protocol 3 common padded batch width is M=max_i M_i. This ledger
isolates the positive (T+1)/T * (M-1)*D0/|QM31| factor with candidate
D0=N*B^2 and R>=1. It is a necessary arithmetic check, not the theorem's
complete batching bound. The 193-column source bucket is reported by the
source-bound pcs_fri_gate_paper_batch_boundary.py diagnostic; parameters here
are conditional and are not independently source-bound.
"""

from __future__ import annotations

import argparse
import json
from math import ceil


def ledger() -> dict[str, object]:
    q = (1 << 31) - 1
    field_size = q**4
    n = 1 << 20
    blowup = 2
    d0 = n * blowup**2
    target_bits = 96
    t = 1 << 64
    target_denominator = 1 << target_bits
    # Observed by the source-bound Gate paper-batch diagnostic. This script
    # does not independently replay that sealed package or certify its roster.
    source_columns = 193
    # The selected target is epsilon(T)/T <= 2^-96. Even for the minimum
    # possible R=1, the BCS factor is (T+1)/T, never exactly one.
    max_excess = (field_size * t) // (d0 * target_denominator * (t + 1))
    max_batch_width = max_excess + 1

    def case(label: str, width: int) -> dict[str, object]:
        min_groups_for_max_term = ceil(width / max_batch_width)
        min_groups_if_additive = max(1, width - max_excess)
        return {
            "label": label,
            "conditional_total_functions": width,
            "unpartitioned_M_lower_bound": width,
            "unpartitioned_lower_term_over_target": {
                "numerator": (width - 1) * d0 * target_denominator * (t + 1),
                "denominator": field_size * t,
                "exceeds_one": (width - 1) > max_excess,
            },
            "minimum_groups_if_only_each_group_max_term_is_checked": min_groups_for_max_term,
            "minimum_groups_if_group_batch_terms_are_additive": min_groups_if_additive,
        }

    return {
        "schema": "s31-p05-gate-batch-partition-necessary-floor-v1",
        "status": "conditional_theorem_arithmetic_only",
        "native_security_bits": None,
        "proven_release_admissible": False,
        "native_to_paper_batch_width_M": None,
        "source_bucket": {
            "native_source_log_height": 4,
            "physical_columns": source_columns,
            "condition": "each source column maps uncompressed to one paper domain batch",
            "source_bound_diagnostic": "scripts/release/pcs_fri_gate_paper_batch_boundary.py",
            "this_script_replays_source_roster": False,
        },
        "candidate_paper_parameters": {
            "N": n,
            "B": blowup,
            "D0_assumed_N_times_B_squared": d0,
            "field_cardinality_QM31": field_size,
            "work_factor_target_bits_at_T_2_to_64": target_bits,
            "T_hash_queries": t,
            "minimum_BCS_rounds_R": 1,
        },
        "isolated_factor": "((T+1)/T)*(M-1)*D0/|QM31| with R>=1",
        "largest_integer_M_passing_isolated_factor": max_batch_width,
        "cases": [
            case("originals_only", source_columns),
            case("one_original_and_one_own_quotient_per_column_same_batch",
                 2 * source_columns),
        ],
        "caveats": [
            "M is the theorem's maximum zero-padded per-domain batch width, not the physical column count",
            "the source-log-4 mapping and D0=N*B^2 substitution remain unproved",
            "the complete batching expression has additional positive list factors",
            "splitting requires a new correlated-agreement and multi-instance composition theorem",
            "the additive-group count is conditional on summing these isolated positive terms",
            "AIR, OOD, fold, query, BCS, collision and PoW terms are omitted",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args()
    report = ledger()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
