#!/usr/bin/env python3
"""Fail-closed P09/P07 theorem-interface ledger for a sealed fold-step-1 gate.

The input is re-extracted from a locally trusted package, including its native
check-key command. The ledger is a map of *missing* theorem substitutions,
not a soundness calculation. In particular a native FRI domain is not silently
identified with either paper's degree parameter or initial oracle domain.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.release.pcs_fri_gate_final_domain import extract_gate
from scripts.release.pcs_fri_proven_preflight import masked_m31_max_set_bias

CIRCLE = "https://eprint.iacr.org/2024/278.pdf"
STWO = "https://eprint.iacr.org/2026/532.pdf"
STWO_MAP = "https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md"


def ratio(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def ledger_from_gate(report: dict) -> dict:
    """Prepare a conditional input ledger; never certify an arbitrary report.

    Production callers must use extract_gate, which rechecks the package and
    pinned source. This pure function makes the mapping testable without
    executing a native package binary in tests.
    """
    if (report.get("lowering"), report.get("key_schema"), report.get("profile")) != (
            "gate", "s31-verification-key-gate-roster-v1", "circuit-v1"):
        raise ValueError("ledger requires a reviewed sealed gate key")
    if report.get("package_checks", {}).get("native_check_key") != "accepted":
        raise ValueError("ledger requires native check-key acceptance")
    fri = report.get("fri", {})
    if fri != {"pow_bits": 26, "log_blowup_factor": 1,
               "last_layer_degree_bound": 1, "raw_queries": 70,
               "fold_step": 1}:
        raise ValueError("ledger requires the source-pinned fold-step-1 tuple")
    final = report.get("gate_final_domain", {})
    if final.get("status") != "conditional_source_bound_geometry":
        raise ValueError("missing conditional gate-domain derivation")
    n = report.get("candidate_N_trace_rows")
    d = final.get("fri_input_domain_rows")
    if (type(n) is not int or type(d) is not int or n != 1 << 20 or
            d != 1 << 21 or report.get("max_trace_log_size") != 20 or
            final.get("fri_input_domain_log") != 21 or
            final.get("fri_input_degree_bound_log") != 20 or
            final.get("split_composition_log_degree_bound") != 20 or
            final.get("committed_composition_column_log_size") != 20 or
            report.get("theorem_inputs", {}).get("D_final_fri_domain") != d):
        raise ValueError("ledger requires the reviewed 2^20/2^21 gate geometry")
    if report.get("status") != "incomplete" or report.get("proven_release_admissible") is not False:
        raise ValueError("upstream geometry must remain fail closed")

    # The numerator N+1 belongs to a *candidate* Circle STARKs rate. The
    # native-to-paper identification of N is deliberately still absent.
    candidate_rho = Fraction(n + 1, d)
    query_bias = masked_m31_max_set_bias(final["fri_input_domain_log"])
    return {
        "schema": "s31-pcs-fri-gate-error-ledger-v1",
        "scope": "one sealed gate package with fold_step=1 and 2^20 maximum trace rows",
        "status": "blocked",
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "published_anchors": {
            "circle_theorems_6_7": CIRCLE + "#appendix-B",
            "stwo_flat_air_multi_fri_nirop": STWO,
            "stwo_official_theorem_map": STWO_MAP,
        },
        "source_bound_observations": {
            "candidate_max_trace_rows": n,
            "fri_input_domain_rows": d,
            "fri_input_domain_status": "conditional on successful execution of the pinned verifier path",
            "raw_query_draws": fri["raw_queries"],
            "fold_step": fri["fold_step"],
            "log_blowup_factor": fri["log_blowup_factor"],
            "pow_bits": fri["pow_bits"],
            "pow_interpretation": "native parameter only; no soundness multiplier assigned",
            "last_layer_degree_bound": fri["last_layer_degree_bound"],
            "package_manifest_sha256": report["package_checks"].get("package_manifest_sha256"),
            "verification_key_sha256": report["package_checks"].get("verification_key_sha256"),
            "engine_gitlink": report.get("source_binding", {}).get("engine_gitlink"),
            "air_bundle_sha256": final.get("air_bundle_sha256"),
            "package_geometry_source_sha256": report.get("source_binding", {}).get("source_sha256"),
            "gate_domain_source_sha256": final.get("source_sha256"),
        },
        "conditional_geometry_premises": [
            "installed native executable corresponds to the checked-out pinned source",
            "sealed key, official AIR bundle, roster and source guard describe that executable",
            "the exact verifier path reaches proof acceptance; check-key alone is insufficient",
        ],
        "theorem_parameter_mapping": {
            "circle_N_degree_parameter": None,
            "circle_D_standard_position_coset": None,
            "stwo_initial_oracle_domains": None,
            "C_constraint_count": None,
            "d_air_degree": None,
            "L_batch_width": None,
            "m_johnson_multiplicity": None,
            "theta_proximity": None,
            "list_size_bound": None,
            "extension_field_order": None,
            "reason": "native geometry and a key tuple do not establish the published oracle, degree, list-decoding or multi-domain relation",
        },
        "conditional_circle_query_comparison": {
            "candidate_rho_if_N_equals_max_trace_rows": ratio(candidate_rho),
            "ideal_m31_masked_max_positive_set_bias": ratio(query_bias),
            "symbolic_bound": "((1 + 1/(2m))*sqrt((N+1)/D) + bias)^s",
            "candidate_substitution": "N=1048576, D=2097152, s=70, bias=1/2147483648; m is unbound",
            "bound_value": None,
            "premises": [
                "prove native N and D identify the exact Circle STARKs theorem oracle and standard-position coset",
                "choose m>=3 and discharge every finite-domain, Johnson and list-size condition",
                "prove a fixed good query set before sampling and independent ideal raw hash words",
                "prove the native reduced-and-masked law and all 70 raw checks match the theorem relation",
            ],
            "role": "candidate query-event comparison only; not a Stwo multi-domain round error",
        },
        "interactive_round_errors": {
            "flat_air_logup": None,
            "composition": None,
            "oods_degree_corrected_batch": None,
            "multi_domain_fri_batching": None,
            "multi_domain_fri_each_fold": None,
            "raw_query_check": None,
            "published_max_round_error": None,
            "missing": "instantiate the complete Stwo flat-AIR and multi-domain FRI per-round bounds; Circle Theorem 6 query arithmetic cannot replace them",
        },
        "noninteractive_rom_bcs": {
            "theorem_expression": "(T+R)*max_i(epsilon_i) + 3*(T^2+1)/2^lambda",
            "T_adversary_hash_query_budget": None,
            "R_transformation_round_count": None,
            "lambda_theorem_oracle_output_bits": None,
            "hash_collision_binding_term": "3*(T^2+1)/2^lambda, only under the theorem's exact BCS/ROM model",
            "hash_collision_binding_bound": None,
            "native_merkle_binding_failure_bound": None,
            "native_blake2s_rom_instantiation": None,
            "native_pow_grinding_reduction": None,
            "bound_value": None,
            "missing": [
                "state a finite adversary budget T and the theorem's round count R for this exact transcript",
                "prove the selected native BLAKE2s channel, Merkle encoding and nonce/grinding schedule instantiate the BCS/ROM model",
                "identify lambda from that reduction; a 32-byte digest or 26 PoW bits alone is insufficient",
                "account for native Merkle binding/collision events without silently assuming they are covered by the BCS term",
            ],
        },
        "native_to_published_refinement_failure_bound": None,
        "whole_proof_error_bound": None,
        "release_gate": "closed until every theorem parameter, round error, ROM/BCS budget, collision event and native refinement premise is discharged",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="locally trusted sealed gate package")
    parser.add_argument("--require-proven", action="store_true",
                        help="fail closed while this ledger has open theorem premises")
    args = parser.parse_args(argv)
    try:
        report = ledger_from_gate(extract_gate(args.package.resolve()))
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"PCS/FRI gate error ledger rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
