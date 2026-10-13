#!/usr/bin/env python3
"""Pinned v0.1 PCS/FRI theorem-admission blockers, never a security certificate.

The matrix records the published theorem interfaces that are still missing
for the current native S31 verifier. File hashes make the review scope
auditable. A changed source or profile roster requires a new reviewed matrix;
neither a file's existence nor a passing local test discharges an obligation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.release.release_candidate import AUDIT_CASES
from scripts.release.s31_v01_audit import CASES
from scripts.s31_formal_lib.pcs_fri_query_epoch import audit as audit_query_epoch


MATRIX = ROOT / "design/s31/security/pcs-fri-v01-blockers.json"
EXPECTED_PROFILE_STEPS = {
    "gate": 1, "gate-fri4": 4, "chip": 1, "sparse-gate": 1,
    "sparse-chip": 1, "sparse-wide-gate": 1,
    "sparse-wide-gate-fri4": 4, "direct-gate": 1,
    "direct-chip": 1, "sha-joint": 1, "sha-shift": 1, "sha-fused": 1,
}

CIRCLE = "https://eprint.iacr.org/2024/278.pdf"
STWO = "https://eprint.iacr.org/2026/532.pdf"

# These are proof obligations, not test names or estimated completion scores.
OBLIGATIONS = (
    {
        "id": "P01_ACTUAL_GEOMETRY",
        "gap_kind": "uninstantiated_theorem_premise",
        "published_requirement": "Circle STARKs Theorems 6/7: bind each N, D, C, d, L, m, rate, list bound and every component domain to the verified oracle",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["scripts/release/pcs_fri_proven_preflight.py", "formal/s31/proof-inventory.json"],
        "missing_discharge": "derive theorem parameters from every sealed native package and check all finite-domain, degree and small-table preconditions",
    },
    {
        "id": "P02_AIR_AND_INTERACTION_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 7 and Stwo flat-AIR IOPP: committed columns, constraints, logUp multiplicities and composition must realize the theorem relation",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/proof-inventory.json", "design/s31/security/MIXED_N1_N8_CONDITIONAL_ERROR_LEDGER_2026-10-12.md"],
        "missing_discharge": "complete source/compiler-to-native AIR correspondence, committed-column origin and program-wide lookup/interaction soundness",
    },
    {
        "id": "P03_LIFTED_MULTI_DOMAIN_PCS_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Stwo multi-domain circle FRI and batch evaluation: all native lifted roots and cross-domain openings realize one cross-domain oracle relation",
        "published_anchor": STWO,
        "partial_evidence": ["scripts/s31_formal_lib/pcs_fri_projection.py", "formal/s31/S31/Gadgets/PcsFri/LayerAcceptance.lean"],
        "missing_discharge": "end-to-end native verifier simulation including all heights, batching, quotient openings and oracle ownership",
    },
    {
        "id": "P04_FRI_ROUND_AND_TERMINAL_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 6: committed round words, independent challenge order, every fold equation and terminal degree check match Protocol 2",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/FoldAlgebra.lean", "formal/s31/S31/Gadgets/PcsFri/LayerAcceptance.lean"],
        "missing_discharge": "compose local fold and acceptance models with the complete native commitment, opening and terminal control flow",
    },
    {
        "id": "P05_OODS_DEEP_DEGREE_CORRECTION",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 7 and Stwo batch-OOD theorem: sampled values, DEEP quotients and degree correction imply the claimed polynomial identity",
        "published_anchor": STWO,
        "partial_evidence": ["scripts/s31_formal_lib/pcs_fri_order.py", "deps/stwo-zig/src/core/pcs/verifier.zig"],
        "missing_discharge": "prove the native quotient construction and OODS verifier checks instantiate the published batch-evaluation relation",
    },
    {
        "id": "P06_MERKLE_BINDING_AND_DECODER",
        "gap_kind": "unproven_crypto_and_native_refinement",
        "published_requirement": "BCS oracle commitments authenticate precisely the queried rows at the committed roots with a quantitative collision bound",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/MerkleOpening.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofDecoder.lean", "scripts/s31_formal_lib/pcs_fri_leaf_encoding.py"],
        "missing_discharge": "native decoder-to-model semantics, committed-column origin and a cryptographic collision/binding reduction for the exact Blake2s layout",
    },
    {
        "id": "P07_FIAT_SHAMIR_AND_POW_BUDGET",
        "gap_kind": "unproven_crypto_and_budget_reduction",
        "published_requirement": "Stwo NIROP/BCS theorem: bound adversary hash budget T, rounds R, hash collision term and exact native grinding and transcript schedule",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/QueryAndTranscript.lean", "scripts/s31_formal_lib/pcs_fri_order.py", "scripts/s31_formal_lib/pcs_fri_query_epoch.py"],
        "missing_discharge": "ROM/BCS reduction for native Blake2s, nonce selection, PoW accounting, pre-query 32-bit draw-counter wrap bound and transcript domain separation; only the post-nonce raw-query epoch is bounded",
    },
    {
        "id": "P08_QUERY_SET_AND_RAW_WORD_MODEL",
        "gap_kind": "unproven_native_and_random_oracle_refinement",
        "published_requirement": "Circle STARKs Theorem 6 query term assumes a fixed good set and independent uniform positions; native M31 masking must be accounted for",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/M31MaskedQuery.lean", "formal/s31/S31/Gadgets/PcsFri/M31WordReduction.lean"],
        "missing_discharge": "derive a fixed good set from the native committed oracle before each draw and connect ideal raw-word independence to the native channel",
    },
    {
        "id": "P09_COMPLETE_ERROR_LEDGER",
        "gap_kind": "uninstantiated_theorem_error_ledger",
        "published_requirement": "Circle STARKs Theorems 6/7 and Stwo NIROP: sum every justified commitment, AIR, OODS, FRI, Merkle and Fiat-Shamir term before comparing with target bits",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["scripts/release/pcs_fri_proven_preflight.py", "design/s31/security/PCS_FRI_PUBLISHED_BOUND_AUDIT.md"],
        "missing_discharge": "evaluate all theorem terms with actual package parameters and an explicit adversary budget; the current preflight computes only necessary illustrative terms",
    },
    {
        "id": "P10_GROUPED_FOLD_SCHEDULE",
        "gap_kind": "unmatched_protocol_schedule",
        "published_requirement": "A grouped four-fold native round needs its own reduction to the paper's single-fold challenge schedule or a theorem covering that schedule",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["deps/stwo-zig/src/core/fri/config.zig", "formal/s31/S31/Gadgets/PcsFri/FoldAlgebra.lean"],
        "missing_discharge": "prove soundness of one challenge reused over each four-fold group and its exact native commitment schedule",
    },
)

COMMON = tuple(item["id"] for item in OBLIGATIONS if item["id"] != "P10_GROUPED_FOLD_SCHEDULE")
NOMINAL_FRI = {"pow_bits": 26, "log_last_layer_degree_bound": 0,
               "log_blowup_factor": 1, "raw_queries": 70}
FRI_CONFIG_SOURCES = (
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/sha/package/sha_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_shift_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_fused_package_runtime.zig",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gitlink(root: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()


def matrix(root: Path = ROOT) -> dict[str, object]:
    observed = {case.id: case.fri_fold_step for case in CASES}
    if observed != EXPECTED_PROFILE_STEPS or set(observed) != AUDIT_CASES:
        raise ValueError("v0.1 profile roster or FRI schedule changed; review blocker matrix")
    expected_init = "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)"
    if expected_init not in (root / FRI_CONFIG_SOURCES[0]).read_text():
        raise ValueError("native S31 FRI tuple changed; review blocker matrix")
    for name in FRI_CONFIG_SOURCES[1:]:
        if "FriConfigV2.init(26, 0, 1, 70, 1)" not in (root / name).read_text():
            raise ValueError(f"native SHA FRI tuple changed: {name}")
    evidence_paths = sorted({path for item in OBLIGATIONS for path in item["partial_evidence"]} |
                            set(FRI_CONFIG_SOURCES))
    evidence = {}
    for name in evidence_paths:
        path = root / name
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
            raise ValueError(f"missing or unsafe partial evidence: {name}")
        evidence[name] = sha(path)
    current_engine = gitlink(root)
    query_epoch = audit_query_epoch(root)
    if query_epoch["engine_gitlink_commit"] != current_engine or query_epoch["hash_draws"] != 9:
        raise ValueError("v0.1 query epoch source or engine binding changed")
    old_cost = json.loads((root / "design/s31/measurements/language/whole-prover-cost-v8r1.json").read_text())
    cost_engine = old_cost["engine_gitlink_commit"]
    return {
        "schema": "s31-pcs-fri-v01-blockers-v1",
        "release": "v0.1.0",
        "status": "blocked",
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "engine_gitlink_commit": current_engine,
        "source_visible_nominal_fri": {
            **NOMINAL_FRI,
            "fold_step_by_profile": dict(sorted(observed.items())),
            "source_paths": list(FRI_CONFIG_SOURCES),
            "interpretation": "source-pinned nominal configuration; not a proven security level",
        },
        "proof_targets": [CIRCLE, STWO],
        "query_epoch": query_epoch,
        "evidence_sha256": evidence,
        "obligations": [{**item, "status": "open"} for item in OBLIGATIONS],
        "profiles": {
            name: {
                "fri_fold_step": step,
                "proven_release_admissible": False,
                "native_proven_security_bits": None,
                "blocker_ids": [*COMMON, *(["P10_GROUPED_FOLD_SCHEDULE"] if step == 4 else [])],
            }
            for name, step in sorted(observed.items())
        },
        "whole_prover_cost": {
            "status": "scoped-local-result-only",
            "v8r1_evidence_engine_gitlink_commit": cost_engine,
            "current_engine_matches_v8r1": current_engine == cost_engine,
            "independent_review": "design/s31/measurements/WHOLE_PROVER_V8R1_RESULT.md",
            "limits": [
                "held-out evaluator required a post-freeze roster-only repair",
                "no demonstrated transfer to the current engine/compiler stack",
                "no cross-host prediction or tail-latency guarantee",
                "no soundness-equivalent automatic lowering; selection remains disabled",
            ],
        },
    }


def encoded(value: dict[str, object]) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate reviewed matrix snapshot")
    parser.add_argument("--check", action="store_true", help="reject stale snapshot or changed evidence")
    parser.add_argument("--require-admissible", action="store_true",
                        help="fail closed while any published-proof obligation is open")
    args = parser.parse_args(argv)
    if args.write and args.check:
        parser.error("--write and --check are mutually exclusive")
    try:
        report = matrix()
        content = encoded(report)
        if args.check and (not MATRIX.is_file() or MATRIX.read_text() != content):
            raise ValueError("stale PCS/FRI blocker matrix; regenerate and review")
        if args.write:
            MATRIX.parent.mkdir(parents=True, exist_ok=True)
            MATRIX.write_text(content)
    except (OSError, subprocess.CalledProcessError, ValueError, KeyError) as exc:
        parser.error(str(exc))
    print(content, end="")
    return 2 if args.require_admissible and not report["proven_release_admissible"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
