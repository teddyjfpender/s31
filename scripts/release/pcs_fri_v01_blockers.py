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
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.release.release_candidate import AUDIT_CASES
from scripts.release.s31_v01_audit import CASES
from scripts.release.pcs_fri_degree_correction import audit as audit_degree_correction
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
        "partial_evidence": ["scripts/release/pcs_fri_proven_preflight.py", "scripts/release/pcs_fri_package_geometry.py", "scripts/release/pcs_fri_gate_final_domain.py", "scripts/release/pcs_fri_gate_binary_rebuild.py", "design/s31/security/PCS_FRI_PACKAGE_GEOMETRY.md", "design/s31/security/PCS_FRI_GATE_FINAL_DOMAIN.md", "design/s31/security/PCS_FRI_GATE_BINARY_REBUILD.md", "design/s31/security/evidence/gate-native-fridomain-accepted-proof-2026-10-14.json", "formal/s31/proof-inventory.json"],
        "missing_discharge": "one fold-step-1 Gate diagnostic can join an accepted proof, reproducibly rebuilt verifier image and conditional native FRI D, but this is not a Zig semantics proof or the paper's full original-plus-quotient domain; identify theorem N/D, C, d, L, m, rate and list bound, complete other package geometry and check all finite-domain, degree and small-table preconditions",
    },
    {
        "id": "P02_AIR_AND_INTERACTION_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 7 and Stwo flat-AIR IOPP: committed columns, constraints, logUp multiplicities and composition must realize the theorem relation",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/proof-inventory.json", "formal/s31/S31/Gadgets/Air/GatePublicInteraction.lean", "formal/s31/S31/Gadgets/Air/NativeGateFinalizerBridge.lean", "formal/s31/tests/native_gate_finalizer_refinement.zig", "formal/s31/tests/run_native_gate_finalizer_refinement.sh", "scripts/release/pcs_fri_gate_interaction.py", "src/frontends/s31/python/package/gate_component_roster.py", "design/s31/security/PCS_FRI_GATE_INTERACTION.md", "design/s31/security/MIXED_N1_N8_CONDITIONAL_ERROR_LEDGER_2026-10-12.md"],
        "missing_discharge": "the Gate profile has source-pinned relation-use caps, eleven-claim/public-output closure, and a fixed-sample finalizer-to-eleven-residual refinement with at most ten cancellation coefficients per bad row. Accepted-proof binary provenance, complete source/compiler-to-native AIR correspondence, committed-column and OODS sample origin, composition randomness, and program-wide lookup/interaction soundness remain open",
    },
    {
        "id": "P03_LIFTED_MULTI_DOMAIN_PCS_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Stwo multi-domain circle FRI and batch evaluation: all native lifted roots and cross-domain openings realize one cross-domain oracle relation",
        "published_anchor": STWO,
        "partial_evidence": ["scripts/s31_formal_lib/pcs_fri_projection.py", "formal/s31/S31/Gadgets/PcsFri/MerkleOpening.lean", "formal/s31/S31/Gadgets/PcsFri/LayerAcceptance.lean", "src/frontends/s31/runtime/pcs_lifted_capture_admission.zig", "formal/s31/tests/pcs_fri_lifted_capture_native.zig", "design/s31/security/PCS_FRI_GATE_LIFTED_PROJECTION.md"],
        "missing_discharge": "the accepted-capture gate replays four roots and sampled lifted-column consistency, but a semantic Zig-to-model extraction, complete committed-oracle ownership, all cross-domain quotient openings, collision reduction and proximity theorem remain open",
    },
    {
        "id": "P04_FRI_ROUND_AND_TERMINAL_REFINEMENT",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 6: committed round words, independent challenge order, every fold equation and terminal degree check match Protocol 2",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/FoldAlgebra.lean", "formal/s31/S31/Gadgets/PcsFri/LayerAcceptance.lean", "formal/s31/S31/Gadgets/PcsFri/TerminalBasisRefinement.lean", "formal/s31/tests/pcs_fri_raw_refinement_native.zig", "design/s31/security/PCS_FRI_OPERATIONAL_TERMINAL_REFINEMENT.md", "src/frontends/s31/sha/verification/pcs_capture_admission.zig"],
        "missing_discharge": "compose local fold and acceptance models with the complete native commitment, opening and terminal control flow",
    },
    {
        "id": "P05_OODS_DEEP_DEGREE_CORRECTION",
        "gap_kind": "unproven_native_refinement",
        "published_requirement": "Circle STARKs Theorem 7 and Stwo batch-OOD theorem: sampled values, DEEP quotients and degree correction imply the claimed polynomial identity",
        "published_anchor": STWO,
        "partial_evidence": ["scripts/s31_formal_lib/pcs_fri_order.py", "scripts/s31_formal_lib/pcs_fri_quotient_algebra.py", "scripts/release/pcs_fri_degree_correction.py", "scripts/release/pcs_fri_cas05_source_profile.py", "formal/s31/S31/Gadgets/PcsFri/DeepQuotientAlgebra.lean", "formal/s31/S31/Gadgets/PcsFri/DegreeCorrectionGap.lean", "formal/s31/S31/Gadgets/PcsFri/PairedRosterDegreeCorrection.lean", "formal/s31/S31/Gadgets/PcsFri/OodAcceptedSupport.lean", "formal/s31/tests/pcs_fri_quotient_degree_gap_native.zig", "formal/s31/tests/run_pcs_fri_quotient_degree_gap_native.sh", "formal/s31/S31/Gadgets/PcsFri/Gate16FourierRows.lean", "formal/s31/tests/pcs_fri_gate16_fourier_rows_native.zig", "formal/s31/tests/run_pcs_fri_gate16_fourier_rows_native.sh", "formal/s31/tests/pcs_fri_gate16_four_slot_fft_native.zig", "formal/s31/tests/run_pcs_fri_gate16_four_slot_fft_native.sh", "design/s31/security/PCS_FRI_GATE16_FOURIER_ROWS.md", "formal/s31/S31/Gadgets/PcsFri/GateFourBlockOwnQuotient.lean", "formal/s31/tests/pcs_fri_gate_four_block_own_quotient_native.zig", "formal/s31/tests/run_pcs_fri_gate_four_block_own_quotient_native.sh", "design/s31/security/PCS_FRI_GATE_FOUR_BLOCK_OWN_QUOTIENT.md", "formal/s31/S31/Gadgets/PcsFri/GateQuotientOnlyGap.lean", "formal/s31/tests/pcs_fri_gate_quotient_only_gap_native.zig", "formal/s31/tests/run_pcs_fri_gate_quotient_only_gap_native.sh", "design/s31/security/PCS_FRI_GATE_QUOTIENT_ONLY_GAP.md", "design/s31/security/PCS_FRI_DEGREE_CORRECTION_GAP.md", "design/s31/security/PCS_FRI_NATIVE_DEGREE_WITNESS.md", "design/s31/security/PCS_FRI_CAS05_PRODUCTION_MIGRATION.md", "design/s31/security/PCS_FRI_CAS05_P05_DISCHARGE_CHECKLIST.md", "deps/stwo-zig/src/prover/pcs/scheme.zig", "deps/stwo-zig/src/core/pcs/verifier.zig", "deps/stwo-zig/src/core/pcs/quotients/row_evaluation.zig", "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig", "deps/stwo-zig/src/core/constraints.zig", "deps/stwo-zig/src/core/fields/mod.zig", "deps/stwo-zig/src/core/fields/cm31.zig", "src/frontends/s31/sha/verification/pcs_capture_admission.zig"],
        "missing_discharge": "production still checks only one accumulated DEEP quotient with FRI, so the published degree-corrected theorem's original-word degree-test premise is absent. Experimental CAS05 pairs original and own-quotient words but lacks production dispatch and the exact two-point circle-basis, derived-oracle, query, OOD and BCS theorem join. Implement and refine the full production ensemble or prove an alternative quotient-only theorem with exact parameters; also prove Zig row-quotient semantics, committed sampled/opened value ownership and OODS checks",
    },
    {
        "id": "P06_MERKLE_BINDING_AND_DECODER",
        "gap_kind": "unproven_crypto_and_native_refinement",
        "published_requirement": "BCS oracle commitments authenticate precisely the queried rows at the committed roots with a quantitative collision bound",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/MerkleOpening.lean", "formal/s31/S31/Gadgets/PcsFri/MerkleBytePreimage.lean", "formal/s31/S31/Gadgets/PcsFri/FriQm31BytePreimage.lean", "formal/s31/tests/pcs_fri_merkle_byte_preimage_native.zig", "formal/s31/tests/run_pcs_fri_merkle_byte_preimage_native.sh", "scripts/s31_formal_lib/pcs_fri_merkle_byte_preimage.py", "scripts/s31_formal_lib/pcs_fri_merkle_admission.py", "src/frontends/s31/runtime/fri_merkle_admission.zig", "design/s31/security/PCS_FRI_MERKLE_BYTE_PREIMAGE.md", "formal/s31/S31/Gadgets/PcsFri/MultiproofDecoder.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofAllHeights.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofSortedFrontier.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofCallerOrder.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofRawQueries.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofCommittedColumns.lean", "formal/s31/S31/Gadgets/PcsFri/MultiproofCompactTiles.lean", "formal/s31/S31/Gadgets/PcsFri/PairedBatchXdm04AuditLoop.lean", "scripts/s31_formal_lib/pcs_fri_leaf_encoding.py", "scripts/s31_formal_lib/pcs_fri_lifted_capture.py", "scripts/s31_formal_lib/pcs_fri_prover_origin.py", "scripts/s31_formal_lib/sha_release_capture.py", "scripts/release/pcs_fri_xdm04_audit_loop.py", "src/frontends/s31/runtime/pcs_lifted_capture_admission.zig", "formal/s31/tests/lib/pcs_merkle_collision_reduction.zig", "formal/s31/tests/lib/pcs_xdm04_mixed_certificate.zig", "formal/s31/tests/pcs_fri_native_collision_reduction.zig", "formal/s31/tests/run_pcs_fri_native_collision_reduction.sh", "formal/s31/tests/pcs_fri_decoder_general_native.zig", "formal/s31/tests/run_pcs_fri_decoder_refinement_native.sh", "formal/s31/tests/pcs_fri_prover_column_origin_native.zig", "formal/s31/tests/run_pcs_fri_prover_column_origin_native.sh", "formal/s31/tests/pcs_fri_compact_column_origin_native.zig", "formal/s31/tests/run_pcs_fri_compact_column_origin_native.sh", "formal/s31/tests/audit/private_main_lde_openings.py", "formal/s31/S31/Gadgets/Functional/Correspondence/PrivateMainLdeOpenings.md", "design/s31/security/PCS_FRI_MULTIPROOF_DECODER_REFINEMENT.md", "design/s31/security/PCS_FRI_COMMITTED_COLUMN_ORIGIN.md", "design/s31/security/PCS_FRI_NATIVE_MERKLE_COLLISION_REDUCTION.md"],
        "missing_discharge": "the Lean audit-loop success theorem yields exact captured steps and path recurrence, but its success has no Zig operational-semantics refinement or installed CAS05 verifier call. General Zig-to-Lean sort/dedup/row-assembly/byte-hash semantics, all-input native interpolation/block evaluation and retained-column ownership (including cached and backend-specific cases), installed-binary correspondence, and a quantitative collision/binding bound for the exact plain BLAKE2s layout remain open; the parametric Lean tile projection/parent theorem and finite native prover/oracle differentials, now including one private Gate proof's 66×12 main-tree LDE openings, grouped block reloads, post-release openings and one log-20 pruned shape, cover only their stated abstract and sampled boundaries",
    },
    {
        "id": "P07_FIAT_SHAMIR_AND_POW_BUDGET",
        "gap_kind": "unproven_crypto_and_budget_reduction",
        "published_requirement": "Stwo NIROP/BCS theorem: bound adversary hash budget T, rounds R, hash collision term and exact native grinding and transcript schedule",
        "published_anchor": STWO,
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/QueryAndTranscript.lean", "formal/s31/S31/Gadgets/PcsFri/BcsTranscriptEpoch.lean", "formal/s31/S31/Gadgets/PcsFri/PowM31Predicate.lean", "formal/s31/S31/Gadgets/PcsFri/BiasedLookupPair.lean", "scripts/s31_formal_lib/pcs_fri_order.py", "scripts/s31_formal_lib/pcs_fri_challenge_custody.py", "scripts/s31_formal_lib/pcs_fri_query_epoch.py", "scripts/s31_formal_lib/pcs_fri_bcs_transcript.py", "scripts/s31_formal_lib/pcs_fri_pow_m31_predicate.py", "scripts/tests/test_pcs_fri_pow_m31_predicate.py", "scripts/release/pcs_fri_lookup_challenge_bias.py", "scripts/tests/test_pcs_fri_lookup_challenge_bias.py", "formal/s31/tests/pcs_fri_bcs_transcript_native.zig", "formal/s31/tests/pcs_fri_bcs_transcript.json", "formal/s31/tests/pcs_fri_pow_m31_predicate_native.zig", "formal/s31/tests/run_pcs_fri_pow_m31_predicate_native.sh", "scripts/release/pcs_fri_gate_error_ledger.py", "design/s31/security/PCS_FRI_GATE_ERROR_LEDGER.md", "design/s31/security/PCS_FRI_BCS_TRANSCRIPT_REFINEMENT.md", "design/s31/security/PCS_FRI_POW_M31_PREDICATE.md", "design/s31/security/PCS_FRI_LOOKUP_PAIR_BIAS.md", "scripts/release/pcs_fri_ood_seed_geometry.py", "scripts/tests/test_pcs_fri_ood_seed_geometry.py", "design/s31/security/PCS_FRI_OOD_SEED_GEOMETRY.md"],
        "missing_discharge": "ROM/BCS reduction for exact M31-reduced Blake2s and unframed root/field absorption, total hash-work/round/collision budget and joint two-stage grinding analysis beyond the proved one-try M31 counts and fixed-prefix lookup-pair density ratio, plus a full selected-verifier Zig control-flow proof; scoped native/Python Gate fixtures and source guards establish deterministic bytes and order only",
    },
    {
        "id": "P08_QUERY_SET_AND_RAW_WORD_MODEL",
        "gap_kind": "unproven_native_and_random_oracle_refinement",
        "published_requirement": "Circle STARKs Theorem 6 query term assumes a fixed good set and independent uniform positions; native M31 masking must be accounted for",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["formal/s31/S31/Gadgets/PcsFri/M31MaskedQuery.lean", "formal/s31/S31/Gadgets/PcsFri/M31WordReduction.lean", "formal/s31/S31/Gadgets/PcsFri/NativeQueryBatch.lean", "formal/s31/tests/pcs_fri_native_query_batch.zig", "formal/s31/tests/run_pcs_fri_native_query_batch.sh", "scripts/s31_formal_lib/pcs_fri_m31_query.py", "scripts/tests/test_pcs_fri_m31_query.py", "design/s31/security/PCS_FRI_M31_MASKED_QUERY_DISTRIBUTION.md"],
        "missing_discharge": "prove all-input compiled Zig-to-Lean sampler refinement, derive a fixed good set from the native committed oracle before each draw, and connect ideal raw-word independence to the native channel",
    },
    {
        "id": "P09_COMPLETE_ERROR_LEDGER",
        "gap_kind": "uninstantiated_theorem_error_ledger",
        "published_requirement": "Circle STARKs Theorems 6/7 and Stwo NIROP: sum every justified commitment, AIR, OODS, FRI, Merkle and Fiat-Shamir term before comparing with target bits",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["scripts/release/pcs_fri_proven_preflight.py", "scripts/release/pcs_fri_gate_error_ledger.py", "scripts/release/pcs_fri_stwo_udr.py", "formal/s31/S31/Gadgets/PcsFri/StwoUDRFeasibility.lean", "design/s31/security/PCS_FRI_PUBLISHED_BOUND_AUDIT.md", "design/s31/security/PCS_FRI_GATE_ERROR_LEDGER.md", "design/s31/security/PCS_FRI_STWO_UDR_FEASIBILITY.md", "scripts/release/pcs_fri_ood_seed_geometry.py", "design/s31/security/PCS_FRI_OOD_SEED_GEOMETRY.md"],
        "missing_discharge": "the exact unique-decoding paper-scenario ledger has all quoted IOPP, FRI and BCS expressions, but instantiate them with theorem-identified native package parameters and prove the native protocol, T, R, Merkle/collision and ROM reductions; every native theorem term remains null",
    },
    {
        "id": "P10_GROUPED_FOLD_SCHEDULE",
        "gap_kind": "unmatched_protocol_schedule",
        "published_requirement": "A grouped four-fold native round needs its own reduction to the paper's single-fold challenge schedule or a theorem covering that schedule",
        "published_anchor": CIRCLE + "#appendix-B",
        "partial_evidence": ["deps/stwo-zig/src/core/fri/config.zig", "deps/stwo-zig/src/core/fri.zig", "deps/stwo-zig/src/core/fri/folding.zig", "scripts/s31_formal_lib/pcs_fri_fold.py", "scripts/s31_formal_lib/pcs_fri_challenge_custody.py", "formal/s31/S31/Gadgets/PcsFri/GroupedFoldSchedule.lean", "design/s31/security/PCS_FRI_GROUPED_FOLD_OBSTRUCTION_2026-10-13.md"],
        "missing_discharge": "prove a grouped-round correlated-agreement and commitment-error bound for one alpha and powers alpha^(2^j), including circle-to-line insertion, adaptive group commitments and exact native-to-theorem refinement; a four-fresh-challenge reduction is invalid",
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


def ungrinded_udr_query_necessity(blowup_log: int, raw_queries: int,
                                  target_bits: int) -> dict[str, object]:
    """Paper UDR query-expression floor, never an actual-error lower bound."""
    if not 1 <= blowup_log <= 30 or not 1 <= raw_queries <= 100000 or not 1 <= target_bits <= 256:
        raise ValueError("invalid UDR query-necessity parameters")
    blowup = 1 << blowup_log
    # theta < (1-rho)/2 implies alpha=1-theta > (1+rho)/2.
    excluded_alpha = Fraction(blowup + 1, 2 * blowup)
    target = Fraction(1, 1 << target_bits)
    boundary_term = excluded_alpha ** raw_queries
    needed = 1
    while excluded_alpha ** needed > target:
        needed += 1
    return {
        "scope": "hypothetical single-fold S-two unique-decoding theorem; zero proved grinding credit",
        "excluded_alpha_boundary": f"{excluded_alpha.numerator}/{excluded_alpha.denominator}",
        "raw_queries": raw_queries,
        "query_expression_at_excluded_boundary": f"{boundary_term.numerator}/{boundary_term.denominator}",
        "necessary_raw_queries_at_boundary_for_target": needed,
        "published_ungrinded_work_factor_expression_cannot_certify_target_for_any_T": boundary_term > target,
        "interpretation": "necessary arithmetic for the quoted paper expression, not a bound on native attack success",
    }


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
    degree_correction = audit_degree_correction(root)
    if (query_epoch["engine_gitlink_commit"] != current_engine or
            query_epoch["hash_draws"] != 9 or
            not query_epoch["native_blake2s_counter_overflow_fail_closed"]):
        raise ValueError("v0.1 query epoch source or engine binding changed")
    if (degree_correction["engine_gitlink_commit"] != current_engine or
            degree_correction["native_gate_epoch_trace_scope"] != "legacy_direct_profile_only" or
            degree_correction["raw_gate_epoch_trace_evidenced"] is not False or
            degree_correction["p05_discharged"] is not False or
            degree_correction["published_degree_corrected_nonquotient_premise_met"] is not False or
            degree_correction["proposed_degree_corrected_profile"]["selector_installed"] is not False or
            degree_correction["proposed_degree_corrected_profile"]["proof_admissible"] is not False):
        raise ValueError("v0.1 native degree-correction theorem status changed; review blocker matrix")
    old_cost = json.loads((root / "design/s31/measurements/language/whole-prover-cost-v8r1.json").read_text())
    cost_engine = old_cost["engine_gitlink_commit"]
    return {
        "schema": "s31-pcs-fri-v01-blockers-v1",
        "release": "v0.1.0",
        "status": "blocked",
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "security_target": {
            "metric": "paper_work_factor_epsilon_over_T",
            "target_bits": 96,
            "adversary_hash_query_budget_T": 1 << 64,
            "status": "target_metric_and_T_selected; native_bound_open",
            "paper_arithmetic": "scripts/release/pcs_fri_stwo_udr.py",
            "single_fold_ungrinded_query_necessity": ungrinded_udr_query_necessity(
                NOMINAL_FRI["log_blowup_factor"], NOMINAL_FRI["raw_queries"], 96),
        },
        "engine_gitlink_commit": current_engine,
        "source_visible_nominal_fri": {
            **NOMINAL_FRI,
            "fold_step_by_profile": dict(sorted(observed.items())),
            "source_paths": list(FRI_CONFIG_SOURCES),
            "interpretation": "source-pinned nominal configuration; not a proven security level",
        },
        "proof_targets": [CIRCLE, STWO],
        "query_epoch": query_epoch,
        "degree_correction": degree_correction,
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
