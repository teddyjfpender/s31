"""Strict, non-overlapping timing projections for mixed prover phase reports.

The reports contain nested intervals. Never add PCS to the native interval or
FRI PoW to PCS: doing so counts the same time twice.
"""

from __future__ import annotations

import statistics

STAGES = ("profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
          "witness_compile_ns", "native_prove_including_setup_ns",
          "envelope_and_serialization_ns")


def exact_nonnegative(value: object) -> bool:
    return type(value) is int and value >= 0


def project(stage: dict, phase: dict, prover_wall_ns: int,
            verifier_wall_ns: int) -> dict[str, int]:
    """Validate native reports and return a disjoint process-wall partition."""
    if not (type(prover_wall_ns) is int and prover_wall_ns > 0 and
            type(verifier_wall_ns) is int and verifier_wall_ns > 0):
        raise ValueError("positive process walls required")
    parts = stage.get("stages_ns")
    if (stage.get("schema") != "s31-mixed-general-prover-stages-v1" or
            type(parts) is not dict or set(parts) != {*STAGES, "package_total_ns"} or
            any(not exact_nonnegative(value) for value in parts.values()) or
            parts["package_total_ns"] != sum(parts[key] for key in STAGES) or
            parts["package_total_ns"] > prover_wall_ns):
        raise ValueError("invalid package stage report")
    native = parts["native_prove_including_setup_ns"]
    if native == 0 or phase.get("schema") != "s31-mixed-native-phase-v1" or \
            any(phase.get(key) != stage.get(key) for key in
                ("source_sha256", "circuit_identity_sha256")) or \
            phase.get("native_prove_including_setup_ns") != native:
        raise ValueError("native phase identity or interval differs")
    keys = ("prove_body_ns", "interaction_pow_ns", "pcs_prove_ns", "fri_pow_ns",
            "pcs_without_fri_pow_ns", "native_without_reported_pow_ns")
    if any(not exact_nonnegative(phase.get(key)) for key in keys):
        raise ValueError("invalid native phase duration")
    body, interaction, pcs, fri = (phase[key] for key in
                                    ("prove_body_ns", "interaction_pow_ns",
                                     "pcs_prove_ns", "fri_pow_ns"))
    if (body == 0 or interaction == 0 or fri == 0 or
            not fri <= pcs <= body <= native or interaction + pcs > body or
            phase["pcs_without_fri_pow_ns"] != pcs - fri or
            phase["native_without_reported_pow_ns"] != native - interaction - fri):
        raise ValueError("nested native phase accounting inconsistent")
    # Disjoint slices sum to prover wall; verifier is separately timed.
    projected = {
        "prover_unattributed_process_wall_ns": prover_wall_ns - parts["package_total_ns"],
        "package_non_native_ns": parts["package_total_ns"] - native,
        "native_outer_minus_body_ns": native - body,
        "body_other_than_pow_or_pcs_ns": body - interaction - pcs,
        "interaction_pow_ns": interaction,
        "pcs_without_fri_pow_ns": pcs - fri,
        "fri_pow_ns": fri,
        "external_verifier_process_wall_ns": verifier_wall_ns,
    }
    if sum(projected.values()) != prover_wall_ns + verifier_wall_ns:
        raise ValueError("process wall partition failed")
    return projected


def cold_warm(trials: list[dict]) -> dict:
    """First post-build process versus later fresh processes; no causal claim."""
    if len(trials) < 3 or [trial.get("ordinal") for trial in trials] != list(range(len(trials))):
        raise ValueError("ordered trials required")
    if trials[0].get("claim_index") != 0 or trials[1].get("claim_index") != 0:
        raise ValueError("first two processes must repeat the same claim")
    fields = ("first_verified_process_wall_ns", "prover_process_wall_ns",
              "external_verifier_process_wall_ns", "prover_unattributed_process_wall_ns",
              "native_prove_including_setup_ns", "native_outer_minus_body_ns",
              "interaction_pow_ns", "pcs_without_fri_pow_ns", "fri_pow_ns")
    result = {"cold_ordinal": 0, "same_claim_warm_ordinal": 1,
              "warm_ordinals": list(range(1, len(trials)))}
    for field in fields:
        values = [trial[field] for trial in trials]
        if any(not exact_nonnegative(value) for value in values):
            raise ValueError(f"invalid trial metric: {field}")
        result[field] = {"first": values[0], "same_claim_repeat": values[1],
                         "warm_median": statistics.median(values[1:]),
                         "first_minus_same_claim_repeat": values[0] - values[1]}
    return result
