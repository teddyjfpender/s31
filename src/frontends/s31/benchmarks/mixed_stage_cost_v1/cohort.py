"""Native-free source, witness, claim, and split inventory for mixed cost v1.

This cohort is distinct from the completed paired-record v2 timing corpus.
Its source names and assignment seed were declared before its native phase.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/paired_record_v2"))
sys.path.insert(0, str(HERE))  # local protocol/model names must win over paired-study modules

from abi.binding_v2 import binding_digest, statement_from_assignment  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import parse_source_json  # noqa: E402
from design import canonical, flat, sha, source as paired_source  # noqa: E402

DESIGN_PATH = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-prospective.json"
P = (1 << 31) - 1


def design() -> dict:
    value = json.loads(DESIGN_PATH.read_bytes())
    if (value.get("schema") != "s31-mixed-stage-cost-v1-prospective" or
            value.get("status") != "design-only-no-native-measurements" or
            value.get("source_template") !=
                "src/frontends/s31/examples/boundary/record_mixed1.s31.json" or
            value.get("source_name_prefix") != "mixed_stage_cost_v1_n" or
            value.get("train_call_counts") != [1, 3, 5, 7] or
            value.get("heldout_call_counts") != [2, 4, 6, 8] or
            value.get("assignments_per_call_count") != 100 or
            value.get("assignment_seed") != 2026101101 or
            value.get("build_mode") != "ReleaseFast" or
            value.get("lowering") != "direct-mixed-general" or
            value.get("minimum_available_disk_bytes_before_native_phase") != 8 * 1024**3 or
            value.get("minimum_available_disk_bytes_at_phase_start") != 12 * 1024**3 or
            value.get("prior_study_data_allowed_in_fit") is not False or
            value.get("automatic_lowering_selection_enabled") is not False or
            value.get("speedup_claim_enabled") is not False or
            set(value.get("model_features", {})) != {
                "profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
                "witness_compile_ns", "native_prove_including_setup_ns",
                "envelope_and_serialization_ns", "prover_process_residual_ns",
                "external_verifier_process_wall_ns", "proof_bytes"} or
            any(kind != ("constant" if field in
                 ("prover_process_residual_ns", "external_verifier_process_wall_ns")
                 else "call_count") for field, kind in value["model_features"].items()) or
            value.get("accuracy_gate") != {
                "minimum_heldout_programs": 4,
                "whole_wall_program_median_p90_relative_error_max": 0.25,
                "whole_wall_program_median_max_relative_error_max": 0.35,
                "whole_wall_trial_interval_coverage_min": 0.80,
                "whole_wall_median_interval_upper_to_measured_median_max": 8.0,
                "proof_bytes_program_median_p90_relative_error_max": 0.10,
                "proof_bytes_trial_interval_coverage_min": 0.80,
                "proof_bytes_median_interval_upper_to_measured_median_max": 1.5,
                "native_opaque_program_median_p90_relative_error_max": 0.30}):
        raise ValueError("prospective mixed stage design differs from declared v1")
    if sorted(value["train_call_counts"] + value["heldout_call_counts"]) != list(range(1, 9)):
        raise ValueError("mixed stage roster is not exactly N=1..8")
    return value


def source(count: int, cfg: dict) -> bytes:
    relation = parse_source_json(paired_source(count, cfg))
    relation["name"] = f"{cfg['source_name_prefix']}{count}"
    binding_digest(flat(relation), relation["public_abi"])
    return canonical(relation)


def case(count: int, index: int, cfg: dict) -> tuple[bytes, bytes, bytes]:
    if count not in range(1, 9) or not 0 <= index < cfg["assignments_per_call_count"]:
        raise ValueError("mixed stage case is outside the prospective roster")
    source_bytes = source(count, cfg)
    relation = parse_source_json(source_bytes)
    seed = cfg["assignment_seed"] + count * 100_000 + index * 17
    words = [(seed * (lane + 11) + lane * lane + 3) % P for lane in range(4)]
    output = words[:]
    for call in range(count):
        for _ in range(16):
            output = [(value * value + 13 + call) % P for value in output]
    output = [(value + start) % P for value, start in zip(output, words)]
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output}}
    if evaluate_relation(flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent relation oracle disagrees with mixed stage recurrence")
    typed = statement_from_assignment(relation, assignment)
    return source_bytes, canonical(assignment), typed


def inventory(cfg: dict) -> dict:
    result: dict[str, dict] = {}
    seen_sources, seen_assignments, seen_claims = set(), set(), set()
    for split, counts in (("train", cfg["train_call_counts"]),
                          ("heldout", cfg["heldout_call_counts"])):
        result[split] = {}
        for count in counts:
            rows = [case(count, index, cfg) for index in
                    range(cfg["assignments_per_call_count"])]
            source_hash = sha(rows[0][0])
            assignment_hashes = [sha(row[1]) for row in rows]
            claim_hashes = [sha(row[2]) for row in rows]
            if (source_hash in seen_sources or
                    len(set(assignment_hashes) | seen_assignments) !=
                        len(assignment_hashes) + len(seen_assignments) or
                    len(set(claim_hashes) | seen_claims) !=
                        len(claim_hashes) + len(seen_claims) or
                    any(row[0] != rows[0][0] for row in rows)):
                raise ValueError("prospective source, assignment or claim reused")
            seen_sources.add(source_hash)
            seen_assignments.update(assignment_hashes)
            seen_claims.update(claim_hashes)
            result[split][str(count)] = {
                "source_sha256": source_hash,
                "assignment_sha256": assignment_hashes,
                "typed_statement_sha256": claim_hashes,
                "call_count": count,
                "repeat_rounds": 16,
                "chip_slots": 1 + 2 * count,
            }
    return result


if __name__ == "__main__":
    cfg = design()
    rows = inventory(cfg)
    print(json.dumps({"schema": "s31-mixed-stage-cost-v1-inventory-preview",
                      "inventory_sha256": sha(canonical(rows)),
                      "source_count": 8,
                      "assignment_count": 8 * cfg["assignments_per_call_count"]},
                     sort_keys=True))
