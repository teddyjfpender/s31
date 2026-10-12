#!/usr/bin/env python3
"""Freeze a prospective one-host build/cold/whole-workload holdout."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(HERE.parent / "mixed_cost_v18_topology_transfer"))
import protocol as v18  # noqa: E402

LANGUAGE = ROOT / "design/s31/measurements/language"
FROZEN = LANGUAGE / "mixed-cost-v20-build-cold-holdout-protocol.json"
NAME = "calls6_log14_b8"
CLAIMS = 20
SEED = 202610120215
SCHEDULE_SEED = 202610120216
BASE_COMMIT = "93114dfa53b9f8762d4da20a41b158992ce61de9"
V18_RESULT = LANGUAGE / "mixed-cost-v18-topology-transfer-result.json"
V19_RESULT = LANGUAGE / "mixed-cost-v19-revision-holdout-result.json"


def canonical(value: object) -> bytes:
    return v18.canonical(value)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def lifecycle_forecast(warm_center_ns: float) -> dict:
    """Fixed median of four previously recorded one-host lifecycle observations."""
    old_raw, new_raw = V18_RESULT.read_bytes(), V19_RESULT.read_bytes()
    old, new = v18.v2.parse(old_raw), v18.v2.parse(new_raw)
    if (old_raw != canonical(old) or new_raw != canonical(new) or
            len(old["records"]) != 3 or new["record"]["name"] != "calls6_log13_b8" or
            len(new["record"]["trials"]) != 22):
        raise ValueError("prior lifecycle records differ")
    records = old["records"] + [new["record"]]
    if {record["name"] for record in old["records"]} != set(v18.NAMES):
        raise ValueError("V18 source roster differs")
    def center(key: str) -> float:
        values = []
        for record in records:
            if len(record["trials"]) != 22:
                raise ValueError("prior lifecycle trial count differs")
            values.append(record["build_wall_ns"] if key == "build" else
                          record["trials"][0 if key == "first" else 1][
                              "first_verified_process_wall_ns"])
        return statistics.median(values)
    build, first, repeat = center("build"), center("first"), center("repeat")
    return {
        "prior_result_sha256": {"v18": sha(old_raw), "v19": sha(new_raw)},
        "fit": "componentwise median of V18's three sources and V19's one source; no target observations",
        "build_wall_ns": build,
        "first_post_build_verified_wall_ns": first,
        "same_claim_immediate_repeat_wall_ns": repeat,
        "warm_verified_wall_ns": warm_center_ns,
        "build_plus_22_verified_proofs_sum_ns": build + first + repeat + CLAIMS * warm_center_ns,
    }


def case(index: int) -> tuple[bytes, bytes, bytes]:
    if not 0 <= index <= CLAIMS:
        raise ValueError("outside frozen V20 claim roster")
    source = v18.source(NAME)
    relation = v18.v2.parse(source)
    seed = SEED + index * 101
    words = [(seed * (lane + 53) + lane * lane + 83) % v18.P
             for lane in range(4)]
    assignment = {
        "public_inputs": {relation["inputs"][0]["name"]: words},
        "private_inputs": {},
        "public_outputs": {relation["public_outputs"][0]: v18.output(NAME, words)},
    }
    if (v18.v2.evaluate_relation(v18.v2.flat(relation), assignment) !=
            assignment["public_outputs"]):
        raise ValueError("independent source arithmetic oracle differs")
    statement = v18.v2.statement_from_assignment(relation, assignment)
    v18.v2.changed_result(source, statement)
    return source, canonical(assignment), statement


def historical_pin_sha256(value: dict) -> dict[str, str]:
    """Check each recorded production file against the preregistered base tree."""
    if value.get("current_revision") != BASE_COMMIT:
        raise ValueError("V20 base commit differs from preregistration")
    recorded = value.get("current_pin_sha256")
    if not isinstance(recorded, dict) or set(recorded) != set(v18.PIN_PATHS):
        raise ValueError("V20 historical production pin roster differs")
    for path, digest in recorded.items():
        historical = v18.v2.git("show", f"{BASE_COMMIT}:{path}")
        if sha(historical) != digest:
            raise ValueError(f"V20 historical production pin differs: {path}")
    gitlink = v18.v2.git("rev-parse", f"{BASE_COMMIT}:deps/stwo-zig").decode().strip()
    if value.get("engine_gitlink_commit") != gitlink:
        raise ValueError("V20 historical engine gitlink differs")
    return recorded


def prepare(*, historical: dict | None = None) -> dict:
    old_raw = v18.PROTOCOL.read_bytes()
    old = v18.v2.parse(old_raw)
    model_raw = v18.MODEL.read_bytes()
    if (old_raw != canonical(old) or
            sha(model_raw) != old["v18_model_sha256"] or
            sha(v18.source(NAME)) != old["source_roster"][NAME]["source_sha256"] or
            (v18.SOURCE_DIR / f"{NAME}.json").read_bytes() != v18.source(NAME)):
        raise ValueError("V18 model, source, or protocol identity differs")
    rows = [case(index) for index in range(CLAIMS + 1)]
    assignments = [sha(row[1]) for row in rows]
    statements = [sha(row[2]) for row in rows]
    if (len(set(assignments + statements)) != 2 * (CLAIMS + 1) or
            any(value in old["source_roster"][NAME][kind]
                for kind, values in (("assignment_sha256", assignments),
                                     ("statement_sha256", statements))
                for value in values)):
        raise ValueError("new claim corpus collides with V18")
    names = list(range(1, CLAIMS + 1))
    random.Random(SCHEDULE_SEED).shuffle(names)
    if historical is None:
        pins = v18.v3.pins()
        current_pin_sha256 = {path: sha((ROOT / path).read_bytes())
                              for path in v18.PIN_PATHS if (ROOT / path).is_file()}
    else:
        current_pin_sha256 = historical_pin_sha256(historical)
        # These are provenance fields committed before the native attempt.
        # A full compiler fingerprint replay uses the pinned-base worktree.
        pins = {key: historical[key] for key in
                ("engine_gitlink_commit", "compiler_sha256", "host")}
    return {
        "schema": "s31-mixed-cost-v20-build-cold-holdout-protocol",
        "status": "pre-native-frozen",
        "source": NAME,
        "source_sha256": old["source_roster"][NAME]["source_sha256"],
        "v18_protocol_sha256": sha(old_raw),
        "v18_model_sha256": sha(model_raw),
        "v18_prediction": old["source_roster"][NAME]["prediction"],
        "v18_expected_geometry": old["source_roster"][NAME]["expected_geometry"],
        "v18_expected_calls": old["source_roster"][NAME]["expected_calls"],
        "v18_gates": old["gates"],
        "lifecycle_forecast": lifecycle_forecast(
            old["source_roster"][NAME]["prediction"]["warm_wall_one_draw_quantile_ns"]["0.5"]),
        "engine_gitlink_commit": pins["engine_gitlink_commit"],
        "compiler_sha256": pins["compiler_sha256"],
        "host": pins["host"],
        "source_base_commit": v18.SOURCE_BASE_COMMIT,
        "current_revision": BASE_COMMIT,
        "current_pin_sha256": current_pin_sha256,
        "study_tool_sha256": sha((HERE / "study.py").read_bytes()),
        "lifecycle_tool_sha256": sha((HERE / "lifecycle.py").read_bytes()),
        "audit_tool_sha256": sha((HERE / "audit.py").read_bytes()),
        "claim_seed": SEED,
        "schedule_seed": SCHEDULE_SEED,
        "claim_order": names,
        "assignment_sha256": assignments,
        "statement_sha256": statements,
        "gates": {
            "manifest_exact_geometry_and_calls": True,
            "all_honest_accepted_and_changed_result_rejected": True,
            "wall_median_relative_error_max": 0.35,
            "nonpow_wall_median_relative_error_max": 0.20,
            "proof_median_relative_error_max": 0.10,
            "wall_one_draw_hits_min": 14,
            "proof_interval_hits_min": 16,
            "sample20_wall_median_in_band": True,
            "rss_and_native_stage_relative_error_max": 0.30,
            "build_wall_relative_error_max": 0.25,
            "first_post_build_verified_relative_error_max": 0.40,
            "immediate_repeat_relative_error_max": 0.50,
            "build_plus_22_proofs_relative_error_max": 0.25,
        },
        "warm_score_scope": "V18 source calls6_log14_b8; 20 fresh claims on current compiler; V18 one-host warm prediction",
        "cold_build_scope": "prospective local exploratory point forecasts for one package build, first proof, repeat, and sum of build plus 22 separately measured proof-process durations; no cross-host inference",
        "one_attempt_semantics": "create marker before build with O_EXCL; preserve failure and do not rerun",
    }


def frozen_record() -> tuple[dict, str]:
    raw = FROZEN.read_bytes()
    value = v18.v2.parse(raw)
    if raw != canonical(value) or value != prepare(historical=value):
        raise ValueError("V20 protocol differs from its preregistered historical record")
    if v18.v2.git("show", f"HEAD:{FROZEN.relative_to(ROOT).as_posix()}") != raw:
        raise ValueError("V20 protocol must be committed unchanged")
    return value, sha(raw)


def frozen() -> tuple[dict, str]:
    """Stricter pre-native check: the current checkout must match the freeze."""
    value, digest = frozen_record()
    if value != prepare():
        raise ValueError("current S31 stack differs from V20 pre-native freeze")
    return value, digest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("preview", "freeze", "check", "check-record"))
    action = parser.parse_args().action
    if action == "check-record":
        value, digest = frozen_record()
        raw = FROZEN.read_bytes()
    else:
        value = prepare()
        raw = canonical(value)
        digest = sha(raw)
    if action == "freeze":
        with FROZEN.open("xb") as file:
            file.write(raw)
    if action == "check":
        frozen()
    print(json.dumps({"protocol_sha256": digest,
                      "source_sha256": value["source_sha256"],
                      "current_revision": value["current_revision"],
                      "v18_protocol_sha256": value["v18_protocol_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
