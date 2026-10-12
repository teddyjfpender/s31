#!/usr/bin/env python3
"""Freeze a same-source, new-claim transfer test across S31 revisions."""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(HERE.parent / "mixed_cost_v18_topology_transfer"))
import protocol as v18  # noqa: E402

LANGUAGE = ROOT / "design/s31/measurements/language"
FROZEN = LANGUAGE / "mixed-cost-v19-revision-holdout-protocol.json"
NAME = "calls6_log13_b8"
CLAIMS = 20
SEED = 202610120019
SCHEDULE_SEED = 202610120020
BASE_COMMIT = "aa15b22ca817485599cda160b0e50ea5bc35f3cf"


def canonical(value: object) -> bytes:
    return v18.canonical(value)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def case(index: int) -> tuple[bytes, bytes, bytes]:
    if not 0 <= index <= CLAIMS:
        raise ValueError("outside frozen V19 claim roster")
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
        raise ValueError("V19 base commit differs from preregistration")
    recorded = value.get("current_pin_sha256")
    if not isinstance(recorded, dict) or set(recorded) != set(v18.PIN_PATHS):
        raise ValueError("V19 historical production pin roster differs")
    for path, digest in recorded.items():
        historical = v18.v2.git("show", f"{BASE_COMMIT}:{path}")
        if sha(historical) != digest:
            raise ValueError(f"V19 historical production pin differs: {path}")
    gitlink = v18.v2.git("rev-parse", f"{BASE_COMMIT}:deps/stwo-zig").decode().strip()
    if value.get("engine_gitlink_commit") != gitlink:
        raise ValueError("V19 historical engine gitlink differs")
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
        "schema": "s31-mixed-cost-v19-revision-holdout-protocol",
        "status": "pre-native-frozen",
        "source": NAME,
        "source_sha256": old["source_roster"][NAME]["source_sha256"],
        "v18_protocol_sha256": sha(old_raw),
        "v18_model_sha256": sha(model_raw),
        "v18_prediction": old["source_roster"][NAME]["prediction"],
        "v18_expected_geometry": old["source_roster"][NAME]["expected_geometry"],
        "v18_expected_calls": old["source_roster"][NAME]["expected_calls"],
        "v18_gates": old["gates"],
        "engine_gitlink_commit": pins["engine_gitlink_commit"],
        "compiler_sha256": pins["compiler_sha256"],
        "host": pins["host"],
        "source_base_commit": v18.SOURCE_BASE_COMMIT,
        "current_revision": BASE_COMMIT,
        "current_pin_sha256": current_pin_sha256,
        "study_tool_sha256": sha((HERE / "study.py").read_bytes()),
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
        },
        "warm_score_scope": "20 fresh claims; fresh prover and verifier processes; V18 one-host frozen prediction; unchanged source but changed compiler revision",
        "cold_build_scope": "descriptive one package build, first claim and immediate repeat; no cold or build accuracy gate",
        "one_attempt_semantics": "create marker before build with O_EXCL; preserve failure and do not rerun",
    }


def frozen_record() -> tuple[dict, str]:
    raw = FROZEN.read_bytes()
    value = v18.v2.parse(raw)
    if raw != canonical(value) or value != prepare(historical=value):
        raise ValueError("V19 protocol differs from its preregistered historical record")
    if v18.v2.git("show", f"HEAD:{FROZEN.relative_to(ROOT).as_posix()}") != raw:
        raise ValueError("V19 protocol must be committed unchanged")
    return value, sha(raw)


def frozen() -> tuple[dict, str]:
    """Stricter pre-native check: the current checkout must match the freeze."""
    value, digest = frozen_record()
    if value != prepare():
        raise ValueError("current S31 stack differs from V19 pre-native freeze")
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
