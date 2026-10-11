#!/usr/bin/env python3
"""Post-freeze V8r1 roster repair; never an unqualified prospective result.

The frozen V8r1 evaluator imports the V3 checker. For validation only, V3
assumes quotient-only outputs at every small signed width, although V8r1's
pinned inventory specifies div/rem below 128 bits. This wrapper changes only
the split label in a *temporary checker view* so the unchanged V3 checker
accepts exactly the pinned V8r1 validation roster. It passes the original
case objects, trials, model, prediction functions, and gates through intact.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
BENCH = ROOT / "src/frontends/s31/benchmarks"
sys.path[:0] = [str(BENCH), str(BENCH / "cost"), str(ROOT / "src/frontends/s31/python")]

import whole_prover_predictor_v3 as legacy
import whole_prover_predictor_v8r1 as predictor
import publish_whole_prover_cost_v8r1 as publisher
import replay_portable_v8r1 as portable_replay

FAILURE = ROOT / "design/s31/measurements/language/whole-prover-cost-v8r1-eval-failure.json"
EXPECTED_MISSING = {f"signed_quotient_{width}" for width in (8, 16, 32, 64)}
EXPECTED_EXTRA = {f"signed_div_rem_{width}" for width in (8, 16, 32, 64)}
OriginalChecker = Callable[..., list[dict]]


def sha_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_cases_roster_bridge(
    original: OriginalChecker, corpus: dict, split: str, protocol: dict, **kwargs
) -> list[dict]:
    if split != "validation":
        return original(corpus, split, protocol, **kwargs)
    if corpus.get("split") != "validation" or not isinstance(corpus.get("cases"), dict):
        raise ValueError("repair requires the original validation corpus")
    spec = protocol["splits"]["validation"]
    if (spec.get("fixed_width_result") != "div_rem_below_128" or
        spec.get("signed_128_result") != "remainder" or
        spec.get("signed_128_output") != "remainder"):
        raise ValueError("repair requires the exact frozen V8r1 signed result contract")
    pinned = set(protocol["inventory"]["validation"])
    if set(corpus["cases"]) != pinned:
        raise ValueError("repair requires the exact frozen validation inventory")
    original_expectation = legacy.expected_names("validation", protocol)
    if (original_expectation - pinned != EXPECTED_MISSING or
        pinned - original_expectation != EXPECTED_EXTRA):
        raise ValueError("repair is not applicable to this roster mismatch")

    # V3's only split-specific branch in checked_cases is expected_names:
    # 'train' selects div/rem below 128. The 128-bit override stays remainder.
    checker_corpus = {**corpus, "split": "train"}
    checker_protocol = {**protocol, "splits": {**protocol["splits"], "train": spec}}
    records = original(checker_corpus, "train", checker_protocol, **kwargs)
    if {record["name"] for record in records} != pinned or any(
        record["case"] is not corpus["cases"][record["name"]] for record in records
    ):
        raise ValueError("repair changed a validation case object")
    return records


def argument_value(args: list[str], option: str) -> str | None:
    if option not in args:
        return None
    index = args.index(option)
    return args[index + 1] if index + 1 < len(args) else None


def main() -> None:
    if len(sys.argv) < 5 or sys.argv[1] not in {"evaluate", "publish", "replay"} or \
            sys.argv[2] != "--repair-record":
        raise SystemExit("usage: s31_v8r1_postfreeze_roster.py <evaluate|publish|replay> "
                         "--repair-record <path> <original tool arguments...>")
    mode = sys.argv[1]
    record_path = Path(sys.argv[3])
    original_args = sys.argv[4:]
    if not FAILURE.is_file():
        raise ValueError("committed original evaluator failure record is required")
    target = {"evaluate": predictor.main, "publish": publisher.main,
              "replay": portable_replay.main}[mode]
    saved_argv, saved_checker = sys.argv, predictor.checked_cases
    sys.argv = [str(BENCH / f"{target.__module__}.py"), *original_args]
    predictor.checked_cases = lambda corpus, split, protocol, **kwargs: \
        checked_cases_roster_bridge(saved_checker, corpus, split, protocol, **kwargs)
    status = "completed"
    try:
        target()
    except BaseException:
        status = "failed"
        raise
    finally:
        predictor.checked_cases = saved_checker
        sys.argv = saved_argv
        record = {
            "schema": "s31-v8r1-postfreeze-roster-repair-v1",
            "status": status,
            "mode": mode,
            "qualification": "post-freeze evaluator roster repair; not an unqualified prospective V8r1 result",
            "repair_script_sha256": sha_file(Path(__file__)),
            "original_evaluator_failure_sha256": sha_file(FAILURE),
            "frozen_protocol_sha256": argument_value(original_args, "--expected-protocol-sha256"),
            "frozen_model_sha256": argument_value(original_args, "--expected-model-sha256"),
        }
        output = argument_value(original_args, "--out")
        if output is not None and Path(output).is_file():
            record["output_sha256"] = sha_file(Path(output))
        record_path.parent.mkdir(parents=True, exist_ok=True)
        record_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print("POST-FREEZE V8r1 ROSTER REPAIR: result requires this wrapper's provenance record",
          file=sys.stderr)


if __name__ == "__main__":
    main()
