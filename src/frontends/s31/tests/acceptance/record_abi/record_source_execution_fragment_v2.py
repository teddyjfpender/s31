#!/usr/bin/env python3
"""Compare independent record-source values to Zig Program.evaluate.

This finite differential corpus is a native execution check, not a proof of
the Zig interpreter or PCS/FRI verifier for arbitrary programs.
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.record_source_fragment import (  # noqa: E402
    expected_public_abi, parse_record_source_fragment,
)
from package.record_value_fragment import (  # noqa: E402
    InvalidRecordValueFragment, P, evaluate_record_source_assignment,
)

SOURCE = b"""struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""


def encoded(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def assignment(a: int, b: int, secret: int) -> dict:
    return {"public_inputs": {"_s31_abi_input_0": [a],
                              "_s31_abi_input_1": [b]},
            "private_inputs": {"_s31_abi_input_2": [13],
                               "_s31_abi_input_3": [secret]},
            "public_outputs": {"q": [(a * secret + b) % P],
                               "_s31_abi_input_1": [b]}}


def corpus() -> list[dict]:
    relation = parse_record_source_fragment(SOURCE)
    relation_text = encoded(relation).decode()
    abi_digest = expected_public_abi(relation)["boundary_sha256"]
    rng = random.Random(0x531_2026)
    vectors = [(2, 3, 7), (0, 0, 0), (P - 1, P - 1, P - 1)]
    vectors.extend((rng.randrange(P), rng.randrange(P), rng.randrange(P))
                   for _ in range(20))
    cases: list[dict] = []
    for index, (a, b, secret) in enumerate(vectors):
        assigned = assignment(a, b, secret)
        independent = evaluate_record_source_assignment(SOURCE, encoded(assigned))
        statement = {"version": 2, "abi_sha256": abi_digest,
                     "leaves": independent["leaves"]}
        cases.append({"label": f"honest_{index}", "source": relation_text,
                      "statement": encoded(statement).decode(),
                      "expected_words": independent["proof_words"],
                      "assignment": encoded(assigned).decode()})
        # Keep the named statement valid, including the repeated right-field
        # alias, while changing only the arithmetic result claim.
        changed = assignment(a, b, secret)
        changed["public_outputs"]["q"] = [(changed["public_outputs"]["q"][0] + 1) % P]
        try:
            evaluate_record_source_assignment(SOURCE, encoded(changed))
        except InvalidRecordValueFragment:
            pass
        else:
            raise AssertionError("independent evaluator accepted changed result")
        bad_leaves = [dict(leaf) for leaf in independent["leaves"]]
        bad_leaves[2] = dict(bad_leaves[2], words=changed["public_outputs"]["q"])
        bad_statement = {"version": 2, "abi_sha256": abi_digest,
                         "leaves": bad_leaves}
        bad_words = independent["proof_words"].copy()
        bad_words[2] = changed["public_outputs"]["q"][0]
        cases.append({"label": f"changed_result_{index}", "source": relation_text,
                      "statement": encoded(bad_statement).decode(),
                      "expected_words": bad_words,
                      "assignment": encoded(changed).decode(),
                      "expected_eval_error": "PublicOutputMismatch"})
    return cases


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    cases = corpus()
    report = {"schema": "s31-record-source-execution-fragment-v2",
              "cases": len(cases),
              "valid_values": sum("expected_eval_error" not in case for case in cases),
              "changed_results": sum("expected_eval_error" in case for case in cases)}
    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-record-execution-") as directory:
            path = Path(directory) / "corpus.json"
            path.write_bytes(encoded({"schema": "s31-record-statement-native-corpus-v2",
                                      "cases": cases}))
            run = subprocess.run(
                ["zig", "build", "--build-file", str(S31 / "build.zig"),
                 "record-statement-parser-corpus", "-j1", "--", str(path)],
                capture_output=True, text=True, check=False)
        if run.returncode:
            raise AssertionError("native record evaluator disagrees: " + run.stderr[-6000:])
        observed = json.loads(run.stdout)
        if observed != {"accepted": len(cases), "rejected": 0}:
            raise AssertionError(f"native counts differ: {observed}")
        report["native"] = observed
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
