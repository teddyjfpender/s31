#!/usr/bin/env python3
"""Source-derived record statement corpus; optionally compare native Zig parser.

This is a claim parser/projection check. The accepted changed claims are not
assertions that an old proof verifies or that the changed computation is true.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.record_source_fragment import parse_record_source_fragment  # noqa: E402
from independent_statement_fragment_v2 import (  # noqa: E402
    ABI_DOMAIN, InvalidRecordStatementFragment, check_record_source_statement,
)

SOURCE = b"""struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def corpus() -> tuple[list[dict], str]:
    relation = parse_record_source_fragment(SOURCE)
    boundary = relation["public_abi"]
    digest = hashlib.sha256(ABI_DOMAIN + canonical(boundary)).hexdigest()
    leaves = [leaf for root in boundary["inputs"] if root["visibility"] == "public"
              for leaf in root["leaves"]] + boundary["result"]["leaves"]
    values = {"_s31_abi_input_0": 2, "_s31_abi_input_1": 3, "q": 17}
    honest = {"version": 2, "abi_sha256": digest,
              "leaves": [{"path": leaf["path"], "words": [values[leaf["wire"]]]}
                         for leaf in leaves]}
    relation_bytes = canonical(relation)
    cases: list[dict] = []

    def add(label: str, claim: dict, accepted: bool) -> None:
        encoded = canonical(claim)
        try:
            words = check_record_source_statement(SOURCE, encoded)["proof_words"]
        except InvalidRecordStatementFragment:
            words = None
        if (words is not None) != accepted:
            raise AssertionError(f"independent oracle disagrees for {label}")
        cases.append({"label": label, "source": relation_bytes.decode(),
                      "statement": encoded.decode(), "expected_words": words})

    add("honest", honest, True)
    changed = copy.deepcopy(honest)
    changed["leaves"][0]["words"] = [9]
    add("changed_public_input", changed, True)
    changed = copy.deepcopy(honest)
    changed["leaves"][2]["words"] = [18]
    add("changed_derived_result", changed, True)
    mutations = {
        "wrong_digest": lambda claim: claim.__setitem__("abi_sha256", "0" * 64),
        "split_input_result_alias": lambda claim: claim["leaves"][3].__setitem__("words", [4]),
        "wrong_root": lambda claim: claim["leaves"][0]["path"][0].__setitem__("root", "y"),
        "modulus_word": lambda claim: claim["leaves"][0].__setitem__("words", [2**31 - 1]),
        "swapped_leaf_order": lambda claim: claim["leaves"].__setitem__(
            slice(0, 2), list(reversed(claim["leaves"][:2]))),
        "missing_result_leaf": lambda claim: claim["leaves"].pop(),
    }
    for label, mutate in mutations.items():
        changed = copy.deepcopy(honest)
        mutate(changed)
        add(label, changed, False)
    hasher = hashlib.sha256()
    for case in cases:
        hasher.update(canonical(case))
    return cases, hasher.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true",
                        help="run the Zig statement parser corpus (no proof generation)")
    args = parser.parse_args()
    cases, digest = corpus()
    accepted = sum(case["expected_words"] is not None for case in cases)
    report = {"schema": "s31-record-source-statement-fragment-v2",
              "source_sha256": hashlib.sha256(SOURCE).hexdigest(),
              "corpus_sha256": digest, "accepted": accepted,
              "rejected": len(cases) - accepted}
    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-record-source-statement-") as directory:
            path = Path(directory) / "corpus.json"
            path.write_bytes(canonical({"schema": "s31-record-statement-native-corpus-v2",
                                        "cases": cases}))
            run = subprocess.run(
                ["zig", "build", "--build-file", str(S31 / "build.zig"),
                 "record-statement-parser-corpus", "-j1", "--", str(path)],
                capture_output=True, text=True, check=False)
        if run.returncode:
            raise AssertionError("native record parser disagrees: " + run.stderr[-6000:])
        observed = json.loads(run.stdout)
        if observed != {"accepted": accepted, "rejected": len(cases) - accepted}:
            raise AssertionError(f"native counts differ: {observed}")
        report["native"] = observed
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
