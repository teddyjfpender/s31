#!/usr/bin/env python3
"""Verify genuine proofs for four diverse layouts in the 13-layout ABI corpus.

The 13-layout parser corpus checks every generated descriptor; this slower
subset checks native proof binding for representative source programs. Each
changed statement remains ABI-valid and projects to different proof words.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from general_statement_refinement_v2 import (LEAN, consistent_change, projection,
                                             relation_and_binding, render, sources)
from nested_alias_v2 import S31, canonical

sys.path.insert(0, str(S31 / "python"))
import s31  # noqa: E402
from abi.binding_v2 import (binding_digest, decode_public_statement,
                            statement_from_assignment)  # noqa: E402
from text_frontend import compile_text  # noqa: E402

P = 2**31 - 1
FIXTURES = {
    "pair_4": {
        "inputs": [[2, 3, 5, 7]],
        "outputs": [[2, 3, 5, 7]],
        "proof_words": [2, 3, 5, 7, 2, 3, 5, 7],
    },
    "tuple_2_2": {
        "inputs": [[11, 13], [17, 19]],
        "outputs": [[11, 13], [17, 19]],
        "proof_words": [11, 13, 17, 19, 11, 13, 17, 19],
    },
    "bit_3": {
        "inputs": [[1], [23, 29, 31]],
        "outputs": [[23, 29, 31]],
        "proof_words": [1, 23, 29, 31, 23, 29, 31, 0],
    },
    "private_2": {
        "inputs": [[P - 1, 5], [37, 41], [2, 7]],
        "outputs": [[1, 12]],
        "proof_words": [P - 1, 5, 37, 41, 1, 12, 0, 0],
    },
}


def assignment_for(relation: dict, label: str) -> dict:
    fixture = FIXTURES[label]
    inputs = relation["inputs"]
    outputs = relation["public_outputs"]
    if len(inputs) != len(fixture["inputs"]) or len(outputs) != len(fixture["outputs"]):
        raise AssertionError(f"{label}: compiled input/output arity changed")
    assignment = {"public_inputs": {}, "private_inputs": {}, "public_outputs": {}}
    for descriptor, values in zip(inputs, fixture["inputs"], strict=True):
        if descriptor["length"] != len(values):
            raise AssertionError(f"{label}: compiled input width changed")
        assignment[f"{descriptor['visibility']}_inputs"][descriptor["name"]] = values
    for wire, values in zip(outputs, fixture["outputs"], strict=True):
        assignment["public_outputs"][wire] = values
    return assignment


def run_case(label: str, source_text: str, work: Path) -> dict:
    compiled, _ = compile_text(source_text)
    relation, binding = relation_and_binding(compiled)
    source = work / f"{label}.s31"
    source.write_text(source_text)
    package = s31.build(source, work / f"package-{label}", "direct-gate")
    native_relation = json.loads((package / "source.s31.json").read_bytes())
    key_path = package / "verification-key.json"
    key = json.loads(key_path.read_bytes())
    if (native_relation != compiled or
            (package / "source.s31").read_text() != source_text or
            key["public_abi_sha256"] != binding_digest(relation, binding)):
        raise AssertionError(f"{label}: native package did not seal compiled source and ABI")

    assignment = assignment_for(compiled, label)
    assignment_path = work / f"assignment-{label}.json"
    assignment_path.write_bytes(canonical(assignment))
    trial_dir = work / f"trial-{label}"
    trial = s31.trial(package, assignment_path, trial_dir)
    if (trial["native_verifier_accepted"] is not True or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{label}: native proof or independent value oracle failed")
    statement_path = trial_dir / "statement.json"
    statement_bytes = statement_path.read_bytes()
    statement = json.loads(statement_bytes)
    expected = FIXTURES[label]["proof_words"]
    projected = projection(compiled, statement)[3]
    if (statement_bytes != statement_from_assignment(compiled, assignment) or
            decode_public_statement(relation, binding, statement_bytes) != expected or
            projected != expected):
        raise AssertionError(f"{label}: native statement disagrees with independent projection")

    changed, changed_words = consistent_change(relation, binding, statement, expected)
    if changed_words == expected:
        raise AssertionError(f"{label}: changed public claim projected to original words")
    changed_path = work / f"changed-valid-{label}.json"
    changed_path.write_bytes(canonical(changed))
    verifier = package / "bin" / f"s31-{compiled['name']}-native-verifier"
    result = subprocess.run(
        (str(verifier), str(trial_dir / "proof.bin"), str(changed_path), str(key_path)),
        capture_output=True, text=True, check=False,
    )
    if (result.returncode != 1 or "error:" not in result.stderr or
            any(parser_error in result.stderr for parser_error in
                ("InvalidRecordStatement", "InvalidRecordAbi", "InvalidVerificationKey", "panic:"))):
        raise AssertionError(f"{label}: ABI-valid changed claim did not fail proof binding: "
                             f"exit={result.returncode}, stderr={result.stderr}")
    return {"case": label, "proof_bytes": trial["proof_bytes"],
            "public_words": expected, "changed_public_words": changed_words,
            "changed_claim_verifier_error": result.stderr.strip().splitlines()[-1],
            "source_sha256": hashlib.sha256(source_text.encode()).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=tuple(FIXTURES), action="append",
                        help="run one selected layout; repeat for several")
    args = parser.parse_args()
    selected = set(args.case or FIXTURES)
    lean_source, corpus = render()
    if not LEAN.is_file() or LEAN.read_text() != lean_source:
        raise AssertionError("proof source corpus differs from checked-in Lean fixture")
    texts = dict(sources())
    if not selected <= texts.keys():
        raise AssertionError("proof fixture is missing from the generated source corpus")
    with tempfile.TemporaryDirectory(prefix="s31-record-proof-corpus-") as temporary:
        work = Path(temporary)
        cases = [run_case(label, texts[label], work) for label in FIXTURES if label in selected]
    print(json.dumps({"schema": "s31-record-native-proof-corpus-v2",
                      "source_corpus_sha256": corpus["source_sha256"],
                      "native_proofs_accepted": len(cases),
                      "abi_valid_changed_claims_rejected_by_proof": len(cases),
                      "cases": cases}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
