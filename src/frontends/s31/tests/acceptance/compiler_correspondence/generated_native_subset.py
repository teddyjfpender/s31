#!/usr/bin/env python3
"""Native direct-Gate proof samples from the pinned source mutation corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
from dataclasses import replace
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

import s31
from package.correspondence import check_package, parse_source
from test_source_mutation_correspondence import CORPUS_SHA256, corpus, corpus_digest
from text_frontend import compile_text

MODULUS = 2_147_483_647
INPUT = (0, 1, 2, 7)
SELECTED = ("00:direct", "07:aliases", "14:direct", "15:comments")


def expected_words(sample) -> list[int]:
    """Evaluate the generator's positional DAG, without either S31 parser."""
    values = [list(INPUT)]
    for op, lhs, rhs in sample.steps:
        values.append([((left + right) if op == "+" else (left * right)) % MODULUS
                       for left, right in zip(values[lhs], values[rhs], strict=True)])
    return values[sample.return_id]


def expected_instructions(sample) -> list[dict]:
    return [
        {"id": index, "name": f"p{index}",
         "op": "add" if op == "+" else "mul", "lhs": lhs, "rhs": rhs}
        for index, (op, lhs, rhs) in enumerate(sample.steps, 1)
    ]


def normalized_bytes(sample) -> bytes:
    """Use the serializer whose exact output the Lean byte fixture checks."""
    relation, _ = compile_text(sample.source)
    return (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()


def check_static(sample) -> dict:
    checked, syntax = parse_source(sample.source.encode())
    produced, _ = compile_text(sample.source)
    if (checked != produced or
            len(checked["nodes"]) != sample.gate_count or
            syntax["output"] != sample.return_id or
            syntax["instructions"] != expected_instructions(sample)):
        raise AssertionError("pinned generator source changed certificate shape")
    return {"sample": sample.label, "gates": sample.gate_count,
            "returned_gate": sample.return_id,
            "expected_public_words": expected_words(sample),
            "normalized_sha256": hashlib.sha256(normalized_bytes(sample)).hexdigest()}


def check_static_mutations(sample) -> int:
    first = sample.steps[0]
    changed_op = (".*" if first[0] == "+" else "+", first[1], first[2])
    mutations = [replace(sample, steps=(changed_op, *sample.steps[1:])),
                 replace(sample, return_id=(1 if sample.return_id != 1 else 0))]
    if sample.return_id < sample.gate_count:
        last = sample.steps[-1]
        dead_op = (".*" if last[0] == "+" else "+", last[1], last[2])
        mutations.append(replace(sample, steps=(*sample.steps[:-1], dead_op)))
    for changed in mutations:
        try:
            check_static(changed)
        except AssertionError:
            continue
        raise AssertionError(f"changed generator DAG escaped: {sample.label}")
    return len(mutations)


def exercise(work: Path, sample) -> dict:
    expected = check_static(sample)
    source = work / f"{sample.label.replace(':', '-')}.s31"
    source.write_text(sample.source + "\n")
    assignment = work / f"{sample.label.replace(':', '-')}.json"
    assignment.write_text(json.dumps({
        "public_inputs": {"x": INPUT},
        "private_inputs": {},
        "public_outputs": {f"p{sample.return_id}": expected_words(sample)},
    }, separators=(",", ":")) + "\n")
    package = s31.build(source, work / f"package-{sample.label.replace(':', '-')}",
                        "direct-gate")
    if (package / "source.s31.json").read_bytes() != normalized_bytes(sample):
        raise AssertionError("native package normalized bytes differ from Lean fixture")
    certificate = check_package(package)
    if (certificate["source_ssa"]["output"] != sample.return_id or
            certificate["source_ssa"]["instructions"] != expected_instructions(sample)):
        raise AssertionError("package correspondence differs from pinned DAG")
    trial = s31.trial(package, assignment,
                      work / f"trial-{sample.label.replace(':', '-')}")
    oracle = trial["independent_value_oracle"]
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            oracle.get("status") != "passed" or
            oracle.get("computed_public_outputs") !=
            {f"p{sample.return_id}": expected_words(sample)}):
        raise AssertionError("native proof or public-word negative control failed")
    return {"sample": expected["sample"], "gates": expected["gates"],
            "returned_gate": expected["returned_gate"],
            "proof_sha256": trial["proof_sha256"],
            "proof_bytes": trial["proof_bytes"],
            "changed_public_statement_rejected": trial["changed_public_statement_rejected"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, help="retain package and proof artifacts")
    parser.add_argument("--static", action="store_true",
                        help="run independent DAG/source checks without native builds")
    args = parser.parse_args()
    samples = corpus()
    if corpus_digest(samples) != CORPUS_SHA256:
        raise AssertionError("pinned source mutation corpus changed")
    selected = {sample.label: sample for sample in samples if sample.label in SELECTED}
    if set(selected) != set(SELECTED):
        raise AssertionError("native sample labels missing from pinned corpus")
    if args.static:
        print(json.dumps({"schema": "s31-generated-source-native-subset-static-v1",
                          "corpus_sha256": CORPUS_SHA256,
                          "cases": [check_static(selected[label]) for label in SELECTED],
                          "generator_mutations_rejected": sum(
                              check_static_mutations(selected[label])
                              for label in SELECTED)},
                         sort_keys=True))
        return

    def run(work: Path) -> None:
        work.mkdir(parents=True, exist_ok=True)
        results = []
        for label in SELECTED:
            print(f"native direct-Gate correspondence: {label}", file=sys.stderr,
                  flush=True)
            results.append(exercise(work, selected[label]))
        print(json.dumps({"schema": "s31-generated-source-native-subset-v1",
                          "corpus_sha256": CORPUS_SHA256,
                          "accepted": True, "cases": results}, sort_keys=True))

    if args.work:
        run(args.work.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="s31-generated-native-") as directory:
            run(Path(directory))


if __name__ == "__main__":
    main()
