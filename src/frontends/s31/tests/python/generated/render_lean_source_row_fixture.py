#!/usr/bin/env python3
"""Render a deterministic Lean source-byte/physical-row audit corpus.

The positional DAG is owned by test_source_mutation_correspondence. The row
calculation below is independent of the native compiler. The native exporter
must still be checked separately against these rows; this fixture makes no
claim about committed AIR columns or verifier soundness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import canonical_ir_bytes, parse_source
from package.direct_gate_schedule import exact_direct_gate_schedule
from test_source_mutation_correspondence import (CORPUS_SHA256, _spell,
                                                 corpus, corpus_digest)
from text_frontend import compile_text

OUTPUT = (ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/"
          "GeneratedMutationRows.lean")
SELECTION = tuple(f"{index:02d}:{'aliases' if index % 2 else 'direct'}"
                  for index in range(16)) + ("15:comments",)
NATIVE_SELECTION = {"00:direct", "07:aliases", "14:direct", "15:comments"}


def lean_bytes(data: bytes) -> str:
    chunks = [data[index:index + 16] for index in range(0, len(data), 16)]
    return "[\n" + "\n".join("    " + ", ".join(map(str, chunk)) +
                             ("," if index < len(chunks) - 1 else "")
                             for index, chunk in enumerate(chunks)) + "\n  ]"


def lean_certificate(sample) -> str:
    instructions = [
        "{ id := %d, lhs := %d, rhs := %d, multiply := %s }" %
        (index, lhs, rhs, str(op == ".*").lower())
        for index, (op, lhs, rhs) in enumerate(sample.steps, 1)
    ]
    return ("{ instructions := [\n      " + ",\n      ".join(instructions) +
            f"],\n    output := {sample.return_id} }}")


def lean_rows(sample, add_rows: int) -> str:
    adds = muls = 0
    rows = []
    for index, (op, lhs, rhs) in enumerate(sample.steps, 1):
        multiply = op == ".*"
        trace_row = add_rows + 28 + muls if multiply else 3 + adds
        rows.append("{ circuitRow := %d, traceRow := %d, multiply := %s, "
                    "in0 := %d, in1 := %d, out := %d }" %
                    (5 + index, trace_row, str(multiply).lower(),
                     22 + lhs, 22 + rhs, 22 + index))
        adds += not multiply
        muls += multiply
    return "[\n      " + ",\n      ".join(rows) + "\n    ]"


def source_uses(sample) -> list[int]:
    uses = [0] * (sample.gate_count + 1)
    for _, lhs, rhs in sample.steps:
        uses[lhs] += 1
        uses[rhs] += 1
    uses[sample.return_id] += 4
    return uses


def render() -> str:
    samples = corpus()
    assert corpus_digest(samples) == CORPUS_SHA256
    selected = {sample.label: sample for sample in samples
                if sample.label in SELECTION}
    assert set(selected) == set(SELECTION)
    assert NATIVE_SELECTION <= set(selected)
    selection_bytes = b"".join(label.encode() + b"\0" +
                               selected[label].source.encode() + b"\0"
                               for label in SELECTION)
    selection_sha = hashlib.sha256(selection_bytes).hexdigest()
    lines = [
        "import S31.Gadgets.Functional.SSAAliasTextBytes",
        "import S31.Gadgets.Functional.SSAAirColumnCells",
        "import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes",
        "",
        "/-!",
        "Kernel-reduced samples for the bounded direct-Gate source grammar.",
        "The independent positional generator and this renderer pin 17 sources",
        "with 1..16 arithmetic instructions, aliases, comments, and earlier returns.",
        f"Full Python mutation corpus SHA-256: {CORPUS_SHA256}",
        f"Selected source-byte SHA-256: {selection_sha}",
        "Each certificate, row address/selector position, and use count is",
        "an explicit datum checked by Lean's byte parser and row projection.",
        "The `totalAddRows` values come from the independent Python schedule.",
        "The native exporter equality, actual AIR fixed columns, proof",
        "authentication, and verifier soundness remain external obligations.",
        "The four native samples additionally check exact normalized JSON",
        "and compact canonical IR bytes with negative controls.",
        "-/",
        "",
        "namespace S31.Functional.Correspondence.GeneratedMutationRows",
        "",
        "open S31.Functional.SSACertificate",
        "open S31.Functional.SSAAliasTextBytes",
        "open S31.Functional.SSADirectGateBridge",
        "open S31.Functional.SSAAirColumnCells",
        "open S31.Functional.Correspondence.AliasCanonicalIrBytes",
        "",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 2000000",
        "",
    ]
    for index, label in enumerate(SELECTION):
        sample = selected[label]
        checked, syntax = parse_source(sample.source.encode())
        gates, _, n_rows, source = exact_direct_gate_schedule(syntax)
        assert n_rows == 512 and len(source) == sample.gate_count
        assert syntax["output"] == sample.return_id
        assert len(checked["nodes"]) == sample.gate_count
        assert {op for op, _, _ in sample.steps} <= {"+", ".*"}
        add_rows = len(gates["add"])
        seen_adds = seen_muls = 0
        for wire_id, ((op, lhs, rhs), emitted) in enumerate(
                zip(sample.steps, source, strict=True), 1):
            kind = "pointwise_mul" if op == ".*" else "add"
            slot = seen_muls if op == ".*" else 3 + seen_adds
            expected_gate = {"in0": 22 + lhs, "in1": 22 + rhs,
                             "out": 22 + wire_id}
            assert gates[kind][slot] == expected_gate
            assert emitted == {"id": wire_id,
                               "op": "mul" if op == ".*" else "add",
                               **expected_gate}
            seen_adds += op == "+"
            seen_muls += op == ".*"
        mutated_return = (1 if sample.return_id != 1 else sample.gate_count)
        if mutated_return == sample.return_id:
            mutated_steps = list(sample.steps)
            op, lhs, rhs = mutated_steps[0]
            mutated_steps[0] = ("+" if op == ".*" else ".*", lhs, rhs)
            mutated = _spell(index, mutated_steps, sample.return_id,
                             label.split(":")[1])
        else:
            mutated = _spell(index, list(sample.steps), mutated_return,
                             label.split(":")[1])
        parsed_mutant = parse_source(mutated.encode())[1]
        assert (parsed_mutant["output"] != sample.return_id or
                parsed_mutant["instructions"] != syntax["instructions"])
        expected_uses = source_uses(sample)
        if sample.return_id < sample.gate_count:
            assert expected_uses[-1] == 0
        prefix = f"case{index:02d}"
        lines += [
            f"-- {label}: {sample.gate_count} producers; returned wire {sample.return_id}.",
            f"def {prefix}Bytes : List Nat := {lean_bytes(sample.source.encode())}",
            f"def {prefix}MutatedBytes : List Nat := {lean_bytes(mutated.encode())}",
            f"def {prefix}Certificate : Certificate :=",
            f"  {lean_certificate(sample)}",
            f"def {prefix}Rows : List NativeSourceRow :=",
            f"  {lean_rows(sample, add_rows)}",
            f"def {prefix}Uses : List Nat := {expected_uses}",
            f"theorem {prefix}Checks :",
            f"    (parseAliasBytes {prefix}Bytes).map (fun parsed => parsed.certificate) =",
            f"      some {prefix}Certificate ∧",
            f"    expectedRows {prefix}Certificate {add_rows} = {prefix}Rows ∧",
            f"    (List.range {sample.gate_count + 1}).map (sourceUses {prefix}Certificate) =",
            f"      {prefix}Uses ∧",
            f"    (parseAliasBytes {prefix}MutatedBytes).map (fun parsed => parsed.certificate) ≠",
            f"      some {prefix}Certificate := by decide",
            "",
        ]
        if label in NATIVE_SELECTION:
            normalized, _ = compile_text(sample.source)
            normalized_bytes = (json.dumps(normalized, indent=2, sort_keys=True) + "\n").encode()
            canonical_bytes = canonical_ir_bytes(syntax)
            old = b'"op": "add"' if b'"op": "add"' in normalized_bytes else b'"op": "mul"'
            new = b'"op": "mul"' if old.endswith(b'"add"') else b'"op": "add"'
            changed_bytes = normalized_bytes.replace(old, new, 1)
            assert changed_bytes != normalized_bytes
            lines += [
                f"-- Native proof sample {label}; normalized SHA-256: "
                f"{hashlib.sha256(normalized_bytes).hexdigest()}",
                f"def {prefix}NormalizedBytes : List Nat := {lean_bytes(normalized_bytes)}",
                f"def {prefix}ChangedNormalizedBytes : List Nat := {lean_bytes(changed_bytes)}",
                f"-- Canonical IR SHA-256: {hashlib.sha256(canonical_bytes).hexdigest()}",
                f"def {prefix}CanonicalBytes : List Nat := {lean_bytes(canonical_bytes)}",
                f"theorem {prefix}NormalizedChecks :",
                f"    checkAliasRelation {prefix}Bytes {prefix}NormalizedBytes =",
                f"      some {prefix}Certificate ∧",
                f"    checkAliasRelation {prefix}Bytes {prefix}ChangedNormalizedBytes =",
                "      none := by decide",
                f"theorem {prefix}CanonicalChecks :",
                f"    checkAliasCanonical {prefix}Bytes {prefix}NormalizedBytes",
                f"      {prefix}CanonicalBytes = some {prefix}Certificate ∧",
                f"    checkAliasCanonical {prefix}Bytes {prefix}NormalizedBytes",
                f"      ({prefix}CanonicalBytes ++ [32]) = none := by decide",
                "",
            ]
    lines += ["end S31.Functional.Correspondence.GeneratedMutationRows", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = render()
    if args.check:
        if OUTPUT.read_text() != rendered:
            raise SystemExit(f"stale generated Lean source/row fixture: {OUTPUT}")
        print(f"checked {OUTPUT.relative_to(ROOT)}")
    else:
        OUTPUT.write_text(rendered)
        print(f"wrote {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
