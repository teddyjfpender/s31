#!/usr/bin/env python3
"""Source-pinned native controls for constrained arithmetic-to-chip ports."""

from __future__ import annotations

import hashlib
import json
import tempfile
from pathlib import Path

from registry_manifest_digest import digest as registry_manifest_digest
from source_pinned_general import MAGIC, MODULUS, SUMS_OFFSET, S31, build, run, verify_rejects

EXAMPLES = S31 / "examples" / "boundary"
INPUTS = [0, 1, MODULUS - 1, 7]


def repeat(values: list[int], constant: int) -> list[int]:
    for _ in range(16):
        values = [(value * value + constant) % MODULUS for value in values]
    return values


def oracle(fork: bool, middle_op: str = "add") -> tuple[list[int], list[int]]:
    first = repeat(INPUTS, 13)
    if middle_op == "add":
        middle = [(left + right) % MODULUS for left, right in zip(first, INPUTS)]
    elif middle_op == "mul":
        middle = [(left * right) % MODULUS for left, right in zip(first, INPUTS)]
    elif middle_op == "add_const":
        middle = [(left + 5) % MODULUS for left in first]
    elif middle_op == "mul_const":
        middle = [(left * 3) % MODULUS for left in first]
    else:
        raise AssertionError(f"unknown middle operation: {middle_op}")
    second = repeat(middle, 17)
    if fork:
        third = repeat(middle, 19)
        return [(a + b) % MODULUS for a, b in zip(second, third)], [
            (a * b) % MODULUS for a, b in zip(second, third)
        ]
    return [(a + b) % MODULUS for a, b in zip(second, INPUTS)], [
        (a * b) % MODULUS for a, b in zip(second, middle)
    ]


def changed_source_verifier(source: Path, work: Path) -> tuple[Path, dict]:
    work.mkdir(parents=True, exist_ok=True)
    path = work / "altered.s31.json"
    # Preserve the canonical IR, endpoints, circuit and public relation. A
    # changed source digest alone must still make the old proof unusable.
    path.write_bytes(source.read_bytes() + b" ")
    _, verifier, inspector = build(path, work / "altered-build")
    return verifier, json.loads(run(str(inspector)).stdout)


def variant(work: Path, middle_op: str) -> tuple[Path, Path]:
    source_value = json.loads((EXAMPLES / "private_arithmetic_chip_input.s31.json").read_text())
    middle = next(node for node in source_value["nodes"] if node["name"] == "middle")
    middle["op"] = middle_op
    if middle_op in ("add_const", "mul_const"):
        middle.pop("rhs")
        middle["constant"] = 5 if middle_op == "add_const" else 3
    source_value["name"] = f"private_arithmetic_chip_{middle_op}"
    assignment_value = json.loads((EXAMPLES / "private_arithmetic_chip_input.valid.json").read_text())
    first, second = oracle(False, middle_op)
    assignment_value["public_outputs"] = {"sum": first, "product": second}
    source = work / f"{source_value['name']}.s31.json"
    assignment = work / f"{source_value['name']}.valid.json"
    source.write_text(json.dumps(source_value, separators=(",", ":")))
    assignment.write_text(json.dumps(assignment_value, separators=(",", ":")))
    return source, assignment


def exercise(work: Path, source: Path, assignment: Path, count: int, middle_op: str = "add") -> dict:
    stem = source.stem.removesuffix(".s31")
    expected = oracle(count == 3, middle_op)
    assert list(json.loads(assignment.read_text())["public_outputs"].values()) == expected
    prover, verifier, inspector = build(source, work / f"build-{stem}")
    manifest = json.loads(run(str(inspector)).stdout)
    assert manifest["call_count"] == count
    assert manifest["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert manifest["registry_manifest_sha256"] == registry_manifest_digest(manifest)
    assert manifest["conditional_lookup_budget"]["integerized_absolute_weight"] < MODULUS
    calls = manifest["calls"]
    assert len(calls[1]["input"]) == 4
    assert all(address > 2 for address in calls[1]["input"])
    if count == 3:
        assert calls[1]["input"] == calls[2]["input"]

    proof = work / f"{stem}.proof"
    statement = work / f"{stem}.statement.json"
    run(str(prover), str(assignment), str(proof), str(statement))
    run(str(verifier), str(proof), str(statement))
    saved = json.loads(statement.read_text())
    assert saved["public_words"] == [*expected[0], *expected[1]]
    raw = proof.read_bytes()
    assert raw.startswith(MAGIC + bytes((count, 1 + 2 * count, 3, 0)))
    for index in range(1 + 2 * count):
        changed = bytearray(raw)
        changed[SUMS_OFFSET + 16 * index] ^= 1
        bad = work / f"{stem}.sum{index}.proof"
        bad.write_bytes(changed)
        verify_rejects(verifier, bad, statement)
    changed = bytearray(raw)
    for index, delta in ((0, 1), (1, -1)):
        at = SUMS_OFFSET + 16 * index
        value = int.from_bytes(changed[at:at + 4], "little")
        changed[at:at + 4] = ((value + delta) % MODULUS).to_bytes(4, "little")
    bad = work / f"{stem}.compensated.proof"
    bad.write_bytes(changed)
    verify_rejects(verifier, bad, statement)
    changed = bytearray(raw)
    changed[-1] ^= 1
    bad.write_bytes(changed)
    verify_rejects(verifier, bad, statement)

    altered_statement = {**saved, "public_words": saved["public_words"].copy()}
    altered_statement["public_words"][0] = (altered_statement["public_words"][0] + 1) % MODULUS
    bad_statement = work / f"{stem}.bad-statement.json"
    bad_statement.write_text(json.dumps(altered_statement))
    verify_rejects(verifier, proof, bad_statement)
    changed_assignment = json.loads(assignment.read_text())
    changed_assignment["private_inputs"]["x"][0] = 2
    bad_assignment = work / f"{stem}.bad-assignment.json"
    bad_assignment.write_text(json.dumps(changed_assignment))
    run(str(prover), str(bad_assignment), str(bad), str(bad_statement), accept=False)

    other_verifier, other_manifest = changed_source_verifier(source, work / stem)
    assert other_manifest["source_sha256"] != manifest["source_sha256"]
    assert other_manifest["canonical_ir_sha256"] == manifest["canonical_ir_sha256"]
    assert other_manifest["fixed_root"] == manifest["fixed_root"]
    assert other_manifest["calls"] == manifest["calls"]
    resealed = {**saved}
    for field, manifest_field in (
        ("source_sha256", "source_sha256"),
        ("selected_manifest_sha256", "manifest_sha256"),
        ("registry_manifest_sha256", "registry_manifest_sha256"),
        ("circuit_identity_sha256", "circuit_identity_sha256"),
    ):
        resealed[field] = other_manifest[manifest_field]
    bad_statement.write_text(json.dumps(resealed))
    verify_rejects(other_verifier, proof, bad_statement)
    # Also reseal the cleartext envelope identity fields. The STARK transcript
    # must reject a proof made under the old source-derived key.
    changed = bytearray(raw)
    for index, field in enumerate(("source_sha256", "registry_manifest_sha256", "circuit_identity_sha256")):
        at = len(MAGIC) + 4 + 32 * index
        changed[at:at + 32] = bytes.fromhex(resealed[field])
    bad.write_bytes(changed)
    verify_rejects(other_verifier, bad, bad_statement)
    return {"source": stem, "middle_op": middle_op, "calls": count,
            "proof_bytes": len(raw), "proof_sha256": hashlib.sha256(raw).hexdigest()}


def reject_dead_call(work: Path) -> None:
    source = json.loads((EXAMPLES / "private_arithmetic_chip_input.s31.json").read_text())
    source["nodes"].insert(1, {
        "name": "unused", "op": "repeat", "lhs": "x", "rounds": 16,
        "body": [{"op": "square"}, {"op": "add_const", "constant": 23}],
    })
    path = work / "dead-call.s31.json"
    path.write_text(json.dumps(source, separators=(",", ":")))
    build(path, work / "dead-build", accept=False)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-arithmetic-chip-input-") as directory:
        work = Path(directory)
        results = [
            exercise(work, EXAMPLES / "private_arithmetic_chip_input.s31.json",
                     EXAMPLES / "private_arithmetic_chip_input.valid.json", 2),
            exercise(work, EXAMPLES / "private_arithmetic_chip_fork.s31.json",
                     EXAMPLES / "private_arithmetic_chip_fork.valid.json", 3),
        ]
        for middle_op in ("mul", "add_const", "mul_const"):
            source, assignment = variant(work, middle_op)
            results.append(exercise(work, source, assignment, 2, middle_op))
        reject_dead_call(work)
        print(json.dumps({"schema": "s31-arithmetic-chip-input-acceptance-v1", "profiles": results, "accepted": True}, sort_keys=True))


if __name__ == "__main__":
    main()
