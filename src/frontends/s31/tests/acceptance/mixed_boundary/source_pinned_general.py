#!/usr/bin/env python3
"""Black-box source-pinned controls for the experimental 1..8 mixed proof."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from registry_manifest_digest import digest as registry_manifest_digest

S31 = Path(__file__).resolve().parents[3]
MODULUS = 2_147_483_647
MAGIC = b"S31MIX07"
SUMS_OFFSET = len(MAGIC) + 4 + 32 * 3 + 8


def run(*args: str, accept: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True, check=False)
    if (result.returncode == 0) != accept:
        raise AssertionError(
            f"unexpected exit {result.returncode} for {args}:\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result


def family(count: int) -> tuple[dict, dict]:
    assert 1 <= count <= 8
    nodes = []
    for call_id in range(count):
        nodes.append({
            "name": f"r{call_id}", "op": "repeat",
            "lhs": "x" if call_id == 0 else f"r{call_id - 1}",
            "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 13 + call_id}],
        })
    nodes += [
        {"name": "sum", "op": "add", "lhs": f"r{count - 1}", "rhs": "x"},
        {"name": "product", "op": "mul", "lhs": f"r{count - 1}", "rhs": "x"},
    ]
    source = {
        "version": 1, "name": f"mixed_general_{count}",
        "inputs": [{"name": "x", "kind": "m31", "length": 4, "visibility": "private"}],
        "nodes": nodes, "assertions": [], "public_outputs": ["sum", "product"],
    }
    initial = [1, 2, 3, 4]
    result = initial.copy()
    for call_id in range(count):
        for _ in range(16):
            result = [(value * value + 13 + call_id) % MODULUS for value in result]
    assignment = {
        "public_inputs": {}, "private_inputs": {"x": initial},
        "public_outputs": {
            "sum": [(a + b) % MODULUS for a, b in zip(result, initial)],
            "product": [(a * b) % MODULUS for a, b in zip(result, initial)],
        },
    }
    return source, assignment


def build(source: Path, prefix: Path, *, accept: bool = True) -> tuple[Path, Path, Path]:
    run(
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source}",
        "-Ds31-name=general", "-j1", "--prefix", str(prefix), accept=accept,
    )
    root = prefix / "bin"
    return (
        root / "s31-general-mixed-general-prover",
        root / "s31-general-mixed-general-native-verifier",
        root / "s31-general-mixed-general-manifest",
    )


def verify_rejects(verifier: Path, proof: Path, statement: Path) -> None:
    result = subprocess.run((str(verifier), str(proof), str(statement)),
                            text=True, capture_output=True, check=False, timeout=30)
    if result.returncode == 0 or result.returncode < 0:
        raise AssertionError(
            f"native verifier accepted or crashed on changed proof or statement "
            f"(exit {result.returncode}): {proof}, {statement}"
        )


def exercise(work: Path, count: int) -> dict:
    source_value, assignment_value = family(count)
    source = work / f"general-{count}.s31.json"
    assignment = work / f"assignment-{count}.json"
    source.write_text(json.dumps(source_value, separators=(",", ":")))
    assignment.write_text(json.dumps(assignment_value, separators=(",", ":")))
    prover, verifier, manifest_bin = build(source, work / f"build-{count}")
    manifest = json.loads(run(str(manifest_bin)).stdout)
    assert manifest["schema"] == "s31-mixed-component-inspection-general-v3"
    assert manifest["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert manifest["call_count"] == count and manifest["slot_count"] == 1 + 2 * count
    assert manifest["registry_manifest_sha256"] == registry_manifest_digest(manifest)
    assert [slot["claimed_sum_index"] for slot in manifest["slots"]] == list(range(1 + 2 * count))
    assert [slot["registry_role"] for slot in manifest["slots"]] == [
        "circuit", *(role for _ in range(count) for role in ("chip", "bridge")),
    ]
    assert [slot["registry_id"] for slot in manifest["slots"]] == [
        0, *(id for call in range(count) for id in ((1, 2) if call < 2 else (3, 4))),
    ]
    proof = work / f"proof-{count}.bin"
    statement = work / f"statement-{count}.json"
    run(str(prover), str(assignment), str(proof), str(statement))
    run(str(verifier), str(proof), str(statement))
    raw = proof.read_bytes()
    saved = json.loads(statement.read_text())
    assert raw[:len(MAGIC) + 4] == MAGIC + bytes((count, 1 + 2 * count, 3, 0))
    assert saved["schema"] == "s31-mixed-public-words-general-v3"
    assert saved["source_sha256"] == manifest["source_sha256"]
    assert saved["selected_manifest_sha256"] == manifest["manifest_sha256"]
    assert saved["registry_manifest_sha256"] == manifest["registry_manifest_sha256"]
    assert saved["circuit_identity_sha256"] == manifest["circuit_identity_sha256"]
    assert saved["public_words"] == [
        *assignment_value["public_outputs"]["sum"],
        *assignment_value["public_outputs"]["product"],
    ]
    for field, offset in (
        ("source_sha256", len(MAGIC) + 4),
        ("registry_manifest_sha256", len(MAGIC) + 36),
        ("circuit_identity_sha256", len(MAGIC) + 68),
    ):
        assert raw[offset:offset + 32].hex() == saved[field]
    for name, offset in (
        ("magic", 0), ("count", len(MAGIC)),
        ("roster", len(MAGIC) + 1), ("schema", len(MAGIC) + 2),
        ("source", len(MAGIC) + 4), ("registry", len(MAGIC) + 36),
        ("identity", len(MAGIC) + 68),
        *((f"sum{i}", SUMS_OFFSET + 16 * i) for i in range(1 + 2 * count)),
        ("proof_tail", len(raw) - 1),
    ):
        changed = bytearray(raw)
        changed[offset] ^= 1
        altered = work / f"bad-{count}-{name}.bin"
        altered.write_bytes(changed)
        verify_rejects(verifier, altered, statement)
    for field, value in (
        ("schema", "s31-mixed-public-words-n4-v2"),
        ("source_sha256", "0" * 64),
        ("selected_manifest_sha256", "0" * 64),
        ("registry_manifest_sha256", "0" * 64),
        ("circuit_identity_sha256", "0" * 64),
        ("public_words", [0] * 8),
    ):
        altered = work / f"bad-{count}-{field}.json"
        altered.write_text(json.dumps({**saved, field: value}))
        verify_rejects(verifier, proof, altered)
    if count in (1, 3, 8):
        for lane, original in enumerate(saved["public_words"]):
            words = saved["public_words"].copy()
            words[lane] = (original + 1) % MODULUS
            altered = work / f"bad-{count}-public-word-{lane}.json"
            altered.write_text(json.dumps({**saved, "public_words": words}))
            verify_rejects(verifier, proof, altered)
        # Preserve the total QM31 claimed sum while changing two individual
        # component claims. The transcript and installed AIR claims must still
        # reject this coordinated mutation.
        compensated = bytearray(raw)
        first = int.from_bytes(compensated[SUMS_OFFSET:SUMS_OFFSET + 4], "little")
        second_at = SUMS_OFFSET + 16
        second = int.from_bytes(compensated[second_at:second_at + 4], "little")
        compensated[SUMS_OFFSET:SUMS_OFFSET + 4] = ((first + 1) % MODULUS).to_bytes(4, "little")
        compensated[second_at:second_at + 4] = ((second - 1) % MODULUS).to_bytes(4, "little")
        altered = work / f"bad-{count}-compensated-sums.bin"
        altered.write_bytes(compensated)
        verify_rejects(verifier, altered, statement)
        header_end = SUMS_OFFSET + 16 * (1 + 2 * count)
        for label, data in (
            ("truncated-header", raw[:header_end - 1]),
            ("truncated-postcard", raw[:-1]),
            ("trailing-postcard", raw + b"\x00"),
            ("malformed-postcard", raw[:header_end] + b"\xff" * 64),
            ("oversized-wire", raw + b"\x00" * ((16 << 20) + 1 - len(raw))),
        ):
            altered = work / f"bad-{count}-{label}.bin"
            altered.write_bytes(data)
            verify_rejects(verifier, altered, statement)
    malformed = work / f"malformed-{count}.json"
    malformed.write_text(json.dumps({**saved, "unknown_field": 1}))
    verify_rejects(verifier, proof, malformed)
    malformed.write_text(json.dumps(saved)[:-1] + ',"public_words":[0,0,0,0,0,0,0,0]}')
    verify_rejects(verifier, proof, malformed)
    noncanonical = {**saved, "public_words": saved["public_words"].copy()}
    noncanonical["public_words"][0] = MODULUS
    malformed.write_text(json.dumps(noncanonical))
    verify_rejects(verifier, proof, malformed)
    invalid = json.loads(assignment.read_text())
    invalid["private_inputs"]["x"][0] += 1
    wrong = work / f"wrong-{count}.json"
    wrong.write_text(json.dumps(invalid))
    run(str(prover), str(wrong), str(work / "bad.proof"), str(work / "bad.statement"), accept=False)
    invalid = json.loads(assignment.read_text())
    invalid["public_outputs"]["sum"][0] = (invalid["public_outputs"]["sum"][0] + 1) % MODULUS
    wrong.write_text(json.dumps(invalid))
    run(str(prover), str(wrong), str(work / "bad.proof"), str(work / "bad.statement"), accept=False)
    if count in (1, 3, 8):
        changed_source = work / "changed-source.s31.json"
        changed_source.write_bytes(source.read_bytes() + b" ")
        _, other_verifier, other_manifest_bin = build(changed_source, work / "changed-source")
        other_manifest = json.loads(run(str(other_manifest_bin)).stdout)
        assert other_manifest["source_sha256"] != manifest["source_sha256"]
        resealed = {**saved,
                    "source_sha256": other_manifest["source_sha256"],
                    "selected_manifest_sha256": other_manifest["manifest_sha256"],
                    "registry_manifest_sha256": other_manifest["registry_manifest_sha256"],
                    "circuit_identity_sha256": other_manifest["circuit_identity_sha256"]}
        malformed.write_text(json.dumps(resealed))
        verify_rejects(other_verifier, proof, malformed)
        resealed_proof = bytearray(raw)
        for field, offset in (
            ("source_sha256", len(MAGIC) + 4),
            ("registry_manifest_sha256", len(MAGIC) + 36),
            ("circuit_identity_sha256", len(MAGIC) + 68),
        ):
            resealed_proof[offset:offset + 32] = bytes.fromhex(resealed[field])
        resealed_path = work / f"bad-{count}-resealed-source.bin"
        resealed_path.write_bytes(resealed_proof)
        verify_rejects(other_verifier, resealed_path, malformed)
    return {"calls": count, "proof_bytes": len(raw), "proof_sha256": hashlib.sha256(raw).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--counts", nargs="+", type=int, default=list(range(1, 9)))
    args = parser.parse_args()
    if len(set(args.counts)) != len(args.counts) or any(not 1 <= count <= 8 for count in args.counts):
        parser.error("counts must be distinct values in 1..8")
    with tempfile.TemporaryDirectory(prefix="s31-mixed-general-") as directory:
        work = Path(directory)
        results = []
        for count in args.counts:
            print(f"checking {count}-call mixed profile", file=sys.stderr, flush=True)
            results.append(exercise(work, count))
        print(json.dumps({"schema": "s31-mixed-general-acceptance-v3",
                          "profiles": results, "accepted": True}, sort_keys=True))


if __name__ == "__main__":
    main()
