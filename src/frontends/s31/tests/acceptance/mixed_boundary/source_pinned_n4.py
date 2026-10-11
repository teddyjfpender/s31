#!/usr/bin/env python3
"""Black-box source-file controls for the experimental fixed mixed N=4 CLI."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
SOURCE = S31 / "examples/boundary/mixed_four.s31.json"
ASSIGNMENT = S31 / "examples/boundary/mixed_four.valid.json"
MAGIC = b"S31MIX06"
SUMS_OFFSET = len(MAGIC) + 4 + 32 * 3 + 8


def run(*args: str, accept: bool) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True, check=False)
    if (result.returncode == 0) != accept:
        raise AssertionError(
            f"unexpected exit {result.returncode} for {args}:\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result


def build(source: Path, prefix: Path, *, accept: bool = True) -> tuple[Path, Path, Path]:
    result = run(
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-mixed4",
        f"-Ds31-source={source}", "-Ds31-name=mixed_four", "-j1",
        "--prefix", str(prefix), accept=accept,
    )
    if not accept:
        assert "UnsupportedMixedProofCount" in result.stderr, result.stderr
    root = prefix / "bin"
    return (
        root / "s31-mixed_four-mixed4-prover",
        root / "s31-mixed_four-mixed4-native-verifier",
        root / "s31-mixed_four-mixed4-manifest",
    )


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-mixed-source-pinned-") as directory:
        work = Path(directory)
        prover, verifier, manifest_bin = build(SOURCE, work / "original")
        manifest = json.loads(run(str(manifest_bin), accept=True).stdout)
        assert manifest["schema"] == "s31-mixed-component-inspection-n4-v2"
        assert manifest["source_sha256"] == hashlib.sha256(SOURCE.read_bytes()).hexdigest()
        assert manifest["call_count"] == 4 and manifest["slot_count"] == 9
        assert [slot["source_kind"] for slot in manifest["slots"]] == [
            "bundled_circuit", "pair_chip", "pair_bridge", "pair_chip",
            "pair_bridge", "many_chip", "many_bridge", "many_chip", "many_bridge",
        ]
        assert [slot["claimed_sum_index"] for slot in manifest["slots"]] == list(range(9))
        assert manifest["tree_columns"] == [8, 80, 120, 8]
        assert [call["constant"] for call in manifest["calls"]] == [13, 14, 15, 16]

        proof = work / "proof.bin"
        statement = work / "statement.json"
        run(str(prover), str(ASSIGNMENT), str(proof), str(statement), accept=True)
        run(str(verifier), str(proof), str(statement), accept=True)
        bad_witness = json.loads(ASSIGNMENT.read_text())
        bad_witness["private_inputs"]["x"][0] += 1
        wrong_assignment = work / "wrong-assignment.json"
        wrong_assignment.write_text(json.dumps(bad_witness))
        run(str(prover), str(wrong_assignment), str(work / "wrong-witness.proof"),
            str(work / "wrong-witness.statement.json"), accept=False)
        bad_output = json.loads(ASSIGNMENT.read_text())
        bad_output["public_outputs"]["sum"][0] += 1
        wrong_assignment.write_text(json.dumps(bad_output))
        run(str(prover), str(wrong_assignment), str(work / "wrong-output.proof"),
            str(work / "wrong-output.statement.json"), accept=False)
        public = json.loads(statement.read_text())
        raw = proof.read_bytes()
        assert len(raw) == 110_020
        assert hashlib.sha256(raw).hexdigest() == "408ff6a32b9374ea92a8a086ffc4b2ef0114749a2f9b2a09b4e5adb9b849aade"
        assert public["schema"] == "s31-mixed-public-words-n4-v2"
        assert len(public["public_words"]) == 8
        assert raw[:len(MAGIC) + 4] == MAGIC + bytes((4, 9, 2, 0))
        for field, offset in (
            ("source_sha256", len(MAGIC) + 4),
            ("manifest_sha256", len(MAGIC) + 36),
            ("circuit_identity_sha256", len(MAGIC) + 68),
        ):
            assert public[field] == manifest[field]
            assert raw[offset:offset + 32].hex() == manifest[field]

        changed = dict(public)
        changed["public_words"] = public["public_words"].copy()
        changed["public_words"][0] += 1
        wrong_statement = work / "wrong-statement.json"
        wrong_statement.write_text(json.dumps(changed))
        run(str(verifier), str(proof), str(wrong_statement), accept=False)
        for field, value in (
            ("schema", "s31-many-public-words-v4"),
            ("source_sha256", "0" * 64),
            ("manifest_sha256", "0" * 64),
            ("circuit_identity_sha256", "0" * 64),
        ):
            changed = {**public, field: value}
            wrong_statement.write_text(json.dumps(changed))
            run(str(verifier), str(proof), str(wrong_statement), accept=False)
        wrong_statement.write_text(json.dumps(public)[:-1] + ',"public_words":[0,0,0,0,0,0,0,0]}')
        run(str(verifier), str(proof), str(wrong_statement), accept=False)
        wrong_statement.write_text(json.dumps({**public, "unknown_field": 1}))
        run(str(verifier), str(proof), str(wrong_statement), accept=False)
        noncanonical = {**public, "public_words": public["public_words"].copy()}
        noncanonical["public_words"][0] = 2_147_483_647
        wrong_statement.write_text(json.dumps(noncanonical))
        run(str(verifier), str(proof), str(wrong_statement), accept=False)

        for name, offset in (
            ("magic", 0), ("count", len(MAGIC)),
            ("roster", len(MAGIC) + 1), ("schema", len(MAGIC) + 2),
            ("source", len(MAGIC) + 4), ("manifest", len(MAGIC) + 36),
            ("identity", len(MAGIC) + 68),
            *((f"sum{i}", SUMS_OFFSET + 16 * i) for i in range(9)),
            ("proof_tail", len(raw) - 1),
        ):
            altered = bytearray(raw)
            altered[offset] ^= 1
            wrong_proof = work / f"wrong-{name}.bin"
            wrong_proof.write_bytes(altered)
            run(str(verifier), str(wrong_proof), str(statement), accept=False)
        run(str(verifier), str(proof), str(statement), "attacker-key.json", accept=False)

        changed_source = work / "changed-source.s31.json"
        changed_source.write_bytes(SOURCE.read_bytes() + b" ")
        _, other_verifier, other_manifest_bin = build(changed_source, work / "changed-source")
        other_manifest = json.loads(run(str(other_manifest_bin), accept=True).stdout)
        assert other_manifest["source_sha256"] != manifest["source_sha256"]
        resealed_statement = {**public, **{
            field: other_manifest[field] for field in (
                "source_sha256", "manifest_sha256", "circuit_identity_sha256")
        }}
        wrong_statement.write_text(json.dumps(resealed_statement))
        run(str(other_verifier), str(proof), str(wrong_statement), accept=False)

        unsupported_source = work / "three-calls.s31.json"
        three_calls = json.loads(SOURCE.read_text())
        three_calls["nodes"] = [
            *three_calls["nodes"][:3],
            {"name": "sum", "op": "add", "lhs": "r2", "rhs": "x"},
            {"name": "product", "op": "mul", "lhs": "r2", "rhs": "x"},
        ]
        unsupported_source.write_text(json.dumps(three_calls))
        build(unsupported_source, work / "unsupported", accept=False)

        print(json.dumps({
            "schema": "s31-mixed-source-pinned-acceptance-n4-v2",
            "source_sha256": manifest["source_sha256"],
            "manifest_sha256": manifest["manifest_sha256"],
            "proof_bytes": len(raw),
            "controls": 30,
            "accepted": True,
        }, sort_keys=True))


if __name__ == "__main__":
    main()
