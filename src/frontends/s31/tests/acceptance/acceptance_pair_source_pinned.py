#!/usr/bin/env python3
"""End-to-end controls for the experimental source-pinned two-call binaries."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
SOURCE = S31 / "examples/boundary/private_pair16_32.s31.json"
ASSIGNMENT = S31 / "examples/boundary/private_pair16_32.valid.json"


def run(*args: str, accept: bool) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True, check=False)
    if (result.returncode == 0) != accept:
        raise AssertionError(
            f"unexpected exit {result.returncode} for {args}:\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result


def build(source: Path, prefix: Path) -> tuple[Path, Path]:
    run(
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-pair",
        f"-Ds31-source={source}", "-Ds31-name=private_pair16_32",
        "--prefix", str(prefix), accept=True,
    )
    root = prefix / "bin"
    return (
        root / "s31-private_pair16_32-pair-prover",
        root / "s31-private_pair16_32-pair-native-verifier",
    )


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-pair-pinned-") as directory:
        work = Path(directory)
        prover, verifier = build(SOURCE, work / "original")
        proof = work / "proof.bin"
        statement = work / "statement.json"
        run(str(prover), str(ASSIGNMENT), str(proof), str(statement), accept=True)
        run(str(verifier), str(proof), str(statement), accept=True)

        value = json.loads(statement.read_text())
        assert value["schema"] == "s31-pair-public-words-v1"
        assert len(value["public_words"]) == 8
        wrong_words = {**value, "public_words": value["public_words"].copy()}
        wrong_words["public_words"][5] = (wrong_words["public_words"][5] + 1) % 2147483647
        wrong_claim = work / "wrong-claim.json"
        wrong_claim.write_text(json.dumps(wrong_words))
        run(str(verifier), str(proof), str(wrong_claim), accept=False)

        wrong_version = {**value, "schema": "s31-pair-public-words-v0"}
        wrong_schema = work / "wrong-schema.json"
        wrong_schema.write_text(json.dumps(wrong_version))
        run(str(verifier), str(proof), str(wrong_schema), accept=False)

        changed_proof = bytearray(proof.read_bytes())
        changed_proof[-1] ^= 1
        wrong_proof = work / "wrong-proof.bin"
        wrong_proof.write_bytes(changed_proof)
        run(str(verifier), str(wrong_proof), str(statement), accept=False)
        run(str(verifier), str(proof), str(statement), "attacker-key.json", accept=False)

        changed_source = work / "changed-source.s31.json"
        changed_source.write_bytes(SOURCE.read_bytes() + b"\n")
        _, other_verifier = build(changed_source, work / "changed-source")
        run(str(other_verifier), str(proof), str(statement), accept=False)

        print(json.dumps({
            "schema": "s31-pair-source-pinned-acceptance-v1",
            "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            "proof_bytes": proof.stat().st_size,
            "controls": ["honest", "wrong_public_word", "wrong_schema", "wrong_proof_byte",
                         "caller_key_argument", "changed_embedded_source"],
            "accepted": True,
        }, sort_keys=True))


if __name__ == "__main__":
    main()
