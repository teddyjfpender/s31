#!/usr/bin/env python3
"""Black-box controls for the experimental source-pinned V4 native binaries."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
SOURCE = S31 / "examples/boundary/private_many1.s31.json"
ASSIGNMENT = S31 / "examples/boundary/private_many1.valid.json"
MAGIC = b"S31MNY04"
SUMS_OFFSET = len(MAGIC) + 1 + 1 + 2 + 32 * 3 + 8


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
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-many",
        f"-Ds31-source={source}", "-Ds31-name=private_many1",
        "--prefix", str(prefix), accept=True,
    )
    root = prefix / "bin"
    return root / "s31-private_many1-many-prover", root / "s31-private_many1-many-native-verifier"


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-many-pinned-") as directory:
        work = Path(directory)
        prover, verifier = build(SOURCE, work / "original")
        proof = work / "proof.bin"
        statement = work / "statement.json"
        run(str(prover), str(ASSIGNMENT), str(proof), str(statement), accept=True)
        run(str(verifier), str(proof), str(statement), accept=True)
        public = json.loads(statement.read_text())
        assert public["schema"] == "s31-many-public-words-v4"
        assert len(public["public_words"]) == 8

        changed = dict(public)
        changed["public_words"] = public["public_words"].copy()
        changed["public_words"][0] += 1
        wrong_statement = work / "wrong-statement.json"
        wrong_statement.write_text(json.dumps(changed))
        run(str(verifier), str(proof), str(wrong_statement), accept=False)
        changed["schema"] = "s31-pair-public-words-v1"
        wrong_statement.write_text(json.dumps(changed))
        run(str(verifier), str(proof), str(wrong_statement), accept=False)

        raw = proof.read_bytes()
        assert raw.startswith(MAGIC) and raw[len(MAGIC):len(MAGIC) + 2] == bytes((1, 3))
        for name, offset in (
            ("magic", 0), ("count", len(MAGIC)),
            ("roster", len(MAGIC) + 1), ("reserved", len(MAGIC) + 2),
            ("source", len(MAGIC) + 4), ("manifest", len(MAGIC) + 36),
            ("identity", len(MAGIC) + 68),
            ("sum0", SUMS_OFFSET), ("sum1", SUMS_OFFSET + 16),
            ("sum2", SUMS_OFFSET + 32), ("proof_tail", len(raw) - 1),
        ):
            altered = bytearray(raw)
            altered[offset] ^= 1
            wrong_proof = work / f"wrong-{name}.bin"
            wrong_proof.write_bytes(altered)
            run(str(verifier), str(wrong_proof), str(statement), accept=False)

        changed_source = work / "changed-source.s31.json"
        changed_source.write_bytes(SOURCE.read_bytes() + b" ")
        _, other_verifier = build(changed_source, work / "changed-source")
        run(str(other_verifier), str(proof), str(statement), accept=False)

        print(json.dumps({
            "schema": "s31-many-source-pinned-acceptance-v4",
            "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            "proof_bytes": len(raw),
            "controls": 15,
            "accepted": True,
        }, sort_keys=True))


if __name__ == "__main__":
    main()
