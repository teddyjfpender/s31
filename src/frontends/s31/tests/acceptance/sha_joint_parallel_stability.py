#!/usr/bin/env python3
"""Repeat one sealed SHA proof to catch shared scratch allocator races."""

import argparse
import json
import subprocess
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parents[2]
ASSIGNMENT = HERE / "examples/bitcoin/bitcoin_header_pow.valid.json"


def run(*args: Path | str) -> None:
    result = subprocess.run([str(arg) for arg in args], capture_output=True, text=True)
    if result.returncode:
        raise AssertionError(f"command failed: {args}\n{result.stdout}{result.stderr}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--joint-package", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=64)
    args = parser.parse_args()
    if args.iterations < 1:
        parser.error("--iterations must be positive")
    package = args.joint_package.resolve()
    cost = json.loads((package / "cost-report.json").read_text())
    if not cost["profile"].startswith("sha-joint"):
        raise AssertionError("expected a sha-joint package")
    assignment = json.loads(ASSIGNMENT.read_text())
    statement = {
        "public_inputs": assignment["public_inputs"],
        "public_outputs": assignment["public_outputs"],
    }
    with tempfile.TemporaryDirectory(prefix="s31-sha-joint-repeat-") as directory:
        root = Path(directory)
        statement_path = root / "statement.json"
        statement_path.write_text(json.dumps(statement, sort_keys=True))
        proof = root / "proof.bin"
        prover = package / "bin/s31-bitcoin_header_pow-prover"
        verifier = package / "bin/s31-bitcoin_header_pow-native-verifier"
        key = package / "verification-key.json"
        for index in range(args.iterations):
            try:
                run(prover, "prove", ASSIGNMENT, proof)
                run(verifier, proof, statement_path, key)
            except AssertionError as exc:
                raise AssertionError(f"iteration {index + 1}/{args.iterations}: {exc}") from exc
    print(json.dumps({"schema": "s31-sha-joint-parallel-stability-v1",
                      "iterations": args.iterations, "proved_and_verified": args.iterations},
                     sort_keys=True))


if __name__ == "__main__":
    main()
