#!/usr/bin/env python3
"""Interleaved, same-binary diagnostic for the mixed prover's PoW worker count.

The source, assignment, claimed public statement, binaries and security
parameters are identical for every trial.  The only changed input is
STWO_ZIG_POW_WORKERS.  Every emitted proof is checked by the native verifier.
This measures whole native prove time, which also contains non-PoW work; it
does not by itself isolate the interaction and FRI grinders.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args: list[str], env: dict[str, str]) -> tuple[int, bytes, bytes, int]:
    start = time.monotonic_ns()
    result = subprocess.run(args, env=env, capture_output=True, check=False)
    return result.returncode, result.stdout, result.stderr, time.monotonic_ns() - start


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--shapes", nargs="+", default=["control_n2", "control_n6"])
    parser.add_argument("--workers", nargs="+", type=int, default=[1, 4, 8, 16])
    parser.add_argument("--rounds", type=int, default=4)
    parser.add_argument("--out", type=Path, required=True)
    options = parser.parse_args()
    if options.rounds < 1 or len(set(options.workers)) != len(options.workers) or any(n < 1 or n > 64 for n in options.workers):
        parser.error("rounds must be positive and workers must be distinct integers in 1..64")
    options.out.mkdir(parents=True, exist_ok=False)
    meta = {"schema": "s31-mixed-pow-workers-diagnostic-v1", "workers": options.workers, "rounds": options.rounds, "shapes": []}
    records = []
    env = os.environ.copy()
    for shape in options.shapes:
        package = options.package_root / shape
        binary_dir = package / "mixed" / "bin"
        prover, = binary_dir.glob("*-mixed-general-prover")
        verifier, = binary_dir.glob("*-mixed-general-native-verifier")
        assignment = package / "assignment-00.json"
        statement = package / "statement-00.json"
        build = json.loads((package / "build.json").read_text())
        binaries = {"prover": digest(prover), "verifier": digest(verifier)}
        if any(binaries[k] != build["binary_sha256"][k] for k in binaries):
            raise RuntimeError(f"{shape}: binary differs from frozen build record")
        meta["shapes"].append({"name": shape, "source_sha256": digest(package / "source.s31.json"), "assignment_sha256": digest(assignment), "statement_sha256": digest(statement), "binary_sha256": binaries})
        previous_proof_hash = None
        changed_claim_checked = False
        for round_id in range(options.rounds):
            # Rotate the worker order each round to reduce thermal/order bias.
            for workers in options.workers[round_id % len(options.workers):] + options.workers[:round_id % len(options.workers)]:
                proof = options.out / f"{shape}-r{round_id}-w{workers}.proof"
                emitted_statement = options.out / f"{shape}-r{round_id}-w{workers}.statement.json"
                env["STWO_ZIG_POW_WORKERS"] = str(workers)
                rc, stdout, stderr, prover_wall_ns = run([str(prover), str(assignment), str(proof), str(emitted_statement), str(statement)], env)
                if rc or not proof.is_file() or not emitted_statement.is_file():
                    raise RuntimeError(f"{shape} r{round_id} w{workers}: prover failed ({rc}): {stderr.decode(errors='replace')}")
                if emitted_statement.read_bytes() != statement.read_bytes():
                    raise RuntimeError(f"{shape} r{round_id} w{workers}: changed public statement")
                stage_lines = [line for line in stderr.decode().splitlines() if line.startswith("S31_MIXED_STAGE_V1 ")]
                if len(stage_lines) != 1:
                    raise RuntimeError(f"{shape} r{round_id} w{workers}: missing/duplicate stage line")
                stage = json.loads(stage_lines[0].split(" ", 1)[1])
                rc, verify_stdout, verify_stderr, verifier_wall_ns = run([str(verifier), str(proof), str(statement)], env)
                if rc or b"verified" not in verify_stderr:
                    raise RuntimeError(f"{shape} r{round_id} w{workers}: verifier rejected ({rc}): {verify_stderr.decode(errors='replace')}")
                proof_hash = digest(proof)
                if previous_proof_hash is not None and proof_hash != previous_proof_hash:
                    raise RuntimeError(f"{shape} r{round_id} w{workers}: canonical proof bytes changed with worker count")
                previous_proof_hash = proof_hash
                if not changed_claim_checked:
                    changed = json.loads(statement.read_text())
                    # The frozen transfer corpus uses ABI v2. Keep its source
                    # ABI digest and all fields intact, changing one result.
                    if changed.get("version") != 2 or not changed.get("leaves"):
                        raise RuntimeError(f"{shape}: expected version-2 public record")
                    words = changed["leaves"][-1]["words"]
                    words[0] = (words[0] + 1) % 2147483647
                    changed_path = options.out / f"{shape}.changed-statement.json"
                    changed_path.write_text(json.dumps(changed, sort_keys=True, separators=(",", ":")) + "\n")
                    bad_rc, _, bad_stderr, _ = run([str(verifier), str(proof), str(changed_path)], env)
                    if bad_rc == 0 or b"InvalidRecordStatement" in bad_stderr:
                        raise RuntimeError(f"{shape}: changed public result was not rejected after ABI admission: {bad_stderr.decode(errors='replace')}")
                    changed_path.unlink()
                    changed_claim_checked = True
                records.append({"shape": shape, "round": round_id, "workers": workers, "prover_wall_ns": prover_wall_ns, "verifier_wall_ns": verifier_wall_ns, "native_prove_including_setup_ns": stage["stages_ns"]["native_prove_including_setup_ns"], "proof_bytes": proof.stat().st_size, "proof_sha256": proof_hash, "native_verifier_accepted": True})
                print(f"{shape} round={round_id} workers={workers} native_ms={records[-1]['native_prove_including_setup_ns'] / 1e6:.2f}", flush=True)
                proof.unlink()
                emitted_statement.unlink()
        meta["shapes"][-1]["changed_public_result_rejected"] = changed_claim_checked
    result = {"metadata": meta, "records": records}
    (options.out / "diagnostic.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
