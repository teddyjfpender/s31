#!/usr/bin/env python3
"""Native regression for v1 prove and both v2 direct-gate verification modes.

Run only after the exclusive V8 measurement slot is released.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/paired_record_v2"))

import s31
from design import canonical, case, design


def command(*args: str, accept: bool = True) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(args, capture_output=True, text=True, check=False)
    if (completed.returncode == 0) != accept:
        raise AssertionError(f"unexpected exit {completed.returncode}: {args}\n"
                             f"{completed.stdout}{completed.stderr}")
    return completed


def main() -> None:
    cfg = design()
    source_bytes, assignment_bytes, typed_statement = case(1, 0, cfg)
    with tempfile.TemporaryDirectory(prefix="s31-paired-v2-regression-") as temporary:
        root = Path(temporary)
        v2_source = root / "record-v2.s31.json"
        v2_source.write_bytes(source_bytes)
        relation_v1 = json.loads(source_bytes)
        relation_v1["version"] = 1
        relation_v1.pop("public_abi")
        v1_source = root / "record-v1.s31.json"
        v1_source.write_bytes(canonical(relation_v1))
        assignment = root / "assignment.json"
        assignment.write_bytes(assignment_bytes)
        flat_statement = root / "flat-statement.json"
        supplied = json.loads(assignment_bytes)
        flat_statement.write_bytes(canonical({"public_inputs": supplied["public_inputs"],
                                             "public_outputs": supplied["public_outputs"]}))
        typed = root / "typed-statement.json"
        typed.write_bytes(typed_statement)

        for version, source, statement in ((1, v1_source, flat_statement),
                                           (2, v2_source, typed)):
            package = s31.build(source, root / f"package-v{version}", "direct-gate")
            manifest = s31.verify_package(package)
            if manifest["program_sha256"] != s31.file_hash(source):
                raise AssertionError("generic package accepted a different source")
            name = manifest["name"]
            prover = package / "bin" / f"s31-{name}-prover"
            verifier = package / "bin" / f"s31-{name}-native-verifier"
            key = package / "verification-key.json"
            modes = ("prove",) if version == 1 else ("prove", "prove-for-external-verification")
            for mode in modes:
                proof = root / f"v{version}-{mode}.proof"
                command(str(prover), mode, str(assignment), str(proof))
                command(str(verifier), str(proof), str(statement), str(key))
                if version == 2:
                    changed = json.loads(typed_statement)
                    changed["leaves"][0]["words"][0] = (changed["leaves"][0]["words"][0] + 1) % ((1 << 31) - 1)
                    bad = root / "changed-typed.json"
                    bad.write_bytes(canonical(changed))
                    command(str(verifier), str(proof), str(bad), str(key), accept=False)

        mismatch = command("zig", "build", "--build-file", str(S31 / "build.zig"),
                           "install", "-Doptimize=ReleaseFast", "-Ds31-version=2",
                           "-Ds31-lowering=direct-gate", f"-Ds31-source={v1_source}",
                           "--prefix", str(root / "wrong-version"), accept=False)
        if "-Ds31-version differs from embedded record source version" not in mismatch.stderr:
            raise AssertionError("record build version mismatch failed for the wrong reason")
        print(json.dumps({"schema": "s31-paired-record-v2-generic-native-regression",
                          "v1_self_verified": True, "v2_self_verified": True,
                          "v2_external_verified": True, "changed_typed_claim_rejected": True},
                         sort_keys=True))


if __name__ == "__main__":
    main()
