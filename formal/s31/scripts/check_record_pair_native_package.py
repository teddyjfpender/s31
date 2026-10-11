#!/usr/bin/env python3
"""Check a built direct-gate Pair package against the pinned Lean ABI fixture.

This reads a completed package and invokes its installed native prover in
`inspect` mode. It does not build Zig artifacts or verify a proof.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from abi.binding_v2 import binding_digest  # noqa: E402
from package.verify import verify_package  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")


def check(package: Path) -> dict[str, object]:
    package = package.resolve()
    manifest = verify_package(package)
    if manifest.get("lowering") != "direct-gate" or manifest.get("name") != "pair":
        raise ValueError("expected the pinned direct-gate pair package")
    source = (package / "source.s31").read_bytes()
    expected_source = (FORMAL / "fixtures/record_pair_alias_v2.s31").read_bytes()
    if source != expected_source:
        raise ValueError("package source differs from pinned record fixture")
    relation, _ = compile_text(source.decode("utf-8"))
    native_source = json.loads((package / "source.s31.json").read_bytes())
    if native_source != relation:
        raise ValueError("native package relation differs from source compiler export")
    descriptor = native_source["public_abi"]
    encoded = canonical(descriptor)
    with tempfile.TemporaryDirectory(prefix="s31-pair-package-abi-") as directory:
        descriptor_path = Path(directory) / "abi.json"
        descriptor_path.write_bytes(encoded)
        checked = subprocess.run(
            ["lake", "env", "lean", "--run", "S31/Audit/RecordPairAliasCheck.lean",
             str(package / "source.s31"), str(descriptor_path)],
            cwd=FORMAL, capture_output=True, text=True, check=False,
        )
        if checked.returncode != 0:
            raise ValueError("Lean source/ABI byte bridge rejected package: " + checked.stdout + checked.stderr)
    flat = {**native_source, "version": 1}
    del flat["public_abi"]
    digest = binding_digest(flat, descriptor)
    key = json.loads((package / "verification-key.json").read_bytes())
    published_abi = json.loads((package / "public-abi.json").read_bytes())
    if (published_abi.get("boundary") != descriptor or
            published_abi.get("boundary_sha256") != digest or
            key.get("public_abi_sha256") != digest):
        raise ValueError("published ABI or sealed key differs from pinned descriptor")
    prover = package / "bin/s31-pair-prover"
    inspected = subprocess.run([str(prover), "inspect"], capture_output=True, text=True, check=True)
    inspection = json.loads(inspected.stdout + inspected.stderr)
    if (inspection.get("public_abi_sha256") != digest or
            inspection.get("program_sha256") != key.get("program_sha256") or
            inspection.get("canonical_ir_sha256") != key.get("canonical_ir_sha256")):
        raise ValueError("live native compiler inspection differs from package key")
    return {
        "schema": "s31-record-pair-abi-lean-native-v1",
        "accepted": True,
        "boundary_sha256": digest,
        "public_word_count": 2,
        "source_relation_equal": True,
        "lean_exact_bytes_equal": True,
        "native_inspect_key_equal": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.package), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
