#!/usr/bin/env python3
"""Independent package trust-boundary control; never edits the input package.

Run with an existing, valid S31 package. The regression gate requires the
forged public ABI and both externally pinned executable replacements to be
rejected. The self-hashed replacement observations remain true: an untrusted
package manifest cannot authenticate its own binaries.
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / "src/frontends/s31/python"))

from package.context import file_hash  # noqa: E402
from package.verify import verify_package  # noqa: E402
from pinned_package import check_pinned_package, pinned_paths  # noqa: E402


def accepted(package: Path) -> bool:
    try:
        verify_package(package)
    except ValueError:
        return False
    return True


def rewrite_manifest_hash(package: Path, artifact: str) -> None:
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["artifacts"][artifact] = file_hash(package / artifact)
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")


def probe_abi(source: Path, work: Path) -> bool:
    package = work / "forged-abi"
    shutil.copytree(source, package)
    path = package / "public-abi.json"
    forged = json.loads(path.read_text())
    forged["public_outputs"] = [
        {"name": "forged_authorized_result", "kind": "m31", "length": 1}
    ]
    path.write_text(json.dumps(forged, indent=2, sort_keys=True) + "\n")
    rewrite_manifest_hash(package, "public-abi.json")
    return accepted(package)


def probe_binary(source: Path, work: Path) -> bool:
    package = work / "forged-verifier"
    shutil.copytree(source, package)
    manifest = json.loads((package / "manifest.json").read_text())
    artifact = f"bin/s31-{manifest['name']}-native-verifier"
    path = package / artifact
    path.write_text("#!/bin/sh\nexit 0\n")
    path.chmod(0o755)
    rewrite_manifest_hash(package, artifact)
    return accepted(package)


def probe_prover(source: Path, work: Path) -> bool:
    package = work / "forged-prover"
    shutil.copytree(source, package)
    manifest = json.loads((package / "manifest.json").read_text())
    artifact = f"bin/s31-{manifest['name']}-prover"
    path = package / artifact
    path.write_text("#!/bin/sh\necho altered-prover\n")
    path.chmod(0o755)
    rewrite_manifest_hash(package, artifact)
    return accepted(package)


def wrong_pin_accepted(package: Path, pins: dict[str, str], kind: str) -> bool:
    changed = dict(pins)
    changed[kind] = ("0" if pins[kind][0] != "0" else "1") + pins[kind][1:]
    try:
        check_pinned_package(package, changed)
    except ValueError:
        return False
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="existing valid S31 package")
    parser.add_argument("--observe", action="store_true", help="report the ABI result without enforcing its rejection")
    args = parser.parse_args()
    package = args.package.resolve()
    verify_package(package)
    pins = {kind: file_hash(path) for kind, path in pinned_paths(package).items()}
    check_pinned_package(package, pins)
    wrong_pins = {kind: wrong_pin_accepted(package, pins, kind) for kind in pins}
    with tempfile.TemporaryDirectory(prefix="s31-package-trust-probe-") as temporary:
        work = Path(temporary)
        abi = probe_abi(package, work)
        binary = probe_binary(package, work)
        prover = probe_prover(package, work)
        try:
            check_pinned_package(work / "forged-verifier", pins)
            pinned_binary_accepted = True
        except ValueError:
            pinned_binary_accepted = False
        try:
            check_pinned_package(work / "forged-prover", pins)
            pinned_prover_accepted = True
        except ValueError:
            pinned_prover_accepted = False
    print(json.dumps({"forged_abi_accepted": abi,
                      "replaced_verifier_accepted": binary,
                      "replaced_prover_accepted": prover,
                      "pinned_replaced_verifier_accepted": pinned_binary_accepted,
                      "pinned_replaced_prover_accepted": pinned_prover_accepted,
                      "wrong_pin_accepted": wrong_pins}, sort_keys=True))
    if not args.observe and abi:
        print("public ABI was not derived from the sealed source", file=sys.stderr)
        return 1
    if pinned_binary_accepted:
        print("externally pinned verifier was replaced", file=sys.stderr)
        return 1
    if pinned_prover_accepted:
        print("externally pinned prover was replaced", file=sys.stderr)
        return 1
    if any(wrong_pins.values()):
        print("incorrect external digest was accepted", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
