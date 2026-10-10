#!/usr/bin/env python3
"""Admit an S31 package against digests obtained from a separate trust root.

The pins must come from a trusted channel. Reading them from the package's own
manifest would make this check circular. Both executable binaries are pinned:
the prover receives private witness data and the verifier decides acceptance.
This command only checks files; it does not run either binary or authenticate
the issuer of the pins.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / "src/frontends/s31/python"))

from package.verify import verify_package  # noqa: E402

PIN_RE = re.compile(r"[0-9a-f]{64}\Z")
NAME_RE = re.compile(r"[A-Za-z0-9_-]+\Z")


def pinned_paths(package: Path) -> dict[str, Path]:
    manifest = json.loads((package / "manifest.json").read_text())
    name = manifest.get("name")
    if not isinstance(name, str) or not NAME_RE.fullmatch(name):
        raise ValueError("invalid package name for pinned verifier")
    return {
        "source": package / "source.s31.json",
        "key": package / "verification-key.json",
        "prover": package / "bin" / f"s31-{name}-prover",
        "verifier": package / "bin" / f"s31-{name}-native-verifier",
    }


def check_pinned_package(package: Path, pins: dict[str, str]) -> dict[str, str]:
    """Check external exact-byte pins, then package-internal consistency.

    Callers must supply all four pins independently of the package being
    checked. This does not pin the trusted local Python checker itself.
    """
    if set(pins) != {"source", "key", "prover", "verifier"}:
        raise ValueError("source, key, prover, and verifier pins are all required")
    if any(not isinstance(digest, str) or not PIN_RE.fullmatch(digest)
           for digest in pins.values()):
        raise ValueError("pins must be lowercase SHA-256 hex digests")
    paths = pinned_paths(package)
    actual: dict[str, str] = {}
    package_root = package.resolve(strict=True)
    for kind, path in paths.items():
        if path.is_symlink() or not path.resolve(strict=True).is_relative_to(package_root):
            raise ValueError(f"pinned {kind} is a symlink or escapes the package")
        actual[kind] = hashlib.sha256(path.read_bytes()).hexdigest()
        if not hmac.compare_digest(actual[kind], pins[kind]):
            raise ValueError(f"pinned {kind} digest mismatch")
    verify_package(package)
    return actual


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--key-sha256", required=True)
    parser.add_argument("--prover-sha256", required=True)
    parser.add_argument("--verifier-sha256", required=True)
    args = parser.parse_args()
    try:
        actual = check_pinned_package(args.package, {
            "source": args.source_sha256,
            "key": args.key_sha256,
            "prover": args.prover_sha256,
            "verifier": args.verifier_sha256,
        })
    except (ValueError, OSError, KeyError, TypeError, RuntimeError,
            UnicodeError, json.JSONDecodeError) as exc:
        print(f"pinned package rejected: {exc}", file=sys.stderr)
        return 1
    print(json.dumps({"accepted": True, "sha256": actual}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
