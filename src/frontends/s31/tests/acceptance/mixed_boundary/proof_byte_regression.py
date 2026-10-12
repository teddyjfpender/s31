#!/usr/bin/env python3
"""Compare two old-family proof receipts with a candidate proof receipt.

Each input is the JSON output of source_pinned_general.py. Run the old source
twice first: a nondeterministic baseline cannot serve as a byte lock.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def profiles(path: Path) -> list[tuple[int, int, str]]:
    receipt = json.loads(path.read_text())
    if receipt.get("schema") != "s31-mixed-general-acceptance-v3" or receipt.get("accepted") is not True:
        raise ValueError(f"{path}: invalid old-family acceptance receipt")
    entries = receipt.get("profiles")
    if not isinstance(entries, list) or len(entries) != 8:
        raise ValueError(f"{path}: expected eight call profiles")
    result = []
    for count, entry in enumerate(entries, 1):
        size, digest = entry.get("proof_bytes"), entry.get("proof_sha256")
        if entry.get("calls") != count or not isinstance(size, int) or size <= 0 or \
                not isinstance(digest, str) or len(digest) != 64:
            raise ValueError(f"{path}: invalid profile {count}")
        try:
            decoded = bytes.fromhex(digest)
        except ValueError as exc:
            raise ValueError(f"{path}: invalid SHA-256 for profile {count}") from exc
        if len(decoded) != 32:
            raise ValueError(f"{path}: invalid SHA-256 length for profile {count}")
        result.append((count, size, digest))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline_first", type=Path)
    parser.add_argument("baseline_repeat", type=Path)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    first = profiles(args.baseline_first)
    repeated = profiles(args.baseline_repeat)
    current = profiles(args.candidate)
    if first != repeated:
        raise SystemExit("old-family baseline changed between identical runs; byte lock is unavailable")
    if first != current:
        changed = [count for (count, size, sha), (_, other_size, other_sha)
                   in zip(first, current) if (size, sha) != (other_size, other_sha)]
        raise SystemExit(f"old-family proof bytes changed for call counts {changed}")
    print("old-family proof bytes unchanged for all eight call counts")


if __name__ == "__main__":
    main()
