#!/usr/bin/env python3
"""Check all case07 native Gate multiplicities from addresses, not mults.

The pinned diagnostic is an unauthenticated fixture. This check demonstrates
nonvacuity of Lean's schedule-read-count rule on the native 512-row export;
it does not establish PCS opening correspondence.
"""

from __future__ import annotations

from collections import Counter
import copy
import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixtures/case07-full-native-roster.json"
FIXTURE_SHA256 = "64328f7ea1cbd817c3a719489791aaedbc7b17829f2d241ede44a2f354ead234"
FEEDERS = list(range(2, 11))


def derived_counts_match(columns: list[list[int]]) -> bool:
    if len(columns) != 8 or any(len(column) != 512 for column in columns):
        return False
    outputs = columns[6]
    if len(set(outputs)) != 512:
        return False
    reads = Counter(columns[4] + columns[5] + FEEDERS)
    return all(mult == reads[address]
               for address, mult in zip(outputs, columns[7], strict=True))


def main() -> None:
    raw = FIXTURE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != FIXTURE_SHA256:
        raise AssertionError("case07 diagnostic bytes changed")
    columns = json.loads(raw)["physical"]["fixed_columns"]
    if not derived_counts_match(columns):
        raise AssertionError("native multiplicities differ from read counts")
    changed = copy.deepcopy(columns)
    changed[7][0] += 1
    if derived_counts_match(changed):
        raise AssertionError("changed multiplicity was accepted")
    print("case07: 512/512 source/schedule read counts match native mults; "
          "one changed multiplicity rejected")


if __name__ == "__main__":
    main()
