#!/usr/bin/env python3
"""Exercise the Lean record-v2 source assignment checker on real text packages."""

from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

from check_record_v2_source_correspondence import ROOT, SOURCES, encode, package_files


ASSIGNMENTS = (
    {
        "public_inputs": {"_s31_abi_input_0": [2], "_s31_abi_input_1": [3]},
        "private_inputs": {"_s31_abi_input_2": [4], "_s31_abi_input_3": [5]},
        "public_outputs": {"z": [10], "_s31_abi_input_1": [3]},
    },
    {
        "public_inputs": {f"_s31_abi_input_{i}": [value]
                          for i, value in enumerate((2, 3, 4, 5))},
        "private_inputs": {},
        "public_outputs": {"p": [5], "_s31_abi_input_1": [3],
                           "q": [20], "_s31_abi_input_3": [5]},
    },
    {
        "public_inputs": {f"_s31_abi_input_{i}": [value]
                          for i, value in enumerate((2, 3, 7))},
        "private_inputs": {f"_s31_abi_input_{i}": [value]
                           for i, value in enumerate((4, 5, 6), start=3)},
        "public_outputs": {"p": [9], "_s31_abi_input_2": [7]},
    },
)

EXPECTED = (
    "source results [10, 3]; public words [2, 3, 10, 3, 0, 0, 0, 0]",
    "source results [5, 3, 20, 5]; public words [2, 3, 4, 5, 5, 3, 20, 5]",
    "source results [9, 9, 7]; public words [2, 3, 7, 9, 7, 0, 0, 0]",
)


def run_case(index: int, assignment: dict[str, object], expected: str | None,
             *, canonical: bool = True) -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-v2-assignment-") as directory:
        folder = Path(directory)
        for name, data in package_files(SOURCES[index]).items():
            (folder / name).write_bytes(data)
        encoded = encode(assignment)
        if not canonical:
            encoded = encoded.rstrip(b"\n")
        (folder / "assignment.json").write_bytes(encoded)
        command = ["lake", "env", "lean", "--run",
                   "S31/Audit/GeneralRecordV2ProgramAdmissionCheck.lean",
                   *(str(folder / name) for name in
                     ("source.s31", "typed-structural-derivation.json",
                      "source.s31.json", "public-abi.json")),
                   "--assignment", str(folder / "assignment.json")]
        result = subprocess.run(command, cwd=ROOT / "formal/s31", check=False,
                                capture_output=True, text=True, timeout=30)
        if expected is None:
            if result.returncode == 0 or "rejected:" not in result.stderr:
                raise AssertionError(f"case {index}: expected rejection: {result}")
        elif result.returncode != 0 or expected not in result.stdout:
            raise AssertionError(f"case {index}: expected {expected!r}: {result}")


def main() -> None:
    for index, assignment in enumerate(ASSIGNMENTS):
        run_case(index, assignment, EXPECTED[index])
    changed_private = {**ASSIGNMENTS[0], "private_inputs":
                       {"_s31_abi_input_2": [4], "_s31_abi_input_3": [6]}}
    run_case(0, changed_private, None)
    extra_output = {**ASSIGNMENTS[2], "public_outputs":
                    {**ASSIGNMENTS[2]["public_outputs"], "extra": [1]}}
    run_case(2, extra_output, None)
    run_case(0, ASSIGNMENTS[0], None, canonical=False)
    print("record-v2 source assignment checker: 3 accepted, 3 rejected")


if __name__ == "__main__":
    main()
