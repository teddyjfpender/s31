#!/usr/bin/env python3
"""Export and check the complete native 8×512 fixed Gate AIR columns.

The fixture is the native preprocessed circuit's column-major M31 words in
little-endian u32 form. It records fixed cells only: no main/interaction
witness, quotient, proof opening, or independent PCS authentication is implied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import struct
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(S31 / "python"))

import s31
from package.correspondence import (DIRECT_COLUMN_IDS, check_package,
                                    check_source_fixed_rows, gate_schedule,
                                    parse_source)

SOURCE = S31 / "examples/arithmetic/functional_square4_manual.s31"
FIXTURE = HERE / "square4-fixed-columns.json"
WORDS = HERE / "square4-fixed-columns.u32le"
FORMAL_ROWS = ROOT / "formal/s31/S31/Gadgets/Functional/TextSquare4Native.lean"
P = (1 << 31) - 1


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def native_fixture(package: Path) -> tuple[dict, bytes]:
    """Read native cells twice and verify their source, AIR and key bindings."""
    checked = check_package(package)
    manifest = json.loads((package / "manifest.json").read_bytes())
    if (manifest.get("lowering") != "direct-gate" or
        manifest.get("source_text_sha256") != sha(SOURCE.read_bytes()) or
        checked["source_sha256"] != sha(SOURCE.read_bytes())):
        raise ValueError("package is not the checked manual square4 source")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    exported = json.loads(s31.invoke(str(prover), "inspect-topology"))
    packaged = json.loads((package / "gate-topology.json").read_bytes())
    if exported != packaged:
        raise ValueError("fresh native topology differs from packaged topology")
    columns = exported.get("columns")
    if (not isinstance(columns, list) or len(columns) != 8 or
        [column.get("id") for column in columns] != list(DIRECT_COLUMN_IDS)):
        raise ValueError("native Gate fixed columns are missing or reordered")
    component = json.loads((package / "component-manifest.json").read_bytes())
    key = json.loads((package / "verification-key.json").read_bytes())
    cost = json.loads((package / "cost-report.json").read_bytes())
    if (cost.get("padded", {}).get("qm31_ops") != 512 or
        cost.get("preprocessed_cells") != 4096 or
        exported.get("preprocessed_root") != key.get("preprocessed_root") or
        exported.get("preprocessed_root") != component.get("preprocessed_root") or
        exported.get("program_sha256") != manifest.get("program_sha256")):
        raise ValueError("square4 fixed geometry or native root binding differs")
    encoded = bytearray()
    column_meta = []
    for index, (column, declared) in enumerate(
            zip(columns, component["preprocessed_columns"], strict=True)):
        values = column.get("values")
        if (not isinstance(values, list) or len(values) != 512 or
            any(type(word) is not int or not 0 <= word < P for word in values)):
            raise ValueError("native Gate fixed column has invalid M31 words")
        data = b"".join(struct.pack("<I", word) for word in values)
        digest = sha(data)
        if (declared.get("id") != column["id"] or
            declared.get("commitment_index") != index or
            declared.get("rows") != 512 or
            declared.get("values_sha256") != digest):
            raise ValueError("native fixed column differs from component manifest")
        column_meta.append({"id": column["id"], "index": index,
                            "byte_offset": len(encoded), "rows": 512,
                            "values_sha256": digest})
        encoded.extend(data)
    if len(encoded) != 8 * 512 * 4:
        raise ValueError("wrong complete fixed-column byte length")
    _, syntax = parse_source(SOURCE.read_bytes())
    rows = check_source_fixed_rows(syntax, exported, gate_schedule(syntax, cost))
    metadata = {
        "schema": "s31-direct-gate-square4-fixed-columns-v1",
        "source": SOURCE.relative_to(ROOT).as_posix(),
        "source_sha256": sha(SOURCE.read_bytes()),
        "program_sha256": manifest["program_sha256"],
        "preprocessed_root": exported["preprocessed_root"],
        "layout": "column-major little-endian u32; M31 canonical words",
        "rows_per_column": 512,
        "columns": column_meta,
        "gate_counts": {kind: len(exported[kind]) for kind in
                        ("add", "sub", "mul", "pointwise_mul")},
        "source_fixed_rows": rows,
        "binary": WORDS.name,
        "binary_bytes": len(encoded),
        "binary_sha256": sha(encoded),
        "scope": ("Native fixed/preprocessed cells only. Main and interaction "
                  "columns, quotient checks and PCS openings are outside this fixture."),
    }
    return metadata, bytes(encoded)


def fixture_bytes(metadata: dict) -> bytes:
    return (json.dumps(metadata, indent=2, sort_keys=True) + "\n").encode()


def read_fixture(metadata_path: Path = FIXTURE,
                 words_path: Path = WORDS) -> tuple[dict, list[tuple[int, ...]]]:
    """Decode and validate the small checked-in column-major snapshot."""
    metadata = json.loads(metadata_path.read_bytes())
    data = words_path.read_bytes()
    if (metadata.get("schema") != "s31-direct-gate-square4-fixed-columns-v1" or
        metadata.get("binary") != words_path.name or
        metadata.get("rows_per_column") != 512 or
        metadata.get("binary_bytes") != 16384 or len(data) != 16384 or
        metadata.get("binary_sha256") != sha(data)):
        raise ValueError("fixed-column fixture header or binary digest differs")
    declarations = metadata.get("columns")
    if (not isinstance(declarations, list) or len(declarations) != 8 or
        [entry.get("id") for entry in declarations] != list(DIRECT_COLUMN_IDS)):
        raise ValueError("fixed-column fixture order differs")
    columns = []
    for index, entry in enumerate(declarations):
        chunk = data[index * 2048:(index + 1) * 2048]
        values = struct.unpack("<512I", chunk)
        if (entry.get("index") != index or entry.get("byte_offset") != index * 2048 or
            entry.get("rows") != 512 or entry.get("values_sha256") != sha(chunk) or
            any(value >= P for value in values)):
            raise ValueError("fixed-column fixture cell or digest differs")
        columns.append(values)
    operation_names = ("add", "sub", "mul", "pointwise_mul")
    counts = dict.fromkeys(operation_names, 0)
    for row in range(512):
        flags = [column[row] for column in columns[:4]]
        if sum(flags) != 1 or any(flag not in (0, 1) for flag in flags):
            raise ValueError("fixed-column row has invalid operation selectors")
        counts[operation_names[flags.index(1)]] += 1
    if counts != metadata.get("gate_counts"):
        raise ValueError("fixed-column row partition differs from metadata")
    return metadata, columns


def read_formal_rows(path: Path = FORMAL_ROWS) -> list[tuple[int, ...]]:
    """Decode the separately generated Lean fixed-row literal exactly."""
    source = path.read_text()
    match = re.search(
        r"(?ms)^def paddedArithmeticFixedRows : List \(List Nat\) := \[\n"
        r"(.*?)^\]$", source,
    )
    if match is None:
        raise ValueError("formal fixed-row literal is missing")
    row_pattern = re.compile(r"\s*\[\s*" + r"\s*,\s*".join([r"(\d+)"] * 8)
                             + r"\s*\],?\s*")
    rows = []
    for line in match.group(1).splitlines():
        parsed = row_pattern.fullmatch(line)
        if parsed is None:
            raise ValueError("formal fixed-row literal has an invalid row")
        rows.append(tuple(map(int, parsed.groups())))
    if len(rows) != 512:
        raise ValueError(f"formal fixed-row literal has {len(rows)} rows, expected 512")
    return rows


def check_formal_rows(columns: list[tuple[int, ...]],
                      path: Path = FORMAL_ROWS) -> None:
    """Compare every independently exported physical fixed cell."""
    for row_index, row in enumerate(read_formal_rows(path)):
        for column_index, (formal_value, native_column) in enumerate(zip(row, columns,
                                                                        strict=True)):
            native_value = native_column[row_index]
            if formal_value != native_value:
                raise ValueError(
                    f"formal/native fixed cell mismatch at row {row_index}, "
                    f"column {DIRECT_COLUMN_IDS[column_index]}: "
                    f"formal {formal_value}, native {native_value}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("write", "check", "row"))
    parser.add_argument("--package", type=Path,
                        help="native package path; defaults to a compiler-fingerprinted cache")
    parser.add_argument("--row", type=int, help="0-based AIR row to inspect in row mode")
    args = parser.parse_args()
    if args.mode == "row":
        if args.row is None or not 0 <= args.row < 512:
            parser.error("row mode requires --row in 0..511")
        metadata, columns = read_fixture()
        print(json.dumps({"row": args.row,
                          "fixed_cells": {entry["id"]: columns[index][args.row]
                                          for index, entry in enumerate(metadata["columns"])}},
                         indent=2, sort_keys=True))
        return
    package_path = args.package or (ROOT / "zig-out/s31-direct-gate-release-cost" /
                                    f"square4-{s31.compiler_fingerprint()[:16]}")
    package = s31.build(SOURCE, package_path, "direct-gate")
    metadata, data = native_fixture(package)
    if args.mode == "write":
        WORDS.write_bytes(data)
        FIXTURE.write_bytes(fixture_bytes(metadata))
    elif WORDS.read_bytes() != data or FIXTURE.read_bytes() != fixture_bytes(metadata):
        raise ValueError("checked-in 8×512 fixed Gate fixture differs from native export")
    _, columns = read_fixture()
    if args.mode == "check":
        check_formal_rows(columns)
    print(f"{args.mode}: {len(metadata['columns'])} columns × "
          f"{metadata['rows_per_column']} rows, binary SHA256 {metadata['binary_sha256']}")


if __name__ == "__main__":
    main()
