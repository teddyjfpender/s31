"""Bounded structural graph to direct-Gate physical-column correspondence.

The caller must first run the Lean statement gate and ``check_graph`` on the
same source, assignment, and graph bytes. This module checks exact cell
equality; a separate native verifier and commitment-root comparison are
required to connect the cells to an accepted proof. It is not a PCS theorem.
"""

from __future__ import annotations

import hashlib
import struct

P = (1 << 31) - 1
ROWS = 512


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("structural committed AIR join: " + reason)


def columns_bytes(columns: object, width: int) -> bytes:
    require(type(columns) is list and len(columns) == width,
            "column count differs")
    require(all(type(column) is list and len(column) == ROWS for column in columns),
            "column height differs")
    words = bytearray()
    for column in columns:
        for word in column:
            require(type(word) is int and 0 <= word < P,
                    "noncanonical column word")
            words.extend(struct.pack("<I", word))
    return bytes(words)


def expected_columns(graph: dict) -> tuple[list[list[int]], list[list[int]]]:
    """Project every direct-Gate fixed and base cell from checked graph data.

    This admits the 512-row transparent, permutation-free Gate-only
    arithmetic fragment. The all-public caller may export actual columns;
    private callers must compare them inside a noninstalled audit executable.
    Other profiles and trace heights fail closed.
    """
    padded = graph["padded"]
    require(not padded["permutation_inputs"] and
            not padded["permutation_outputs"] and
            not padded["permutation_ends"] and not graph["eq"],
            "permutation or equality component is outside this join")
    rows = padded["qm31_rows"]
    values = padded["values"]
    require(type(rows) is list and len(rows) == ROWS and
            type(values) is list and len(values) == padded["n_vars"],
            "bounded row or variable shape differs")
    # The structural exporter checks the full eleven-component padContext
    # roster. The installed direct-Gate preprocessor keeps only QM31 rows;
    # padding Eq/XOR/conversion/Blake rows must contribute no Gate uses. Its
    # first seven fixed columns are unchanged, but multiplicity is rebuilt
    # from active QM31 reads plus the public output roster.
    uses = [0] * len(values)
    for row in rows:
        require(type(row) is list and len(row) == 8 and
                all(type(address) is int and 0 <= address < len(values)
                    for address in row[4:7]),
                "fixed row address exceeds direct profile")
        uses[row[4]] += 1
        uses[row[5]] += 1
    for address in padded["output"]:
        require(type(address) is int and 0 <= address < len(values),
                "public output address exceeds direct profile")
        uses[address] += 1
    require(all(count < P for count in uses),
            "direct Gate multiplicity exceeds M31")
    fixed = [[0] * ROWS for _ in range(8)]
    main = [[0] * ROWS for _ in range(12)]
    for index, row in enumerate(rows):
        require(type(row) is list and len(row) == 8 and
                all(type(word) is int and 0 <= word < P for word in row) and
                sum(row[:4]) == 1 and all(flag in (0, 1) for flag in row[:4]),
                "fixed row is malformed")
        for column, word in enumerate(row):
            fixed[column][index] = word
        fixed[7][index] = uses[row[6]]
        for offset, address in ((0, row[4]), (4, row[5]), (8, row[6])):
            require(address < len(values) and type(values[address]) is list and
                    len(values[address]) == 4, "base row address differs")
            for lane, word in enumerate(values[address]):
                require(type(word) is int and 0 <= word < P,
                        "base row has noncanonical M31 coordinate")
                main[offset + lane][index] = word
    require(sorted(fixed[6]) == list(range(ROWS)),
            "fixed rows do not uniquely produce each address")
    return fixed, main


def check_columns(graph: dict, physical: dict, root_report: dict,
                  program_sha256: str, public_words: list[int]) -> dict:
    """Compare native ``writeBase`` export to all checked graph-derived cells."""
    require(physical.get("schema") == "s31-direct-gate-public-functional-physical-v1" and
            root_report.get("schema") == "s31-direct-gate-public-main-root-v1" and
            physical.get("program_sha256") == program_sha256 and
            root_report.get("program_sha256") == program_sha256 and
            physical.get("public_words") == public_words and
            root_report.get("public_words") == public_words,
            "physical source or public-claim identity differs")
    fixed, main = expected_columns(graph)
    require(columns_bytes(physical.get("fixed_columns"), 8) == columns_bytes(fixed, 8),
            "native fixed cells differ from checked structural graph")
    encoded = columns_bytes(main, 12)
    require(columns_bytes(physical.get("main_columns"), 12) == encoded,
            "native base cells differ from checked structural graph")
    digest = hashlib.sha256(encoded).hexdigest()
    require(root_report.get("main_columns_sha256") == digest,
            "native base-column digest differs")
    return {"fixed_columns": fixed, "main_columns": main,
            "main_columns_sha256": digest, "fixed_cells": 8 * ROWS,
            "main_cells": 12 * ROWS}
