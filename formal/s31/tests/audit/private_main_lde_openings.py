#!/usr/bin/env python3
"""Finite, independent M31 circle-LDE check for one accepted private Gate proof.

The production verifier is used to authenticate the proof and, with a test-only
debug environment variable, report its sampled query indices. This module
independently evaluates the source-derived base columns at those indices by
ordinary Lagrange interpolation on conjugate circle-point pairs. It does not
prove PCS/FRI soundness, or promise zero knowledge for transparent proofs.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

from structural_private_committed_air_join import run as committed_run
from scripts.structural_committed_air_join import expected_columns
from package.fixed_root_join import proof_roots

P = 2**31 - 1
GEN = (2, 1_268_011_823)
QUERY_LINE = re.compile(r"verifier_sampled_queries=\{([^}]*)\}")


def reverse_bits(value: int, bits: int) -> int:
    if not 0 <= value < 1 << bits:
        raise ValueError("position outside circle domain")
    return int(f"{value:0{bits}b}"[::-1], 2)


def add_points(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    x, y = left
    z, w = right
    return ((x*z - y*w) % P, (x*w + y*z) % P)


def point_at_index(index: int) -> tuple[int, int]:
    """Independent exponentiation of the stated M31 circle generator."""
    result = (1, 0)
    power = GEN
    while index:
        if index & 1:
            result = add_points(result, power)
        power = add_points(power, power)
        index >>= 1
    if (result[0]*result[0] + result[1]*result[1]) % P != 1:
        raise AssertionError("circle generator arithmetic left the circle")
    return result


def canonical_point(log_size: int, physical_index: int) -> tuple[int, int]:
    """Canonical circle domain at the physical, bit-reversed column index."""
    natural = reverse_bits(physical_index, log_size)
    half = 1 << (log_size - 1)
    first_half = natural < half
    coset_index = natural if first_half else natural - half
    # CanonicCoset.halfCoset = Coset.halfOdds(log_size-1).
    initial = 1 << (31 - (log_size + 1))
    step = 1 << (31 - (log_size - 1))
    x, y = point_at_index(initial + step*coset_index)
    return (x, y if first_half else (-y) % P)


def pair_data(columns: list[list[int]]) -> tuple[list[int], list[list[int]], list[list[int]]]:
    if len(columns) != 12 or any(len(column) != 512 for column in columns):
        raise ValueError("private Gate main base-column shape differs")
    half = 256
    abscissas: list[int] = []
    positives: list[int] = []
    for natural in range(half):
        even = reverse_bits(natural, 9)
        odd = reverse_bits(natural + half, 9)
        if even & 1 or odd != even + 1:
            raise AssertionError("bit-reversed conjugate pair ordering differs")
        x, y = canonical_point(9, even)
        x_other, y_other = canonical_point(9, odd)
        if x != x_other or (y + y_other) % P or y == 0:
            raise AssertionError("base-domain conjugate pair differs")
        abscissas.append(x)
        positives.append(y)
    if len(set(abscissas)) != half:
        raise AssertionError("base-domain pair x coordinates are not distinct")
    inv_two = (P + 1) // 2
    a_columns: list[list[int]] = []
    b_columns: list[list[int]] = []
    for column in columns:
        a: list[int] = []
        b: list[int] = []
        for natural, y in enumerate(positives):
            even = reverse_bits(natural, 9)
            upper, lower = column[even], column[even + 1]
            if not 0 <= upper < P or not 0 <= lower < P:
                raise ValueError("noncanonical source-derived base cell")
            a.append((upper + lower)*inv_two % P)
            b.append((upper - lower)*pow(2*y, -1, P) % P)
        a_columns.append(a)
        b_columns.append(b)
    return abscissas, a_columns, b_columns


def barycentric_weights(xs: list[int]) -> list[int]:
    weights: list[int] = []
    for i, x in enumerate(xs):
        product = 1
        for j, other in enumerate(xs):
            if i != j:
                product = product*(x - other) % P
        weights.append(pow(product, -1, P))
    return weights


def interpolate_all(xs: list[int], a_columns: list[list[int]],
                    b_columns: list[list[int]], weights: list[int],
                    physical_index: int) -> list[int]:
    x, y = canonical_point(10, physical_index)
    if x in xs:
        raise AssertionError("2x LDE coset intersects base pair x coordinates")
    basis = [weight*pow(x - source_x, -1, P) % P
             for weight, source_x in zip(weights, xs)]
    denominator = sum(basis) % P
    if denominator == 0:
        raise AssertionError("barycentric denominator vanished")
    inv_denominator = pow(denominator, -1, P)
    return [((sum(c*t for c, t in zip(a, basis)) +
              y*sum(c*t for c, t in zip(b, basis))) * inv_denominator) % P
            for a, b in zip(a_columns, b_columns)]


class Reader:
    def __init__(self, data: bytes, offset: int):
        self.data = data
        self.offset = offset

    def bounded(self, count: int) -> None:
        if count < 0 or count > 1_000_000:
            raise ValueError("oversized proof vector")

    def take(self, count: int) -> bytes:
        self.bounded(count)
        end = self.offset + count
        if end > len(self.data):
            raise ValueError("truncated proof")
        result = self.data[self.offset:end]
        self.offset = end
        return result

    def varint(self) -> int:
        result = 0
        for shift in range(0, 70, 7):
            byte = self.take(1)[0]
            result |= (byte & 127) << shift
            if byte < 128:
                if result >= 1 << 64 or (shift and byte == 0):
                    raise ValueError("noncanonical proof varint")
                return result
        raise ValueError("oversized proof varint")


def main_openings(raw: bytes) -> list[list[int]]:
    # Native verification of these exact bytes precedes this bounded parser.
    _, _, main_offset = proof_roots(raw)
    reader = Reader(raw, main_offset + 3*32)  # finish four commitment roots
    sampled_trees = reader.varint()
    if sampled_trees != 4:
        raise ValueError("unexpected sampled tree roster")
    for _ in range(sampled_trees):
        columns = reader.varint()
        reader.bounded(columns)
        for _ in range(columns):
            values = reader.varint()
            reader.bounded(values)
            for _ in range(values*4):
                if reader.varint() >= P:
                    raise ValueError("noncanonical sampled coordinate")
    decommitments = reader.varint()
    if decommitments != 4:
        raise ValueError("unexpected decommitment roster")
    for _ in range(decommitments):
        reader.take(reader.varint()*32)
    if reader.varint() != 4:
        raise ValueError("unexpected queried tree roster")
    main: list[list[int]] = []
    for tree in range(4):
        columns = reader.varint()
        reader.bounded(columns)
        if tree == 1 and columns != 12:
            raise ValueError("private Gate main query columns differ")
        for _ in range(columns):
            count = reader.varint()
            reader.bounded(count)
            values = [reader.varint() for _ in range(count)]
            if any(value >= P for value in values):
                raise ValueError("noncanonical queried field value")
            if tree == 1:
                main.append(values)
    return main


def verifier_positions(verifier: Path, proof: Path, statement: Path, key: Path) -> list[int]:
    env = dict(os.environ, STWO_ZIG_SN2_LOG_VERIFIER_DECOMMIT="1")
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                            env=env, text=True, capture_output=True, timeout=120,
                            check=False)
    if result.returncode:
        raise AssertionError("native verifier rejected original private proof: " +
                             result.stderr[-1500:])
    matches = QUERY_LINE.findall(result.stdout + result.stderr)
    if len(matches) != 1:
        raise AssertionError("verifier did not report one sampled query roster")
    positions = [int(value) for value in re.findall(r"\d+", matches[0])]
    if (not positions or len(positions) != len(set(positions)) or
            any(not 0 <= value < 1024 for value in positions)):
        raise AssertionError("sampled query positions differ")
    return positions


def compare_openings(opened: list[list[int]], positions: list[int],
                     xs: list[int], a_columns: list[list[int]],
                     b_columns: list[list[int]], weights: list[int]) -> int:
    if len(opened) != 12 or any(len(column) != len(positions) for column in opened):
        raise AssertionError("queried main opening matrix does not match query roster")
    for sample, position in enumerate(positions):
        expected = interpolate_all(xs, a_columns, b_columns, weights, position)
        for column, value in enumerate(expected):
            if opened[column][sample] != value:
                raise AssertionError(f"source-derived main LDE differs at query {sample}, "
                                     f"column {column}")
    return len(positions)*12


def check(work: Path) -> dict:
    work.mkdir(mode=0o700, parents=True, exist_ok=True)
    prior = committed_run(work)
    graph = json.loads((work / "native-graph.json").read_bytes())
    _, source_main = expected_columns(graph)
    package = work / "package"
    manifest = json.loads((package / "manifest.json").read_bytes())
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    positions = verifier_positions(verifier, work / "proof.bin", work / "statement.json",
                                   package / "verification-key.json")
    opened = main_openings((work / "proof.bin").read_bytes())
    xs, a_columns, b_columns = pair_data(source_main)
    weights = barycentric_weights(xs)
    compared = compare_openings(opened, positions, xs, a_columns, b_columns, weights)
    hostile = [column.copy() for column in opened]
    hostile[8][0] = (hostile[8][0] + 1) % P
    try:
        compare_openings(hostile, positions, xs, a_columns, b_columns, weights)
    except AssertionError as error:
        if "source-derived main LDE differs" not in str(error):
            raise
    else:
        raise AssertionError("altered queried value escaped independent LDE comparison")
    shifted = positions.copy()
    shifted[0] = (shifted[0] + 2) % 1024
    try:
        compare_openings(opened, shifted, xs, a_columns, b_columns, weights)
    except AssertionError as error:
        if "source-derived main LDE differs" not in str(error):
            raise
    else:
        raise AssertionError("changed queried position escaped independent LDE comparison")
    return {"schema": "s31-private-main-lde-openings-v1",
            "source_sha256": prior["source_sha256"],
            "proof_sha256": hashlib.sha256((work / "proof.bin").read_bytes()).hexdigest(),
            "sampled_positions": len(positions),
            "main_openings_compared": compared,
            "hostile_mutations_rejected": 2,
            "native_verifier_accepted": True,
            "production_private_export_rejected": prior["production_private_export_rejected"],
            "proof_mode": "transparent"}


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="s31-private-main-lde-") as directory:
        print(json.dumps(check(Path(directory)), sort_keys=True))
