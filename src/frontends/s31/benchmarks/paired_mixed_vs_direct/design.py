"""Native-free paired source/assignment generator for direct gate vs mixed AIR."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

P = (1 << 31) - 1
CONSTANT = 13
SEED = 2026101201
S31 = Path(__file__).resolve().parents[2]
TEMPLATE = S31 / "examples/boundary/record_mixed1.s31.json"
SPECS = {"n1_r16": (1, 16), "n4_r16": (4, 16), "n1_r1024": (1, 1024)}


def spec(case: str | int) -> tuple[str, int, int]:
    if case == 1:
        case = "n1_r16"
    elif case == 4:
        case = "n4_r16"
    if case not in SPECS:
        raise ValueError("outside paired case roster")
    calls, rounds = SPECS[case]
    return case, calls, rounds


def name(case: str | int) -> str:
    key, calls, rounds = spec(case)
    return f"paired_fold_{calls}" if rounds == 16 else f"paired_fold_{calls}_r{rounds}"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source(case: str | int) -> bytes:
    _, calls, rounds = spec(case)
    nodes = []
    previous = "x"
    for index in range(calls):
        repeated = f"r{index}"
        nodes.append({"name": repeated, "op": "repeat", "lhs": previous,
                      "rounds": rounds,
                      "body": [{"op": "square"},
                               {"op": "add_const", "constant": CONSTANT + index}]})
        if index + 1 < calls:
            forwarded = f"feed{index}"
            nodes.append({"name": forwarded, "op": "add", "lhs": repeated, "rhs": "x"})
            previous = forwarded
        else:
            previous = repeated
    nodes.append({"name": "out", "op": "add", "lhs": previous, "rhs": "x"})
    template = json.loads(TEMPLATE.read_bytes())
    input_name = template["inputs"][0]["name"]
    output_name = template["public_outputs"][0]
    if input_name != "_s31_abi_input_0" or output_name != "_s31_0":
        raise ValueError("pinned v2 record template changed")
    for node in nodes:
        if node.get("lhs") == "x":
            node["lhs"] = input_name
        if node.get("rhs") == "x":
            node["rhs"] = input_name
        if node["name"] == "out":
            node["name"] = output_name
    return canonical({**template, "name": name(case), "nodes": nodes})


def output(case: str | int, words: list[int]) -> list[int]:
    _, calls, rounds = spec(case)
    previous = words[:]
    for index in range(calls):
        for _ in range(rounds):
            previous = [(value * value + CONSTANT + index) % P
                        for value in previous]
        if index + 1 < calls:
            previous = [(a + b) % P for a, b in zip(previous, words, strict=True)]
    return [(a + b) % P for a, b in zip(previous, words, strict=True)]


def assignment(case: str | int, sample: int) -> bytes:
    key, calls, rounds = spec(case)
    if sample < 0:
        raise ValueError("invalid paired assignment")
    words = [((SEED + calls * 100_000 + rounds * 1009 + sample * 131) * (lane + 7)
              + lane * lane + 17) % P for lane in range(4)]
    return canonical({"public_inputs": {"_s31_abi_input_0": words},
                      "private_inputs": {},
                      "public_outputs": {"_s31_0": output(key, words)}})


def write_case(directory: Path, case: str | int, sample: int) -> tuple[Path, Path]:
    directory.mkdir(parents=True, exist_ok=True)
    source_path = directory / "source.s31.json"
    assignment_path = directory / f"assignment-{sample:03d}.json"
    source_path.write_bytes(source(case))
    assignment_path.write_bytes(assignment(case, sample))
    return source_path, assignment_path
