#!/usr/bin/env python3
"""Replay two source Gate rows against the direct AIR cell geometry.

The package checker binds source, topology, component manifest and installed
AIR bundle digest. This fixture then constructs main cells independently from
the source test vector and evaluates the 9 + 2 modeled residuals in Python.
Its interaction cells are deliberately synthetic: no proof opening or PCS
authentication is inferred from this fixture.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, canonical, check_package, parse_canonical_json,
)

P = (1 << 31) - 1
READ_ORDER = (0, 2, 3, 1, 4, 5, 6, 7)
SPANS = ({"tree": 0, "start": 0, "end": 0},
         {"tree": 1, "start": 0, "end": 12},
         {"tree": 2, "start": 0, "end": 8})


def add(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((a + b) % P for a, b in zip(x, y, strict=True))


def sub(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    return tuple((a - b) % P for a, b in zip(x, y, strict=True))


def mul(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    a, b, c, d = x
    e, f, g, h = y
    real = c * g - d * h
    imag = c * h + d * g
    return ((a * e - b * f + 2 * real - imag) % P,
            (a * f + b * e + real + 2 * imag) % P,
            (a * g - b * h + c * e - d * f) % P,
            (a * h + b * g + c * f + d * e) % P)


def scale(x: tuple[int, ...], n: int) -> tuple[int, ...]:
    return tuple((a * n) % P for a in x)


def base(n: int) -> tuple[int, int, int, int]:
    return (n % P, 0, 0, 0)


def decoded_fixed(local: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(local[READ_ORDER.index(i)] for i in range(8))


def arithmetic(local: tuple[int, ...], main: tuple[int, ...]) -> tuple[int, ...]:
    f = decoded_fixed(local)[:4]
    x, y, out = main[:4], main[4:8], main[8:12]
    product = mul(x, y)
    constraints = [(sum(f) - 1) % P]
    constraints += [(bit * (bit - 1)) % P for bit in f]
    for i in range(4):
        weighted = (product[i] * f[2] + (x[i] + y[i]) * f[0] +
                    (x[i] - y[i]) * f[1] + x[i] * y[i] * f[3]) % P
        constraints.append((out[i] - weighted) % P)
    return tuple(constraints)


def denominator(address: int, value: tuple[int, ...], alpha: tuple[int, ...],
                z: tuple[int, ...]) -> tuple[int, ...]:
    words = (378353459, address, *value)
    acc = base(words[-1])
    for word in reversed(words[:-1]):
        acc = add(mul(acc, alpha), base(word))
    return sub(acc, z)


def interaction_residuals(local: tuple[int, ...], main: tuple[int, ...],
                          current: tuple[int, ...], previous: tuple[int, ...]
                          ) -> tuple[tuple[int, ...], tuple[int, ...]]:
    fixed = decoded_fixed(local)
    x, y, out = main[:4], main[4:8], main[8:12]
    alpha, z, claimed = base(2), base(7), base(11)
    left = denominator(fixed[4], x, alpha, z)
    right = denominator(fixed[5], y, alpha, z)
    produced = denominator(fixed[6], out, alpha, z)
    first, last, prev_last = current[:4], current[4:], previous[4:]
    pair = sub(mul(first, mul(left, right)), add(left, right))
    diff = add(sub(sub(last, prev_last), first), scale(claimed, pow(512, -1, P)))
    last_residual = add(mul(diff, produced), base(fixed[7]))
    return pair, last_residual


def _fin_array(values: tuple[int, ...]) -> str:
    return "![" + ", ".join(str(value) for value in values) + "]"


def _quad(values: tuple[int, ...]) -> str:
    return "⟨⟨%d, %d⟩, ⟨%d, %d⟩⟩" % values


def validate_component_geometry(component: dict) -> None:
    """Reject every changed fixed/main/interaction position in this profile."""
    if (component["preprocessed_indices"] != list(READ_ORDER) or
            component["trace_spans"] != list(SPANS) or
            component["base_trace_columns"] != 12 or
            component["interaction_trace_columns"] != 8 or
            component["n_constraints"] != 11 or
            component["trace_log_size"] != 9):
        raise ValueError("selected captured AIR column geometry changed")


def render(package: Path, assignment: Path) -> str:
    checked = check_package(package)
    relation_source = (ROOT / "deps/stwo-zig/src/frontends/circuit/common/component_list.zig").read_text()
    relation_constant = re.search(r"\bpub const GATE_RELATION_ID\s*:\s*u32\s*=\s*(\d+)\s*;",
                                  relation_source)
    if relation_constant is None or int(relation_constant.group(1)) != 378353459:
        raise ValueError("native Gate relation constant differs from independent replay")
    topology_bytes = (package / "gate-topology.json").read_bytes()
    if hashlib.sha256(topology_bytes).hexdigest() != checked["gate_topology_sha256"]:
        raise ValueError("topology changed after package validation")
    topology = parse_canonical_json(topology_bytes, "gate-topology.json")
    component_bytes = (package / "component-manifest.json").read_bytes()
    component_manifest = parse_canonical_json(component_bytes, "component-manifest.json")
    if hashlib.sha256(canonical(component_manifest)).hexdigest() != checked["air_profile"]["component_manifest_sha256"]:
        raise ValueError("component manifest changed after package validation")
    component = component_manifest["components"][0]
    validate_component_geometry(component)
    columns = topology["columns"]
    if ([item["id"] for item in columns] != list(DIRECT_COLUMN_IDS) or
            any(len(item["values"]) != 512 for item in columns)):
        raise ValueError("preprocessed column order or height changed")
    source = checked["source_ssa"]
    instructions = source["instructions"]
    if (source["input"] != "x" or source["output_name"] != "result" or
            len(instructions) != 2 or
            [(node["id"], node["lhs"], node["rhs"], node["op"])
             for node in instructions] != [(1, 0, 0, "mul"), (2, 1, 1, "mul")]):
        raise ValueError("fixture expects the exact two-step square program")
    statement = json.loads(assignment.read_text())
    vector = statement["public_inputs"]["x"]
    if vector != [0, 1, 2, 7]:
        raise ValueError("fixture expects the documented public input")
    wires = [tuple(vector)]
    for node in instructions:
        x, y = wires[node["lhs"]], wires[node["rhs"]]
        wires.append(tuple(a * b % P for a, b in zip(x, y, strict=True)))
    if wires[-1] != (0, 1, 16, 2401):
        raise ValueError("source vector did not produce documented result")
    if statement["public_outputs"] != {"result": list(wires[-1])} or statement["private_inputs"] != {}:
        raise ValueError("test vector output or privacy shape changed")
    source_gates = checked["source_gates"]
    first_pointwise_row = (checked["gate_counts"]["add"] +
                           checked["gate_counts"]["sub"] +
                           checked["gate_counts"]["mul"])
    rows = []
    for index, gate in enumerate(source_gates):
        trace_row = first_pointwise_row + index
        semantic = tuple(item["values"][trace_row] for item in columns)
        local = tuple(semantic[i] for i in READ_ORDER)
        main = wires[index] + wires[index] + wires[index + 1]
        if (semantic[:4] != (0, 0, 0, 1) or
                semantic[4:7] != (gate["in0"], gate["in1"], gate["out"]) or
                arithmetic(local, main) != (0,) * 9):
            raise ValueError("source row does not satisfy exported fixed/main arithmetic")
        current = tuple(index * 16 + i + 1 for i in range(8))
        previous = tuple(index * 16 + i + 9 for i in range(8))
        rows.append((trace_row, local, main, current, previous))
    first = rows[0]
    fixed_changed = list(first[1]); fixed_changed[1], fixed_changed[2] = fixed_changed[2], fixed_changed[1]
    main_changed = list(first[2]); main_changed[8], main_changed[11] = main_changed[11], main_changed[8]
    interaction_changed = list(first[3]); interaction_changed[0], interaction_changed[4] = interaction_changed[4], interaction_changed[0]
    previous_changed = list(first[4]); previous_changed[4] += 1
    if (arithmetic(tuple(fixed_changed), first[2]) == (0,) * 9 or
            arithmetic(first[1], tuple(main_changed)) == (0,) * 9 or
            interaction_residuals(first[1], first[2], tuple(interaction_changed), first[4]) ==
            interaction_residuals(first[1], first[2], first[3], first[4]) or
            interaction_residuals(first[1], first[2], first[3], tuple(previous_changed))[1] ==
            interaction_residuals(first[1], first[2], first[3], first[4])[1]):
        raise ValueError("column-map mutation failed its residual control")
    names = ("sourceFirst", "sourceSecond", "changedFixed", "changedMain",
             "changedInteraction", "changedPrevious")
    variants = (first, rows[1], (first[0], tuple(fixed_changed), first[2], first[3], first[4]),
                (first[0], first[1], tuple(main_changed), first[3], first[4]),
                (first[0], first[1], first[2], tuple(interaction_changed), first[4]),
                (first[0], first[1], first[2], first[3], tuple(previous_changed)))
    lines = [
        "-- Generated from checked direct Gate package plus a documented test vector.",
        "-- Source SHA-256: " + checked["source_sha256"],
        "-- Interaction cells are synthetic and are not proof openings.",
        "import S31.Gadgets.Air.DirectGateEvaluatorCells", "",
        "namespace S31.Gadgets.Air.GeneratedDirectGateEvaluatorFixture", "",
        "open S31.Gadgets.Air.DirectGateEvaluatorCells", "",
    ]
    for name, (trace_row, fixed, main, current, previous) in zip(names, variants, strict=True):
        lines += [f"-- Direct trace row {trace_row}.", f"def {name} : Cells :=",
                  "  { localFixed := " + _fin_array(fixed) + ",",
                  "    main := " + _fin_array(main) + ",",
                  "    interaction := " + _fin_array(current) + ",",
                  "    previousInteraction := " + _fin_array(previous) + " }", ""]
    for name in names[:2]:
        lines += [f"theorem {name}_arithmetic : arithmetic {name} = List.replicate 9 0 := by decide", ""]
    lines += [
        "theorem changed_fixed_detected : arithmetic changedFixed ≠ List.replicate 9 0 := by decide",
        "theorem changed_main_detected : arithmetic changedMain ≠ List.replicate 9 0 := by decide",
        "theorem changed_interaction_detected :",
        "    pair sourceFirst 2 7 ≠ pair changedInteraction 2 7 := by decide", "",
        "theorem changed_previous_detected :",
        "    last sourceFirst 2 7 11 512 ≠ last changedPrevious 2 7 11 512 := by decide", "",
    ]
    for name, (_, fixed, main, current, previous) in zip(names[:2], rows, strict=True):
        pair, last = interaction_residuals(fixed, main, current, previous)
        lines += [f"theorem {name}_pair_replay : pair {name} 2 7 = {_quad(pair)} := by decide",
                  f"theorem {name}_last_replay : last {name} 2 7 11 512 = {_quad(last)} := by decide", ""]
    lines += ["end S31.Gadgets.Air.GeneratedDirectGateEvaluatorFixture", ""]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("assignment", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = render(args.package, args.assignment)
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            raise SystemExit("direct Gate evaluator fixture changed")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)


if __name__ == "__main__":
    main()
