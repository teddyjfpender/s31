#!/usr/bin/env python3
"""Check two complete native direct-Gate base traces against an independent plan.

The default path checks checked-in diagnostic exports; --native rebuilds both
source-bound packages and checks their fresh uncommitted writeBase exports.
Neither path authenticates proof openings or establishes PCS/FRI soundness.
"""

from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import json
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[2]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))
sys.path.insert(0, str(ROOT / "formal/s31/scripts"))

import s31  # noqa: E402
import check_early_return_nonvacuity as model  # noqa: E402
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, canonical_ir_bytes, check_package, parse_source,
)
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from test_source_mutation_correspondence import (  # noqa: E402
    CORPUS_SHA256, corpus, corpus_digest,
)

P = 2_147_483_647
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
U = (0, 0, 1, 0)
I = (0, 1, 0, 0)
IU = (0, 0, 0, 1)
INV5 = pow(5, -1, P)
INV_I = (0, P - 1, 0, 0)
INV_U = (0, 0, 2 * INV5 % P, -INV5 % P)
INV_IU = (0, 0, -INV5 % P, -2 * INV5 % P)
INPUT = (0, 1, 2, 7)
SELECTED = (("00:direct", "case00"), ("15:comments", "case16"))
FIXTURES = HERE / "fixtures"
SNAPSHOT = ROOT / "formal/s31/fixtures/correspondence/native_source_cells.json"
SCHEMA = "s31-direct-gate-public-functional-physical-v1"
FIELDS = model.FIELDS[1:]
KINDS = ("add", "sub", "mul", "pointwise_mul")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def selected_samples():
    samples = corpus()
    if corpus_digest(samples) != CORPUS_SHA256:
        raise ValueError("pinned positional source corpus changed")
    by_label = {sample.label: sample for sample in samples}
    return [(by_label[label], prefix) for label, prefix in SELECTED]


def pinned_cases() -> dict[str, dict]:
    snapshot = json.loads(SNAPSHOT.read_bytes())
    if snapshot.get("corpus_sha256") != CORPUS_SHA256:
        raise ValueError("source-cell snapshot corpus differs")
    return {case["label"]: case for case in snapshot["cases"]}


def evaluate(sample) -> tuple[list[tuple[int, ...]], tuple[int, ...]]:
    """Evaluate the generator's positional four-lane DAG, not either parser."""
    values = [INPUT]
    for operation, left, right in sample.steps:
        values.append(tuple(((a + b) if operation == "+" else a * b) % P
                            for a, b in zip(values[left], values[right], strict=True)))
    return values, values[sample.return_id]


def assignment(sample) -> dict:
    _, output = evaluate(sample)
    return {"public_inputs": {"x": list(INPUT)}, "private_inputs": {},
            "public_outputs": {f"p{sample.return_id}": list(output)}}


def source_plan(sample) -> tuple[dict, dict, list[list[int]], list[model.Cell]]:
    relation, syntax = parse_source(sample.source.encode())
    steps = [("+" if item["op"] == "add" else ".*", item["lhs"], item["rhs"])
             for item in syntax["instructions"]]
    if (steps != list(sample.steps) or syntax["output"] != sample.return_id or
            len(steps) != sample.gate_count or relation.get("name") !=
            f"mutation_{int(sample.label[:2])}"):
        raise ValueError("independent source DAG differs from admitted parser")
    # This generator-based projected plan is separate from the full fixed
    # schedule and from Zig's exported gate list.
    n_mul = sum(op == ".*" for op, _, _ in sample.steps)
    instructions = [(index, lhs, rhs, op == ".*")
                    for index, (op, lhs, rhs) in enumerate(sample.steps, 1)]
    source, inputs, outputs = model.expected_plans(
        instructions, sample.return_id, 476 - n_mul)
    projected = [*source, *inputs, *outputs]
    if len(projected) != sample.gate_count + 25 or len({c.traceRow for c in projected}) != len(projected):
        raise ValueError("source/public projected physical roles are incomplete")
    return relation, syntax, [list(vars(c).values()) for c in source], projected


def expected_fixed(syntax: dict) -> tuple[list[list[int]], dict, int]:
    """Construct all 512 fixed rows from the independent Python schedule."""
    gates, n_vars, rows, _ = exact_direct_gate_schedule(syntax)
    if n_vars != 512 or rows != 512 or sum(len(gates[k]) for k in KINDS) != 512:
        raise ValueError("independent direct-Gate schedule is not 512 rows")
    reads: Counter[int] = Counter()
    for kind in KINDS:
        for gate in gates[kind]:
            reads[gate["in0"]] += 1
            reads[gate["in1"]] += 1
    # The native direct profile consumes one unit at address 2 and eight
    # public scalar words at addresses 3..10. There are no external yields.
    reads.update((2, *range(3, 11)))
    rows_fixed = [[int(opcode == column) for column in range(4)] +
                  [gate["in0"], gate["in1"], gate["out"], reads[gate["out"]]]
                  for opcode, kind in enumerate(KINDS) for gate in gates[kind]]
    if sorted(row[6] for row in rows_fixed) != list(range(512)):
        raise ValueError("independent output addresses are not a permutation")
    return [[row[column] for row in rows_fixed] for column in range(8)], gates, n_vars


def columns(raw: object, count: int, label: str) -> list[list[int]]:
    if (type(raw) is not list or len(raw) != count or
            any(type(column) is not list or len(column) != 512 for column in raw) or
            any(type(value) is not int or not 0 <= value < P
                for column in raw for value in column)):
        raise ValueError(f"invalid {label} shape or M31 word")
    return raw


def gate_balance(fixed: list[list[int]], main: list[list[int]], public: list[int],
                 extra_external_uses: tuple[tuple[int, tuple[int, ...]], ...] = ()) -> int:
    uses: Counter[tuple[int, tuple[int, ...]]] = Counter()
    yields: Counter[tuple[int, tuple[int, ...]]] = Counter()
    uses[(2, U)] += 1
    for address, word in enumerate(public, 3):
        uses[(address, (word, 0, 0, 0))] += 1
    uses.update(extra_external_uses)
    for row in range(512):
        left = tuple(main[column][row] for column in range(4))
        right = tuple(main[column][row] for column in range(4, 8))
        output = tuple(main[column][row] for column in range(8, 12))
        uses[(fixed[4][row], left)] += 1
        uses[(fixed[5][row], right)] += 1
        yields[(fixed[6][row], output)] += fixed[7][row]
    if uses != yields:
        raise ValueError("exact Gate address/value ledger differs from native public feeders")
    return sum(uses.values())


def check_case(data: dict, sample, pinned: dict) -> dict:
    relation, syntax, source_cells, projected = source_plan(sample)
    source_sha = sha(sample.source.encode())
    normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    if (data.get("schema") != "s31-full-native-roster-diagnostic-v1" or
            data.get("label") != sample.label or
            data.get("source_sha256") != source_sha or
            pinned.get("source_sha256") != source_sha or
            pinned.get("normalized_sha256") != sha(normalized) or
            pinned.get("canonical_ir_sha256") != sha(canonical_ir_bytes(syntax)) or
            pinned.get("source_rows") != source_cells):
        raise ValueError("case provenance differs from admitted source/generator")
    topology = data.get("topology")
    report = data.get("physical")
    if type(topology) is not dict or type(report) is not dict:
        raise ValueError("topology or physical export missing")
    expected, gates, n_vars = expected_fixed(syntax)
    fixed = columns(report.get("fixed_columns"), 8, "physical fixed")
    main = columns(report.get("main_columns"), 12, "physical main")
    exported = topology.get("columns")
    if (topology.get("schema") != "s31-direct-gate-topology-v2" or
            topology.get("program_sha256") != sha(normalized) or
            topology.get("n_vars") != n_vars or
            topology.get("output") != [2, *range(3, 11)] or
            topology.get("permutation_inputs") != [] or
            topology.get("permutation_outputs") != [] or
            topology.get("permutation_ends") != [] or
            topology.get("first_permutation_row") != 512 or
            any(topology.get(kind) != gates[kind] for kind in KINDS) or
            type(exported) is not list or len(exported) != 8 or
            [entry.get("id") for entry in exported] != list(DIRECT_COLUMN_IDS) or
            [entry.get("values") for entry in exported] != expected or fixed != expected):
        raise ValueError("complete native fixed roster differs from independent schedule/topology")
    encoded = b"".join(struct.pack("<I", word) for column in fixed for word in column)
    root = topology.get("preprocessed_root")
    if (type(root) is not str or re.fullmatch(r"[0-9a-f]{64}", root) is None or
            root != data.get("sealed_key_root") or
            root != pinned.get("preprocessed_root") or
            sha(encoded) != pinned.get("all_fixed_columns_sha256")):
        raise ValueError("exported fixed columns/root differ from sealed key/pinned native digest")
    _, expected_output = evaluate(sample)
    public = report.get("public_words")
    if (report.get("schema") != SCHEMA or report.get("program_sha256") != sha(normalized) or
            public != [*INPUT, *expected_output]):
        raise ValueError("physical public words differ from source evaluation")
    projected_rows = {cell.traceRow for cell in projected}
    for cell in projected:
        actual = [column[cell.traceRow] for column in fixed]
        wanted = [getattr(cell, name) for name in FIELDS]
        if actual != wanted:
            raise ValueError(f"source/public projected role differs at row {cell.traceRow}")
    n = sample.gate_count
    n_add = sum(op == "+" for op, _, _ in sample.steps)
    n_mul = n - n_add
    add_rows = 476 - n_mul
    constant_rows = set(range(11 + n_add, add_rows)) | {add_rows} | set(range(add_rows + 7, add_rows + 28))
    if (projected_rows & constant_rows or
            projected_rows | constant_rows != set(range(512)) or
            len(constant_rows) != 487 - n):
        raise ValueError("projected/constant roles do not partition physical rows")
    seeds = {0: ZERO, 1: ONE, 2: U,
             15: I, 16: IU,
             25 + n: INV_I, 28 + n: INV_U,
             31 + n: INV_IU}
    for row in constant_rows:
        ports = fixed[4][row], fixed[5][row], fixed[6][row]
        if any(address not in seeds and address < 33 + n for address in ports):
            raise ValueError(f"constant island reads/writes projected-only address at row {row}")
        opcode = next(i for i in range(4) if fixed[i][row] == 1)
        if opcode != (1 if row == add_rows else 2 if add_rows + 7 <= row < add_rows + 28 else 0):
            raise ValueError(f"constant island row role differs at row {row}")
    produced: dict[int, tuple[int, ...]] = {}
    for row in range(512):
        left = tuple(main[column][row] for column in range(4))
        right = tuple(main[column][row] for column in range(4, 8))
        output = tuple(main[column][row] for column in range(8, 12))
        physical = model.Row(fixed[4][row], fixed[5][row], fixed[6][row],
                             tuple(fixed[column][row] for column in range(4)),
                             left, right, output, fixed[7][row])
        if any(model.roots(physical)):
            raise ValueError(f"installed arithmetic roots differ at row {row}")
        address = fixed[6][row]
        if address in produced:
            raise ValueError(f"duplicate producer address {address}")
        produced[address] = output
    if set(produced) != set(range(512)):
        raise ValueError("main producer addresses do not cover the full wire")
    for row in range(512):
        for address_column, offset in ((4, 0), (5, 4)):
            actual = tuple(main[offset + i][row] for i in range(4))
            if actual != produced[fixed[address_column][row]]:
                raise ValueError(f"main values are not coherent at row {row}")
    for address, expected_value in seeds.items():
        if produced[address] != expected_value:
            raise ValueError(f"constant seed/basis/inverse differs at address {address}")
    values, _ = evaluate(sample)
    for wire_id, words in enumerate(values):
        if produced[22 + wire_id] != tuple(words):
            raise ValueError(f"source value differs at SSA wire {wire_id}")
    for address, word in enumerate(public, 3):
        if produced[address] != (word, 0, 0, 0):
            raise ValueError(f"public copy value differs at address {address}")
    events = gate_balance(fixed, main, public)
    return {"label": sample.label, "source_gates": n,
            "zero_use_source_results": sum(cell[-1] == 0 for cell in source_cells),
            "constant_rows": len(constant_rows), "physical_rows": 512,
            "fixed_cells": 4096, "main_cells": 6144,
            "arithmetic_roots": 4608, "gate_events": events,
            "fixed_root": root, "fixed_columns_sha256": sha(encoded)}


def reject_mutations(data: dict, sample, pinned: dict) -> int:
    base = check_case(data, sample, pinned)
    two_constant_add = 13 + sum(op == "+" for op, _, _ in sample.steps)

    def locally_valid_wrong_wire(changed: dict) -> None:
        # This is still a valid zero-plus-zero add. Only the single coherent
        # address-to-value map rejects it, so the control is not a root check.
        for column in changed["physical"]["main_columns"]:
            column[two_constant_add] = 0

    tests = (
        ("fixed-selector", lambda x: x["physical"]["fixed_columns"][0].__setitem__(11, 0), "fixed roster"),
        ("fixed-topology", lambda x: x["topology"]["columns"][7]["values"].__setitem__(0, 2), "fixed roster"),
        ("main-output", lambda x: x["physical"]["main_columns"][8].__setitem__(0, 1), "arithmetic roots"),
        ("locally-valid-wrong-wire", locally_valid_wrong_wire, "main values are not coherent"),
        ("public-claim", lambda x: x["physical"]["public_words"].__setitem__(7, 1), "public words"),
        ("sealed-root", lambda x: x.__setitem__("sealed_key_root", "00" * 32), "sealed key"),
        ("source-identity", lambda x: x.__setitem__("source_sha256", "00" * 32), "provenance"),
    )
    for label, mutate, expected in tests:
        changed = copy.deepcopy(data)
        mutate(changed)
        try:
            check_case(changed, sample, pinned)
        except ValueError as exc:
            if expected not in str(exc):
                raise AssertionError(f"{label}: wrong rejection boundary: {exc}") from exc
        else:
            raise AssertionError(f"{label}: mutation accepted")
    fixed = data["physical"]["fixed_columns"]
    main = data["physical"]["main_columns"]
    public = data["physical"]["public_words"]
    try:
        gate_balance(fixed, main, public, ((2, U),))
    except ValueError as exc:
        if "Gate address/value ledger" not in str(exc):
            raise
    else:
        raise AssertionError("extra native public feeder use was accepted")
    assert base["physical_rows"] == 512
    return len(tests) + 1


def native_case(work: Path, sample, prefix: str, pinned: dict) -> dict:
    source = work / f"{prefix}.s31"
    source.write_bytes(sample.source.encode())
    package = s31.build(source, work / f"package-{prefix}", "direct-gate")
    check_package(package)
    manifest = json.loads((package / "manifest.json").read_bytes())
    key = json.loads((package / "verification-key.json").read_bytes())
    if (manifest.get("source_text_sha256") != sha(sample.source.encode()) or
            manifest.get("program_sha256") != pinned["normalized_sha256"]):
        raise ValueError("fresh package source/normalization changed")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    topology = json.loads(s31.invoke(str(prover), "inspect-topology"))
    if topology != json.loads((package / "gate-topology.json").read_bytes()):
        raise ValueError("fresh exporter differs from sealed topology")
    if topology.get("preprocessed_root") != key.get("preprocessed_root"):
        raise ValueError("fresh topology differs from sealed verifier key")
    assigned = work / f"assignment-{prefix}.json"
    assigned.write_text(json.dumps(assignment(sample), sort_keys=True) + "\n")
    result = subprocess.run((str(prover), "inspect-physical-rows", str(assigned)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode:
        raise ValueError(f"native physical-row inspection failed: {result.stderr[-1000:]}")
    physical = json.loads(result.stdout + result.stderr)
    denied = copy.deepcopy(assignment(sample))
    denied["private_inputs"] = {"secret": [1]}
    denied_path = work / f"nonempty-private-assignment-{prefix}.json"
    denied_path.write_text(json.dumps(denied, sort_keys=True) + "\n")
    denied_result = subprocess.run((str(prover), "inspect-physical-rows", str(denied_path)),
                                   capture_output=True, text=True, timeout=120, check=False)
    if (denied_result.returncode == 0 or
            "PrivatePhysicalRowsUnavailable" not in denied_result.stderr):
        raise ValueError("native inspect CLI did not reject nonempty private assignment")
    data = {"schema": "s31-full-native-roster-diagnostic-v1", "label": sample.label,
            "source_sha256": sha(sample.source.encode()),
            "sealed_key_root": key["preprocessed_root"],
            "topology": topology, "physical": physical}
    check_case(data, sample, pinned)
    return data


def run_native(work: Path, write: bool) -> list[dict]:
    work.mkdir(parents=True, exist_ok=True)
    pinned = pinned_cases()
    results = []
    for sample, prefix in selected_samples():
        print(f"native full-roster export: {sample.label}", file=sys.stderr, flush=True)
        data = native_case(work, sample, prefix, pinned[sample.label])
        result = check_case(data, sample, pinned[sample.label])
        result["mutations_rejected"] = reject_mutations(data, sample, pinned[sample.label])
        result["native_cli_private_assignment_rejected"] = True
        path = FIXTURES / f"{prefix}-full-native-roster.json"
        encoded = (json.dumps(data, separators=(",", ":"), sort_keys=True) + "\n").encode()
        if write:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_bytes(encoded)
        elif path.read_bytes() != encoded:
            raise ValueError(f"fresh native export differs from pinned diagnostic {prefix}")
        results.append(result)
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build and inspect fresh native packages")
    parser.add_argument("--write", action="store_true", help="update fixtures from fresh native exports")
    parser.add_argument("--work", type=Path, help="retain fresh packages and assignments")
    args = parser.parse_args()
    if args.write and not args.native:
        parser.error("--write requires --native")
    if args.work and not args.native:
        parser.error("--work requires --native")
    if args.native:
        if args.work:
            results = run_native(args.work.resolve(), args.write)
        else:
            with tempfile.TemporaryDirectory(prefix="s31-full-native-roster-") as directory:
                results = run_native(Path(directory), args.write)
    else:
        pinned = pinned_cases()
        results = []
        for sample, prefix in selected_samples():
            data = json.loads((FIXTURES / f"{prefix}-full-native-roster.json").read_bytes())
            results.append({**check_case(data, sample, pinned[sample.label]),
                            "mutations_rejected": reject_mutations(data, sample, pinned[sample.label])})
    print(json.dumps({"schema": "s31-full-native-roster-check-v1",
                      "cases": results}, sort_keys=True))


if __name__ == "__main__":
    main()
