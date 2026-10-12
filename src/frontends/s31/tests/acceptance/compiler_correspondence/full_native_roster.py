#!/usr/bin/env python3
"""Check four complete native direct-Gate base traces against a checked plan.

The default path checks checked-in diagnostic exports; --native rebuilds all
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
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))
sys.path.insert(0, str(ROOT / "formal/s31/scripts"))

import s31  # noqa: E402
import check_early_return_nonvacuity as model  # noqa: E402
from text_frontend import compile_text  # noqa: E402
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, canonical_ir_bytes, check_package, parse_source,
)
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from test_source_mutation_correspondence import (  # noqa: E402
    CORPUS_SHA256, corpus, corpus_digest,
)
from public_main_root_binding import main_words, proof_roots  # noqa: E402

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
SELECTED = (("00:direct", "case00"), ("07:aliases", "case07"),
            ("14:direct", "case14"), ("15:comments", "case16"))
FIXTURES = HERE / "fixtures"
SNAPSHOT = ROOT / "formal/s31/fixtures/correspondence/native_source_cells.json"
PRIVATE_SOURCE = S31 / "examples/arithmetic/named_square4_manual.s31"
SCHEMA = "s31-direct-gate-public-functional-physical-v1"
# Public words are mixed into the Fiat-Shamir channel before the verifier's
# interaction nonce check. These deterministic trial bytes reject here; a
# different changed transcript could by chance pass the nonce and fail later.
CHANGED_RESULT_ERROR = "InvalidInteractionNonce"
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


def check_static_plan(sample, pinned: dict) -> dict:
    """Check source, projected roles, and every fixed cell without native work.

    This binds the host-side schedule to an earlier native fixed-column digest.
    It cannot check main values, the exporter, or a fresh sealed key.
    """
    relation, syntax, source_cells, projected = source_plan(sample)
    source_sha = sha(sample.source.encode())
    normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    fixed, _, n_vars = expected_fixed(syntax)
    encoded = b"".join(struct.pack("<I", word) for column in fixed for word in column)
    if (pinned.get("source_sha256") != source_sha or
            pinned.get("normalized_sha256") != sha(normalized) or
            pinned.get("canonical_ir_sha256") != sha(canonical_ir_bytes(syntax)) or
            pinned.get("source_rows") != source_cells or
            pinned.get("all_fixed_columns_sha256") != sha(encoded)):
        raise ValueError(f"{sample.label}: static source or fixed schedule differs from pinned native export")
    projected_rows = {cell.traceRow for cell in projected}
    for cell in projected:
        if [column[cell.traceRow] for column in fixed] != [getattr(cell, name) for name in FIELDS]:
            raise ValueError(f"{sample.label}: projected fixed role differs at row {cell.traceRow}")
    n = sample.gate_count
    n_add = sum(op == "+" for op, _, _ in sample.steps)
    add_rows = 476 - (n - n_add)
    constant_rows = (set(range(11 + n_add, add_rows)) | {add_rows} |
                     set(range(add_rows + 7, add_rows + 28)))
    if (projected_rows & constant_rows or
            projected_rows | constant_rows != set(range(512)) or
            len(constant_rows) != 487 - n):
        raise ValueError(f"{sample.label}: projected and constant rows do not partition 512 rows")
    shared_seeds = {0, 1, 2, 15, 16, 25 + n, 28 + n, 31 + n}
    for row in constant_rows:
        ports = fixed[4][row], fixed[5][row], fixed[6][row]
        if any(address not in shared_seeds and address < 33 + n for address in ports):
            raise ValueError(f"{sample.label}: constant island touches a projected-only address")
        opcode = next(index for index in range(4) if fixed[index][row] == 1)
        wanted = 1 if row == add_rows else 2 if add_rows + 7 <= row < add_rows + 28 else 0
        if opcode != wanted:
            raise ValueError(f"{sample.label}: constant island opcode differs at row {row}")
    return {"label": sample.label, "source_gates": n, "selected_return": sample.return_id,
            "alias_source": ":aliases" in sample.label, "rows": n_vars,
            "projected_rows": len(projected), "constant_rows": len(constant_rows),
            "fixed_columns_sha256": sha(encoded)}


def check_private_guard_source() -> dict:
    """Identify an existing private M31×4 direct source for the CLI control."""
    relation, _ = compile_text(PRIVATE_SOURCE.read_text())
    if (relation.get("name") != "named_square4" or relation.get("version") != 1 or
            relation.get("proof_mode", "transparent") != "transparent" or
            relation.get("inputs") != [{"name": "x", "kind": "m31", "length": 4,
                                        "visibility": "private"}] or
            relation.get("nodes") != [{"name": "result", "op": "mul",
                                       "lhs": "x", "rhs": "x"}] or
            relation.get("public_outputs") != ["result"]):
        raise ValueError("private guard source is not the expected one-gate M31×4 program")
    return {"source": str(PRIVATE_SOURCE.relative_to(ROOT)),
            "source_sha256": sha(PRIVATE_SOURCE.read_bytes())}


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
    check_static_plan(sample, pinned)
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


def native_proof_binding(package: Path, assigned: Path, work: Path, sample,
                         physical: dict, key: dict) -> dict:
    """Bind one accepted proof's first two roots to its public base export."""
    manifest = s31.verify_package(package)
    abi = json.loads((package / "public-abi.json").read_bytes())
    result_name = f"p{sample.return_id}"
    if (abi.get("schema") != "s31-public-abi-v1" or
            abi.get("public_inputs") != [{"name": "x", "kind": "m31", "length": 4}] or
            abi.get("public_outputs") != [{"name": result_name, "kind": "m31", "length": 4}]):
        raise ValueError("native package public ABI differs from admitted four-lane source")
    trial_dir = work / f"trial-{sample.label.replace(':', '-')}"
    trial = s31.trial(package, assigned, trial_dir)
    field = f"public_outputs.{result_name}[0]"
    if (trial.get("native_verifier_accepted") is not True or
            trial.get("changed_public_statement_rejected") != field or
            trial.get("proof_bytes", 0) <= 0):
        raise ValueError("honest proof or changed-result native trial failed")
    # The trial has accepted this exact proof with the generated native
    # verifier and the package's sealed key before we interpret its roots.
    proof = (trial_dir / "proof.bin").read_bytes()
    if len(proof) != trial["proof_bytes"] or sha(proof) != trial["proof_sha256"]:
        raise ValueError("native trial proof bytes differ from its accepted report")
    fixed_root, proof_main_root, _ = proof_roots(proof)
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    root_report = json.loads(s31.invoke(str(prover), "inspect-physical-root", str(assigned)))
    serialized_main_digest = sha(main_words(physical))
    if (type(root_report) is not dict or
            set(root_report) != {"schema", "program_sha256", "public_words",
                                 "main_root", "main_columns_sha256"} or
            root_report["schema"] != "s31-direct-gate-public-main-root-v1" or
            root_report["program_sha256"] != manifest["program_sha256"] or
            root_report["program_sha256"] != physical.get("program_sha256") or
            root_report["public_words"] != physical.get("public_words") or
            type(root_report["main_root"]) is not str or
            re.fullmatch(r"[0-9a-f]{64}", root_report["main_root"]) is None or
            type(root_report["main_columns_sha256"]) is not str or
            root_report["main_columns_sha256"] != serialized_main_digest or
            fixed_root.hex() != key.get("preprocessed_root") or
            proof_main_root.hex() != root_report["main_root"]):
        raise ValueError("accepted proof roots differ from sealed fixed key or public writeBase rows")
    honest = json.loads((trial_dir / "statement.json").read_bytes())
    changed = json.loads((trial_dir / "changed-statement.json").read_bytes())
    expected = {"public_inputs": {"x": list(INPUT)},
                "public_outputs": {result_name: list(evaluate(sample)[1])}}
    wanted = copy.deepcopy(expected)
    wanted["public_outputs"][result_name][0] = (wanted["public_outputs"][result_name][0] + 1) % P
    if honest != expected or changed != wanted:
        raise ValueError("changed-result statement is not the exact ABI-valid M31 mutation")
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    denied = subprocess.run((str(verifier), str(trial_dir / "proof.bin"),
                             str(trial_dir / "changed-statement.json"),
                             str(package / "verification-key.json")),
                            capture_output=True, text=True, timeout=120, check=False)
    # Zig prints `error: Name` in its CLI; preserve a strict single-error
    # requirement while accepting the older `error.Name` spelling in logs.
    errors = re.findall(r"(?m)^error(?:\.|: )([A-Za-z][A-Za-z0-9_]*)$", denied.stderr)
    if denied.returncode == 0 or errors != [CHANGED_RESULT_ERROR]:
        raise ValueError(f"changed-result native rejection differs: {errors}, exit {denied.returncode}")
    return {"proof_bytes": trial["proof_bytes"],
            "proof_sha256": trial["proof_sha256"],
            "native_verifier_accepted": True,
            "proof_fixed_root": fixed_root.hex(),
            "proof_main_root": proof_main_root.hex(),
            "main_columns_sha256": serialized_main_digest,
            "main_cells_bound": 6144,
            "changed_public_result_rejected_at": field,
            "changed_public_result_error": errors[0]}


def native_case(work: Path, sample, prefix: str, pinned: dict) -> tuple[dict, dict]:
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
    for command in ("inspect-physical-rows", "inspect-physical-root"):
        denied_result = subprocess.run((str(prover), command, str(denied_path)),
                                       capture_output=True, text=True, timeout=120, check=False)
        if (denied_result.returncode == 0 or
                "PrivatePhysicalRowsUnavailable" not in denied_result.stderr or
                any(key in denied_result.stdout + denied_result.stderr
                    for key in ('"fixed_columns"', '"main_columns"', '"main_root"',
                                '"main_columns_sha256"'))):
            raise ValueError(f"native {command} leaked a nonempty private assignment")
    data = {"schema": "s31-full-native-roster-diagnostic-v1", "label": sample.label,
            "source_sha256": sha(sample.source.encode()),
            "sealed_key_root": key["preprocessed_root"],
            "topology": topology, "physical": physical}
    check_case(data, sample, pinned)
    return data, native_proof_binding(package, assigned, work, sample, physical, key)


def native_private_source_rejection(work: Path) -> dict:
    """Exercise the CLI source guard using a real private-input package."""
    source = check_private_guard_source()
    package = s31.build(PRIVATE_SOURCE, work / "package-private-guard", "direct-gate")
    manifest = s31.verify_package(package)
    if manifest.get("source_text_sha256") != source["source_sha256"]:
        raise ValueError("private guard package does not bind the selected source")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    assigned = work / "assignment-private-guard.json"
    assigned.write_text(json.dumps({"public_inputs": {}, "private_inputs": {"x": list(INPUT)},
                                    "public_outputs": {"result": [0, 1, 4, 49]}},
                                   sort_keys=True) + "\n")
    for command in ("inspect-physical-rows", "inspect-physical-root"):
        result = subprocess.run((str(prover), command, str(assigned)),
                                capture_output=True, text=True, timeout=120, check=False)
        if (result.returncode == 0 or
                "UnsupportedPhysicalRowInspection" not in result.stderr or
                any(key in result.stdout + result.stderr
                    for key in ('"fixed_columns"', '"main_columns"', '"main_root"',
                                '"main_columns_sha256"'))):
            raise ValueError(f"private-input source reached the native {command} exporter")
    return {**source, "native_cli_rejected": True}


def run_native(work: Path, write: bool) -> tuple[list[dict], dict]:
    work.mkdir(parents=True, exist_ok=True)
    pinned = pinned_cases()
    results = []
    pending_writes: list[tuple[Path, bytes]] = []
    for sample, prefix in selected_samples():
        print(f"native full-roster export: {sample.label}", file=sys.stderr, flush=True)
        data, proof_binding = native_case(work, sample, prefix, pinned[sample.label])
        result = check_case(data, sample, pinned[sample.label])
        result.update(proof_binding)
        result["mutations_rejected"] = reject_mutations(data, sample, pinned[sample.label])
        result["native_cli_private_assignment_rejected"] = True
        path = FIXTURES / f"{prefix}-full-native-roster.json"
        encoded = (json.dumps(data, separators=(",", ":"), sort_keys=True) + "\n").encode()
        if write:
            pending_writes.append((path, encoded))
        else:
            fixture_bytes = path.read_bytes()
            fixture = json.loads(fixture_bytes)
            if sha(main_words(fixture["physical"])) != proof_binding["main_columns_sha256"]:
                raise ValueError(f"accepted proof main root has a different pinned-row digest: {prefix}")
            if fixture_bytes != encoded:
                raise ValueError(f"fresh native export differs from pinned diagnostic {prefix}")
        results.append(result)
    private_guard = native_private_source_rejection(work)
    if pending_writes:
        FIXTURES.mkdir(parents=True, exist_ok=True)
        for path, encoded in pending_writes:
            path.write_bytes(encoded)
    return results, private_guard


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build and inspect fresh native packages")
    parser.add_argument("--plan-only", action="store_true",
                        help="check source, row-role partition, and pinned fixed digest without native exports")
    parser.add_argument("--write", action="store_true", help="update fixtures from fresh native exports")
    parser.add_argument("--work", type=Path, help="retain fresh packages and assignments")
    args = parser.parse_args()
    if args.plan_only and (args.native or args.write or args.work):
        parser.error("--plan-only cannot be combined with native export options")
    if args.write and not args.native:
        parser.error("--write requires --native")
    if args.work and not args.native:
        parser.error("--work requires --native")
    if args.plan_only:
        pinned = pinned_cases()
        results = [check_static_plan(sample, pinned[sample.label])
                   for sample, _ in selected_samples()]
        private_guard = check_private_guard_source()
    elif args.native:
        if args.work:
            results, private_guard = run_native(args.work.resolve(), args.write)
        else:
            with tempfile.TemporaryDirectory(prefix="s31-full-native-roster-") as directory:
                results, private_guard = run_native(Path(directory), args.write)
    else:
        pinned = pinned_cases()
        results = []
        for sample, prefix in selected_samples():
            data = json.loads((FIXTURES / f"{prefix}-full-native-roster.json").read_bytes())
            results.append({**check_case(data, sample, pinned[sample.label]),
                            "mutations_rejected": reject_mutations(data, sample, pinned[sample.label])})
        private_guard = check_private_guard_source()
    print(json.dumps({"schema": "s31-full-native-roster-plan-v1" if args.plan_only
                      else "s31-full-native-roster-check-v1",
                      "cases": results, "private_guard": private_guard}, sort_keys=True))


if __name__ == "__main__":
    main()
