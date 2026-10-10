"""Independent, fail-closed checker for a small direct-gate S31 fragment.

The accepted grammar has one public [m31; 4] input and one public [m31; 4]
output. Its body contains 1..16 fresh `let name = left + right;` or
`let name = left .* right;` statements followed by a returned wire name.
Operands must name the input or an earlier let, appear in canonical operand
order, and create distinct arithmetic expressions. No imports, calls,
constants, assertions, private inputs, or implicit coercions enter this
certificate.

This checks source bytes against normalized relation and the published native
row schedule. It does not derive the native circuit hash or prove Gate lookup,
AIR-to-rational, PCS, or the installed verifier correct.
"""

from __future__ import annotations

import hashlib
import json
import re
import struct
from pathlib import Path
from typing import Any

from package.direct_gate_schedule import constant_and_padding, exact_direct_gate_schedule


class UnsupportedFragment(ValueError):
    """The source is outside the certificate grammar."""


TOKEN = re.compile(r"\s+|//[^\n]*|->|\.\*|[()\[\];:{}=+]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
SCHEMA = "s31-direct-gate-correspondence-v2"
M31_MODULUS = 2**31 - 1
MAX_SOURCE_BYTES = 16_384
DIRECT_COLUMN_IDS = (
    "qm31_ops_add_flag", "qm31_ops_sub_flag", "qm31_ops_mul_flag",
    "qm31_ops_pointwise_mul_flag", "qm31_ops_in0_address",
    "qm31_ops_in1_address", "qm31_ops_out_address", "qm31_ops_mults",
)
KEY_FIELDS = (
    "schema", "profile", "chip", "name", "program_sha256",
    "canonical_ir_sha256", "preprocessed_root", "circuit_hash",
    "padded", "trace_log_size", "projection_sha256", "air_bundle_sha256",
    "fri", "component_manifest", "stdlib_lock_sha256",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def read_canonical_json(path: Path) -> Any:
    """Reject duplicate keys, non-JSON numbers, and serialization ambiguity."""
    data = path.read_bytes()

    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate JSON key in {path.name}: {key}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> Any:
        raise ValueError(f"invalid JSON constant in {path.name}: {value}")

    value = json.loads(data, object_pairs_hook=pairs, parse_constant=invalid_constant)
    expected = (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()
    if data != expected:
        raise ValueError(f"noncanonical JSON serialization: {path.name}")
    return value


def _tokens(data: bytes) -> list[str]:
    if len(data) > MAX_SOURCE_BYTES:
        raise UnsupportedFragment("source exceeds bounded correspondence byte limit")
    try:
        source = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise UnsupportedFragment("source is not UTF-8") from exc
    result: list[str] = []
    position = 0
    while position < len(source):
        match = TOKEN.match(source, position)
        if match is None:
            raise UnsupportedFragment(f"unsupported token at character {position}")
        token = match.group()
        if not token.isspace() and not token.startswith("//"):
            result.append(token)
            if len(result) > 256:
                raise UnsupportedFragment("source exceeds bounded correspondence token limit")
        position = match.end()
    return result


def parse_source(data: bytes) -> tuple[dict[str, Any], dict[str, Any]]:
    """Reparse exact bytes without using the production lexer or compiler."""
    tokens = _tokens(data)
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedFragment("unexpected end of source")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedFragment(f"expected {expected!r}, found {found!r}")
        return found

    def identifier() -> str:
        value = take()
        if NAME.fullmatch(value) is None or value in {"circuit", "public", "let", "m31"}:
            raise UnsupportedFragment("expected a non-keyword identifier")
        return value

    def lane_type() -> None:
        for token in ("[", "m31", ";", "4", "]"):
            take(token)

    take("circuit")
    circuit = identifier()
    take("(")
    take("public")
    input_name = identifier()
    take(":")
    lane_type()
    take(")")
    take("->")
    take("public")
    lane_type()
    take("{")
    wires = {input_name: 0}
    expressions: set[tuple[str, int, int]] = set()
    nodes: list[dict[str, str]] = []
    ssa: list[dict[str, Any]] = []
    while cursor < len(tokens) and tokens[cursor] == "let":
        take("let")
        name = identifier()
        if name in wires:
            raise UnsupportedFragment("duplicate wire name")
        take("=")
        left = identifier()
        op_token = take()
        if op_token not in {"+", ".*"}:
            raise UnsupportedFragment("only binary add and pointwise multiply are supported")
        right = identifier()
        take(";")
        if left not in wires or right not in wires:
            raise UnsupportedFragment("forward or unbound operand")
        op = "add" if op_token == "+" else "mul"
        lhs_id, rhs_id = wires[left], wires[right]
        if lhs_id > rhs_id:
            raise UnsupportedFragment("commutative operands are not in canonical order")
        expression = (op, lhs_id, rhs_id)
        if expression in expressions:
            raise UnsupportedFragment("canonical common-subexpression elimination would merge lets")
        expressions.add(expression)
        ssa.append({"id": len(wires), "name": name, "op": op,
                    "lhs": lhs_id, "rhs": rhs_id})
        nodes.append({"name": name, "op": op, "lhs": left, "rhs": right})
        wires[name] = len(wires)
        if len(nodes) > 16:
            raise UnsupportedFragment("more than 16 arithmetic operations")
    if not nodes:
        raise UnsupportedFragment("at least one arithmetic operation is required")
    output = identifier()
    take("}")
    if cursor != len(tokens) or output not in wires or output == input_name:
        raise UnsupportedFragment("trailing tokens or output is not a bound let wire")
    relation = {
        "version": 1, "name": circuit,
        "inputs": [{"name": input_name, "kind": "m31", "length": 4,
                    "visibility": "public"}],
        "nodes": nodes, "assertions": [], "public_outputs": [output],
    }
    syntax = {"input": input_name, "instructions": ssa,
              "output": wires[output], "output_name": output}
    return relation, syntax


def public_abi(syntax: dict[str, Any]) -> dict[str, Any]:
    def field(name: str) -> dict[str, Any]:
        return {"name": name, "kind": "m31", "length": 4}
    return {
        "schema": "s31-public-abi-v1",
        "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
        "public_inputs": [field(syntax["input"])],
        "public_outputs": [field(syntax["output_name"])],
    }


def gate_schedule(syntax: dict[str, Any], report: dict[str, Any]) -> list[dict[str, Any]]:
    """Check the native source-map spans against the canonical SSA order."""
    rows = report.get("source_map")
    instructions = syntax["instructions"]
    if not isinstance(rows, list) or len(rows) != len(instructions) + 1:
        raise ValueError("native source-map length differs from checked SSA")
    expected_names = [syntax["input"], *(node["name"] for node in instructions)]
    schedule: list[dict[str, Any]] = []
    prior_end = 0
    for index, (row, name) in enumerate(zip(rows, expected_names, strict=True)):
        if (not isinstance(row, dict) or row.get("name") != name or
                type(row.get("canonical_id")) is not int or row["canonical_id"] != index):
            raise ValueError("native source-map order differs from checked SSA")
        start, end = row.get("qm31_start"), row.get("qm31_end")
        if (type(start) is not int or type(end) is not int or start != prior_end or
                end - start != (6 if index == 0 else 1) or
                any(type(row.get(f"{component}_start")) is not int or
                    type(row.get(f"{component}_end")) is not int or
                    row[f"{component}_start"] != row[f"{component}_end"]
                    for component in ("eq", "m31_to_u32", "triple_xor", "blake_g"))):
            raise ValueError("native gate spans differ from bounded direct arithmetic schedule")
        schedule.append({"id": index, "name": name, "qm31_start": start,
                         "qm31_end": end,
                         "op": "pack_public_input" if index == 0 else instructions[index - 1]["op"]})
        prior_end = end
    return schedule


Qm31 = tuple[int, int, int, int]
QM_ZERO: Qm31 = (0, 0, 0, 0)
QM_ONE: Qm31 = (1, 0, 0, 0)
QM_U: Qm31 = (0, 0, 1, 0)


def _qm_add(left: Qm31, right: Qm31) -> Qm31:
    return tuple((a + b) % M31_MODULUS for a, b in zip(left, right, strict=True))


def _qm_sub(left: Qm31, right: Qm31) -> Qm31:
    return tuple((a - b) % M31_MODULUS for a, b in zip(left, right, strict=True))


def _qm_mul(left: Qm31, right: Qm31) -> Qm31:
    """Independent QM31 arithmetic: i²=-1 and u²=2+i over M31."""
    p = M31_MODULUS

    def complex_mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
        return ((a[0] * b[0] - a[1] * b[1]) % p,
                (a[0] * b[1] + a[1] * b[0]) % p)

    a, b = left[:2], left[2:]
    c, d = right[:2], right[2:]
    ac = complex_mul(a, c)
    bd = complex_mul(b, d)
    cross = complex_mul(a, d)
    other = complex_mul(b, c)
    rbd = complex_mul(bd, (2, 1))
    return ((ac[0] + rbd[0]) % p, (ac[1] + rbd[1]) % p,
            (cross[0] + other[0]) % p, (cross[1] + other[1]) % p)


def _check_constant_island(adds: list[dict[str, int]],
                           subs: list[dict[str, int]],
                           muls: list[dict[str, int]],
                           basis: list[int], inverses: list[int]) -> None:
    """Derive every non-data wire from the fixed public constants 0, 1, u."""
    gates = [(op, gate) for op, group in (("add", adds), ("sub", subs), ("mul", muls))
             for gate in group]
    values: dict[int, Qm31] = {0: QM_ZERO, 1: QM_ONE, 2: QM_U}
    pending = gates
    while pending:
        next_pending = []
        for op, gate in pending:
            lhs, rhs = values.get(gate["in0"]), values.get(gate["in1"])
            if lhs is None or rhs is None:
                next_pending.append((op, gate))
                continue
            value = (_qm_add(lhs, rhs) if op == "add" else
                     _qm_sub(lhs, rhs) if op == "sub" else _qm_mul(lhs, rhs))
            previous = values.get(gate["out"])
            if previous is not None and previous != value:
                raise ValueError("native constant island has contradictory gate equations")
            values[gate["out"]] = value
        if len(next_pending) == len(pending):
            raise ValueError("native constant island contains an underived gate")
        pending = next_pending
    for index, address in enumerate(basis):
        expected = tuple(int(lane == index) for lane in range(4))
        if values.get(address) != expected:
            raise ValueError("native four-lane basis is not derived from fixed constants")
    for basis_address, inverse_address in zip(basis[1:], inverses, strict=True):
        inverse = values.get(inverse_address)
        if inverse is None or _qm_mul(values[basis_address], inverse) != QM_ONE:
            raise ValueError("native output lane inverse basis is not derived correctly")


def _require_gate_schedule(kind: str, actual: list[dict[str, int]],
                           expected: list[dict[str, int]], *,
                           scope: str = "constant derivation or padding gate schedule differs") -> None:
    for index, (found, wanted) in enumerate(zip(actual, expected)):
        if found != wanted:
            raise ValueError(
                f"{scope}: "
                f"{kind}[{index}] = {found}, expected {wanted}")
    if len(actual) != len(expected):
        raise ValueError(
            f"{scope}: "
            f"{kind} has {len(actual)} gates, expected {len(expected)}")


def check_gate_topology(syntax: dict[str, Any], topology: dict[str, Any],
                        component: dict[str, Any], report: dict[str, Any],
                        relation_sha256: str) -> list[dict[str, Any]]:
    """Replay value-free gate rows independently of the native AIR emitter.

    The column digests are checked against the native component manifest.
    This still assumes that the native PCS root commits to those columns.
    """
    if (not isinstance(topology, dict) or set(topology) != {
            "schema", "program_sha256", "n_vars", "output", "add", "sub", "mul",
            "pointwise_mul", "permutation_ends", "permutation_inputs",
            "permutation_outputs", "first_permutation_row", "columns"} or
            topology["schema"] != "s31-direct-gate-topology-v1" or
            topology["program_sha256"] != relation_sha256):
        raise ValueError("native direct-gate topology header differs from source")
    n_vars = topology["n_vars"]
    if type(n_vars) is not int or not 11 < n_vars < M31_MODULUS:
        raise ValueError("invalid native direct-gate variable bound")

    def addresses(name: str, *, exact: list[int] | None = None) -> list[int]:
        values = topology[name]
        if (not isinstance(values, list) or len(values) > 1024 or
                any(type(value) is not int or value < 0 or value >= n_vars
                    for value in values) or (exact is not None and values != exact)):
            raise ValueError(f"invalid native direct-gate {name}")
        return values

    output = addresses("output", exact=[2, *range(3, 11)])
    gate_lists: dict[str, list[dict[str, int]]] = {}
    for kind in ("add", "sub", "mul", "pointwise_mul"):
        gates = topology[kind]
        if not isinstance(gates, list) or len(gates) > 1024:
            raise ValueError(f"invalid native {kind} gates")
        for gate in gates:
            if (not isinstance(gate, dict) or set(gate) != {"in0", "in1", "out"} or
                    any(type(gate[field]) is not int or not 0 <= gate[field] < n_vars
                        for field in ("in0", "in1", "out"))):
                raise ValueError(f"invalid native {kind} gate")
        gate_lists[kind] = gates
    ends = topology["permutation_ends"]
    if (not isinstance(ends, list) or len(ends) > 1024 or
            any(type(end) is not int or not 0 <= end <= 1024 for end in ends)):
        raise ValueError("invalid direct-gate permutation end offsets")
    perm_inputs = addresses("permutation_inputs")
    perm_outputs = addresses("permutation_outputs")
    if (ends or perm_inputs or perm_outputs or
            len(perm_inputs) != len(perm_outputs) or
            ends != sorted(ends) or (ends[-1] if ends else 0) != len(perm_inputs)):
        raise ValueError("bounded arithmetic source cannot emit permutation gates")
    first_permutation = sum(len(gates) for gates in gate_lists.values())
    n_rows = first_permutation + 2 * len(perm_inputs)
    if (type(topology["first_permutation_row"]) is not int or
            topology["first_permutation_row"] != first_permutation or
            n_rows < 16 or n_rows > 1024 or n_rows & (n_rows - 1) or
            report.get("padded", {}).get("qm31_ops") != n_rows or
            report.get("trace_log_size") != n_rows.bit_length() - 1):
        raise ValueError("direct-gate row layout differs from native report")
    uses = [0] * n_vars
    producers: set[int] = set()
    for gates in gate_lists.values():
        for gate in gates:
            if gate["out"] in producers:
                raise ValueError("duplicate native direct-gate producer address")
            producers.add(gate["out"])
            uses[gate["in0"]] += 1
            uses[gate["in1"]] += 1
    if any(address in producers for address in perm_outputs) or len(set(perm_outputs)) != len(perm_outputs):
        raise ValueError("duplicate permutation producer address")
    if producers | set(perm_outputs) != set(range(n_vars)):
        raise ValueError("native direct-gate variable lacks a unique producer")
    for value in (*perm_inputs, *output):
        uses[value] += 1
    uses[0] += 2 * len(perm_inputs)
    if any(value >= M31_MODULUS for value in uses):
        raise ValueError("direct-gate use count exceeds M31")
    rows: list[list[int]] = []
    for flag, gates in enumerate(gate_lists.values()):
        for gate in gates:
            rows.append([*(int(i == flag) for i in range(4)),
                         gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]])
    begin = 0
    for index, end in enumerate(ends):
        scratch = n_vars + index
        if scratch >= M31_MODULUS:
            raise ValueError("permutation scratch address exceeds M31")
        for source, target in zip(perm_inputs[begin:end], perm_outputs[begin:end], strict=True):
            rows.extend(([1, 0, 0, 0, 0, source, scratch, 1],
                         [1, 0, 0, 0, 0, scratch, target, uses[target]]))
        begin = end
    columns = topology["columns"]
    manifests = component["preprocessed_columns"]
    if (not isinstance(columns, list) or len(columns) != 8 or
            not isinstance(manifests, list) or len(manifests) != 8):
        raise ValueError("direct-gate preprocessed columns are incomplete")
    for index, (column, declared) in enumerate(zip(columns, manifests, strict=True)):
        expected = [row[index] for row in rows]
        if (not isinstance(column, dict) or set(column) != {"id", "values"} or
                column["id"] != DIRECT_COLUMN_IDS[index] or
                not isinstance(column["values"], list) or
                column["values"] != expected or
                any(type(word) is not int or not 0 <= word < M31_MODULUS
                    for word in column["values"]) or
                declared.get("id") != column["id"] or
                declared.get("commitment_index") != index or
                declared.get("rows") != n_rows or
                declared.get("log_size") != n_rows.bit_length() - 1 or
                declared.get("values_sha256") != digest(b"".join(
                    struct.pack("<I", word) for word in expected))):
            raise ValueError("emitted direct-gate selector/address columns differ from gate replay")

    # The compiler groups gates by kind. Input packing is first in `mul`
    # and `add`; source operations follow in their respective kind list.
    adds, muls, products = (gate_lists[name] for name in ("add", "mul", "pointwise_mul"))
    instructions = syntax["instructions"]
    add_count = sum(node["op"] == "add" for node in instructions)
    product_count = len(instructions) - add_count
    if (len(adds) < 3 + add_count + 8 or len(muls) < 6 or
            len(products) != product_count + 8):
        raise ValueError("direct-gate packing or source gates are missing")
    copies = {}
    for gate in adds:
        if gate["out"] in output[1:]:
            if gate["out"] in copies or gate["in1"] != 0:
                raise ValueError("public ABI output is not a unique zero-copy gate")
            copies[gate["out"]] = gate["in0"]
    if set(copies) != set(output[1:]):
        raise ValueError("native public ABI output gates are incomplete")
    input_raw = [copies[3 + index] for index in range(4)]
    if len(set(input_raw)) != 4 or any(address < 11 for address in input_raw):
        raise ValueError("public input lanes do not have distinct wires")
    for address in input_raw:
        if not any(gate == {"in0": address, "in1": 1, "out": address}
                   for gate in products):
            raise ValueError("public input M31 lane lacks its self-product producer")
    if sorted(products[product_count + 4:], key=lambda gate: gate["out"]) != [
            {"in0": address, "in1": 1, "out": address}
            for address in sorted(input_raw)]:
        raise ValueError("unexpected pointwise gates outside source and ABI lanes")
    for lane in range(1, 4):
        term = muls[lane - 1]
        packed = adds[lane - 1]
        if (term["in1"] != input_raw[lane] or
                packed["in0"] != (input_raw[0] if lane == 1 else adds[lane - 2]["out"]) or
                packed["in1"] != term["out"]):
            raise ValueError("public input pack gate topology differs from four-lane ABI")
    wire = {0: adds[2]["out"]}
    add_cursor, product_cursor = 3, 0
    source_gates = []
    for node in instructions:
        kind = node["op"]
        gate = adds[add_cursor] if kind == "add" else products[product_cursor]
        if gate["in0"] != wire[node["lhs"]] or gate["in1"] != wire[node["rhs"]]:
            raise ValueError("native source gate selector or operands differ from checked SSA")
        if gate["out"] < 11 or gate["out"] in wire.values():
            raise ValueError("native source gate does not create a fresh wire")
        wire[node["id"]] = gate["out"]
        source_gates.append({"id": node["id"], "op": kind, **gate})
        add_cursor += kind == "add"
        product_cursor += kind == "mul"
    if add_cursor != 3 + add_count or product_cursor != product_count:
        raise ValueError("native source gate schedule is incomplete")
    if [gate["out"] for gate in adds[add_cursor:add_cursor + 8]] != list(range(3, 11)):
        raise ValueError("public ABI copy gates are not in canonical order")

    # Public input lanes are copied directly from scalar M31 guesses. Four
    # pointwise masks and three inverses extract the public result.
    for lane in range(4):
        masked = products[product_count + lane]
        if masked["in0"] != wire[syntax["output"]]:
            raise ValueError("public output lane does not unpack checked source wire")
        if lane == 0 and masked["in1"] != 1:
            raise ValueError("first public result lane lacks the unit mask")
        unpacked = masked["out"]
        if lane:
            inverse = muls[3 + lane - 1]
            if inverse["in0"] != unpacked:
                raise ValueError("public output lane inverse has wrong operand")
            unpacked = inverse["out"]
        if copies[7 + lane] != unpacked:
            raise ValueError("public ABI copy differs from extracted source lane")
    for lane in range(1, 4):
        if muls[lane - 1]["in0"] != products[product_count + lane]["in1"]:
            raise ValueError("four-lane pack/unpack basis topology differs")
    if len({muls[lane]["in0"] for lane in range(3)}) != 3:
        raise ValueError("four-lane nonzero basis wires are not distinct")
    data_wires = (set(input_raw) | set(output[1:]) | set(wire.values()) |
                  {gate["out"] for gate in adds[:add_cursor]} |
                  {gate["out"] for gate in muls[:6]} |
                  {gate["out"] for gate in products[:product_count + 4]})
    for gate in (*adds[add_cursor + 8:], *gate_lists["sub"], *muls[6:]):
        if {gate["in0"], gate["in1"], gate["out"]} & data_wires:
            raise ValueError("extra native gate depends on source or public data")
    _check_constant_island(
        adds[add_cursor + 8:], gate_lists["sub"], muls[6:],
        [products[product_count + lane]["in1"] for lane in range(4)],
        [muls[3 + lane]["in1"] for lane in range(3)],
    )
    expected_constant, expected_vars, expected_rows = constant_and_padding(len(instructions))
    if n_vars != expected_vars or n_rows != expected_rows:
        raise ValueError(
            "constant derivation or padding gate schedule differs: "
            f"{n_vars} variables/{n_rows} rows, expected "
            f"{expected_vars} variables/{expected_rows} rows")
    _require_gate_schedule("add", adds[add_cursor + 8:], expected_constant["add"])
    _require_gate_schedule("sub", gate_lists["sub"], expected_constant["sub"])
    _require_gate_schedule("mul", muls[6:], expected_constant["mul"])
    exact_gates, exact_vars, exact_rows, exact_source = exact_direct_gate_schedule(syntax)
    if (exact_vars != n_vars or exact_rows != n_rows or exact_source != source_gates):
        raise ValueError("native direct-gate allocation schedule differs from checked source")
    for kind, actual in gate_lists.items():
        _require_gate_schedule(kind, actual, exact_gates[kind],
                               scope="native direct-gate allocation schedule differs")
    return source_gates


def _assets() -> tuple[str, str]:
    root = Path(__file__).resolve().parents[5]
    official = root / "deps/stwo-zig/vectors/circuit/official"
    return (digest((official / "compiled_air_constraints_v1.bin").read_bytes()),
            digest((official / "circuit_air.air_programs_v1.bin").read_bytes()))


def _checked_material(package: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    source_bytes = (package / "source.s31").read_bytes()
    expected_relation, syntax = parse_source(source_bytes)
    relation_bytes = (package / "source.s31.json").read_bytes()
    relation = read_canonical_json(package / "source.s31.json")
    if relation != expected_relation:
        raise ValueError("normalized relation differs from independent source parse")
    if read_canonical_json(package / "public-abi.json") != public_abi(syntax):
        raise ValueError("public ABI differs from checked source")
    manifest = read_canonical_json(package / "manifest.json")
    key = read_canonical_json(package / "verification-key.json")
    report = read_canonical_json(package / "cost-report.json")
    component = read_canonical_json(package / "component-manifest.json")
    topology = read_canonical_json(package / "gate-topology.json")
    source_map = read_canonical_json(package / "source-map.json")
    interface = read_canonical_json(package / "typed-interface.json")
    library_lock = read_canonical_json(package / "stdlib-lock.json")
    artifacts = manifest.get("artifacts")
    required = (
        "source.s31", "source.s31.json", "public-abi.json",
        "verification-key.json", "cost-report.json", "component-manifest.json",
        "gate-topology.json",
        "source-map.json", "typed-interface.json", "stdlib-lock.json",
    )
    if (manifest.get("schema") != "s31-package-v1" or
            not isinstance(artifacts, dict) or
            any(artifacts.get(name) != digest((package / name).read_bytes())
                for name in required) or
            source_map.get("schema") != "s31-text-source-map-v1" or
            source_map.get("source_sha256") != digest(source_bytes) or
            not isinstance(source_map.get("nodes"), dict) or
            set(source_map["nodes"]) != {node["name"] for node in relation["nodes"]} or
            interface.get("schema") != "s31-text-interface-v1" or
            interface.get("inputs") != [{
                "name": syntax["input"], "type": {"kind": "m31", "length": 4},
                "visibility": "public"}] or
            interface.get("output") != {"kind": "m31", "length": 4} or
            library_lock.get("schema") != "s31-stdlib-lock-v1" or
            library_lock.get("package") != "std" or
            library_lock.get("explicit_import") is not False or
            interface.get("stdlib") != {
                "package": "std", "version": library_lock.get("version"),
                "explicit_import": False} or
            key.get("stdlib_lock_sha256") != digest((package / "stdlib-lock.json").read_bytes())):
        raise ValueError("source text artifacts or standard library lock differ from checked package")
    projection_hash, air_hash = _assets()
    if (manifest.get("lowering") != "direct-gate" or manifest.get("fri_fold_step") != 1 or
            manifest.get("name") != relation["name"] or
            manifest.get("source_text_sha256") != digest(source_bytes) or
            manifest.get("program_sha256") != digest(relation_bytes) or
            key.get("schema") != "s31-verification-key-direct-manifest-v1" or
            key.get("profile") != "direct-m31-v4" or key.get("chip") is not None or
            key.get("name") != relation["name"] or
            key.get("program_sha256") != digest(relation_bytes) or
            key.get("projection_sha256") != projection_hash or
            key.get("air_bundle_sha256") != air_hash or
            key.get("fri", {}).get("fold_step") != 1 or
            component.get("schema") != "s31-component-manifest-direct-gate-v1" or
            component.get("profile") != "direct-m31-v4" or
            component.get("chip_call") is not None or
            component.get("claimed_sums") != 1 or
            not isinstance(component.get("components"), list) or
            len(component["components"]) != 1 or
            component["components"][0].get("name") != "qm31_ops" or
            component["components"][0].get("source_index") != 1 or
            component["components"][0].get("proof_index") != 0 or
            component["components"][0].get("base_trace_columns") != 12 or
            component["components"][0].get("interaction_trace_columns") != 8 or
            component["components"][0].get("n_constraints") != 11 or
            component["components"][0].get("preprocessed_indices") != [0, 2, 3, 1, 4, 5, 6, 7] or
            [column.get("id") for column in component.get("preprocessed_columns", [])] != [
                "qm31_ops_add_flag", "qm31_ops_sub_flag", "qm31_ops_mul_flag",
                "qm31_ops_pointwise_mul_flag", "qm31_ops_in0_address",
                "qm31_ops_in1_address", "qm31_ops_out_address", "qm31_ops_mults"] or
            report.get("input_packing") != [{
                "name": syntax["input"], "lanes": 4, "qm31_wires": 1}] or
            component != key.get("component_manifest") or
            component != report.get("component_manifest") or
            any(component.get(field) != key.get(field) for field in (
                "program_sha256", "canonical_ir_sha256", "preprocessed_root",
                "circuit_hash", "air_bundle_sha256"))):
        raise ValueError("direct-gate AIR profile or key core differs from checked package")
    schedule = gate_schedule(syntax, report)
    source_gates = check_gate_topology(syntax, topology, component, report,
                                       digest(relation_bytes))
    if any(report.get(field) != key.get(field) for field in (
            "program_sha256", "canonical_ir_sha256", "profile", "chip",
            "preprocessed_root", "circuit_hash", "padded", "trace_log_size", "fri")):
        raise ValueError("native report differs from verification key")
    material = {
        "schema": SCHEMA,
        "status": {
            "source_to_normalized": "source-to-normalized-checked",
            "native_gate_emission": "native-gate-topology-and-selectors-checked",
            "native_root_binding": "preprocessed-root-binding-assumed",
            "gate_lookup_air_pcs": "AIR/PCS-assumed",
            "admission": "python-package-only",
        },
        "source_sha256": digest(source_bytes),
        "relation_sha256": digest(relation_bytes),
        "source_ssa": syntax,
        "gate_schedule": schedule,
        "source_gates": source_gates,
        "gate_counts": {name: len(topology[name]) for name in
                        ("add", "sub", "mul", "pointwise_mul")},
        "gate_topology_sha256": digest((package / "gate-topology.json").read_bytes()),
        "public_abi": public_abi(syntax),
        "air_profile": {"lowering": "direct-gate", "profile": "direct-m31-v4",
                        "projection_sha256": projection_hash,
                        "air_bundle_sha256": air_hash,
                        "component_manifest_sha256": digest(canonical(component))},
        "key_core": {field: key.get(field) for field in KEY_FIELDS},
    }
    return material, manifest


def make_certificate(package: Path) -> dict[str, Any]:
    """Create only a certificate that this independent checker accepts."""
    material, _ = _checked_material(package)
    return material


def check_package(package: Path) -> dict[str, Any]:
    """Recompute the certificate from source bytes and all bound artifacts."""
    material, manifest = _checked_material(package)
    path = package / "correspondence-certificate.json"
    listed = manifest.get("artifacts", {}).get(path.name)
    if not isinstance(listed, str) or listed != digest(path.read_bytes()):
        raise ValueError("correspondence certificate is absent or changed")
    if read_canonical_json(path) != material:
        raise ValueError("correspondence certificate differs from independent check")
    return material
