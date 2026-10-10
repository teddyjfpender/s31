"""Independent, fail-closed checker for a small direct-gate S31 fragment.

The accepted grammar has one public [m31; 4] input and one public [m31; 4]
output. Its body contains 1..16 fresh `let name = left + right;` or
`let name = left .* right;` statements followed by a returned wire name.
Operands must name the input or an earlier let. No imports, calls, constants,
assertions, private inputs, or implicit coercions enter this certificate.

This checks source bytes against normalized relation and the published native
row schedule. It does not derive the native circuit hash or prove Gate lookup,
AIR-to-rational, PCS, or the installed verifier correct.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any


class UnsupportedFragment(ValueError):
    """The source is outside the certificate grammar."""


TOKEN = re.compile(r"\s+|//[^\n]*|->|\.\*|[()\[\];:{}=+]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
SCHEMA = "s31-direct-gate-correspondence-v1"
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
        ssa.append({"id": len(wires), "name": name, "op": op,
                    "lhs": wires[left], "rhs": wires[right]})
        nodes.append({"name": name, "op": op, "lhs": left, "rhs": right})
        wires[name] = len(wires)
        if len(nodes) > 16:
            raise UnsupportedFragment("more than 16 arithmetic operations")
    if not nodes:
        raise UnsupportedFragment("at least one arithmetic operation is required")
    output = identifier()
    take("}")
    if cursor != len(tokens) or output not in wires:
        raise UnsupportedFragment("trailing tokens or unbound output")
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
    source_map = read_canonical_json(package / "source-map.json")
    interface = read_canonical_json(package / "typed-interface.json")
    library_lock = read_canonical_json(package / "stdlib-lock.json")
    artifacts = manifest.get("artifacts")
    required = (
        "source.s31", "source.s31.json", "public-abi.json",
        "verification-key.json", "cost-report.json", "component-manifest.json",
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
    if any(report.get(field) != key.get(field) for field in (
            "program_sha256", "canonical_ir_sha256", "profile", "chip",
            "preprocessed_root", "circuit_hash", "padded", "trace_log_size", "fri")):
        raise ValueError("native report differs from verification key")
    material = {
        "schema": SCHEMA,
        "status": {
            "source_to_normalized": "source-to-normalized-checked",
            "native_gate_emission": "native-gate-emission-assumed",
            "gate_lookup_air_pcs": "AIR/PCS-assumed",
            "admission": "python-package-only",
        },
        "source_sha256": digest(source_bytes),
        "relation_sha256": digest(relation_bytes),
        "source_ssa": syntax,
        "gate_schedule": schedule,
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
