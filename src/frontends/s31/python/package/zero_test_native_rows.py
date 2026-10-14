"""Exact source-to-fixed-Gate validation for one scalar public zero test.

The Lean `ZeroRows` theorem proves the local equations for arbitrary witnesses.
This validator binds those row *roles* to source bytes and every exported fixed
cell. It does not authenticate arbitrary proof openings or prove the native
compiler correct for other programs.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from pathlib import Path
from typing import Any

from package.correspondence import (check_exported_root, parse_canonical_json,
                                    replay_direct_topology, same_json_shape)
from package.direct_gate_schedule import I, IU, U, _Constants, gate
from package.direct_gate_main_correspondence import (_operate,
                                                     canonical_column_bytes)
from package.manifest_digest import direct_gate_v2_digest
from package.source_relation_fragment import (MAX_RELATION_NAME_CHARS, NAME,
                                              SOURCE_KEYWORDS, _tokens)

ARTIFACT = "zero-test-native-rows-certificate.json"
TOPOLOGY = "gate-topology.json"
SCHEMA = "s31-scalar-zero-test-native-rows-v1"


class UnsupportedZeroTest(ValueError):
    """The source is outside the deliberately narrow scalar control slice."""


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_source(data: bytes) -> dict[str, Any]:
    """Reparse exact text without the production lexer or elaborator.

    Whitespace and comments may vary. One public M31 input, one `is_zero`
    producer, and that producer as the sole public result are required.
    """
    try:
        tokens = _tokens(data)
    except ValueError as exc:
        raise UnsupportedZeroTest(str(exc)) from exc
    at = 0

    def take(wanted: str | None = None) -> str:
        nonlocal at
        if at == len(tokens):
            raise UnsupportedZeroTest("truncated scalar zero-test source")
        token = tokens[at]
        at += 1
        if wanted is not None and token != wanted:
            raise UnsupportedZeroTest("outside scalar zero-test grammar")
        return token

    def ident() -> str:
        token = take()
        if (NAME.fullmatch(token) is None or token in SOURCE_KEYWORDS or
                len(token) > MAX_RELATION_NAME_CHARS):
            raise UnsupportedZeroTest("invalid bounded identifier")
        return token

    if tokens[:5] == ["use", "std", "@", "1", ";"]:
        for token in ("use", "std", "@", "1", ";"):
            take(token)
    take("circuit")
    circuit = ident()
    for token in ("(", "public"):
        take(token)
    input_name = ident()
    for token in (":", "[", "m31", ";", "1", "]", ")", "->",
                  "public", "[", "m31", ";", "1", "]", "{", "let"):
        take(token)
    output_name = ident()
    for token in ("=", "std", ":", ":", "field", ":", ":", "is_zero", "("):
        take(token)
    take(input_name)
    for token in (")", ";"):
        take(token)
    take(output_name)
    if at < len(tokens) and tokens[at] == ";":
        take(";")
    take("}")
    if at != len(tokens) or len({circuit, input_name, output_name}) != 3:
        raise UnsupportedZeroTest("trailing syntax or shadowed zero-test name")
    return {"version": 1, "name": circuit,
            "inputs": [{"name": input_name, "kind": "m31", "length": 1,
                        "visibility": "public"}],
            "nodes": [{"name": output_name, "op": "is_zero", "lhs": input_name}],
            "assertions": [], "public_outputs": [output_name]}


def admitted_source_package(package: Path) -> bool:
    source = package / "source.s31"
    relation = package / "source.s31.json"
    if not source.is_file() or not relation.is_file():
        return False
    try:
        expected = parse_source(source.read_bytes())
        actual = parse_canonical_json(relation.read_bytes(), relation.name)
    except (UnsupportedZeroTest, ValueError):
        return False
    return same_json_shape(actual, expected)


def expected_schedule() -> dict[str, list[dict[str, int]]]:
    """All 512 grouped Gate rows, including constant and guessed-var islands.

    Addresses 14 and 15 are the indicator and inverse hints. The two anchor
    loops force difference=0 and x*z=0; finalization gives each hint one
    identity producer. The one-lane public result copies indicator 14.
    """
    constants = _Constants(next_address=22, pending=[(U, 2), (I, 12), (IU, 13)])
    constants.derive([])
    if constants.next_address != 281:
        raise AssertionError("scalar zero-test constant layout changed")
    add = [gate(19, 18, 19), gate(21, 20, 21),
           gate(11, 0, 3), gate(14, 0, 4),
           *(gate(0, 0, address) for address in range(5, 11)),
           *constants.adds, gate(14, 0, 14), gate(15, 0, 15),
           *(gate(1, 1, address) for address in range(281, 512))]
    return {"add": add,
            "sub": [gate(1, 14, 17), gate(16, 17, 18), *constants.subs],
            "mul": [gate(11, 15, 16), gate(11, 14, 20), *constants.muls],
            "pointwise_mul": [gate(11, 1, 11)]}


def make_certificate(package: Path) -> dict[str, Any]:
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    relation = parse_source(source_bytes)
    if not same_json_shape(parse_canonical_json(relation_bytes, "source.s31.json"), relation):
        raise ValueError("zero-test normalized relation differs from exact source")
    data = {name: parse_canonical_json((package / name).read_bytes(), name)
            for name in ("manifest.json", "verification-key.json", "cost-report.json",
                         "component-manifest.json", "public-abi.json", TOPOLOGY)}
    manifest, key, report = (data[name] for name in
                             ("manifest.json", "verification-key.json", "cost-report.json"))
    component, abi, topology = (data[name] for name in
                                ("component-manifest.json", "public-abi.json", TOPOLOGY))
    relation_digest = _hash(relation_bytes)
    if (manifest.get("lowering") != "direct-gate" or
            manifest.get("source_text_sha256") != _hash(source_bytes) or
            manifest.get("program_sha256") != relation_digest or
            manifest.get("name") != relation["name"] or
            key.get("schema") != "s31-verification-key-direct-manifest-v2" or
            key.get("profile") != "direct-m31-v4" or key.get("chip") is not None or
            key.get("program_sha256") != relation_digest or
            component.get("schema") != "s31-component-manifest-direct-gate-v2" or
            component.get("profile") != "direct-m31-v4" or
            not same_json_shape(component.get("claimed_sums"), 1) or
            key.get("manifest_precommitment_sha256") != direct_gate_v2_digest(component) or
            not same_json_shape(component, key.get("component_manifest")) or
            report.get("manifest_precommitment_sha256") != key.get("manifest_precommitment_sha256") or
            any(not same_json_shape(report.get(field), key.get(field)) for field in
                ("program_sha256", "canonical_ir_sha256", "profile", "chip",
                 "preprocessed_root", "circuit_hash", "padded", "trace_log_size")) or
            any(not same_json_shape(component.get(field), key.get(field)) for field in
                ("program_sha256", "canonical_ir_sha256", "preprocessed_root", "circuit_hash"))):
        raise ValueError("scalar zero-test key or component differs from source")
    expected_abi = {"schema": "s31-public-abi-v1",
                    "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
                    "public_inputs": [{"name": relation["inputs"][0]["name"],
                                       "kind": "m31", "length": 1}],
                    "public_outputs": [{"name": relation["public_outputs"][0],
                                        "kind": "m31", "length": 1}]}
    if not same_json_shape(abi, expected_abi):
        raise ValueError("scalar zero-test ABI differs from source")
    if (not same_json_shape(report.get("raw", {}).get("qm31_ops"), 281) or
            not same_json_shape(report.get("padded", {}).get("qm31_ops"), 512) or
            not same_json_shape(report.get("source_map"), [
                {"name": relation["inputs"][0]["name"], "canonical_id": 0,
                 "qm31_start": 0, "qm31_end": 0,
                 **{f"{kind}_{side}": 0 for kind in
                    ("eq", "triple_xor", "m31_to_u32", "blake_g")
                    for side in ("start", "end")}},
                {"name": relation["public_outputs"][0], "canonical_id": 1,
                 "qm31_start": 0, "qm31_end": 6,
                 **{f"{kind}_{side}": 0 for kind in
                    ("eq", "triple_xor", "m31_to_u32", "blake_g")
                    for side in ("start", "end")}}])):
        raise ValueError("scalar zero-test source row span differs")
    if not check_exported_root(topology, key):
        raise ValueError("scalar zero-test topology lacks fixed root")
    actual = replay_direct_topology(topology, component, report, relation_digest)
    expected = expected_schedule()
    if (topology["n_vars"] != 512 or topology["first_permutation_row"] != 512 or
            any(not same_json_shape(actual[kind], expected[kind]) for kind in expected)):
        raise ValueError("scalar zero-test native Gate schedule differs from source")
    return {"schema": SCHEMA, "capability": "source-zero-test-to-native-fixed-rows-only",
            "source_sha256": _hash(source_bytes), "relation_sha256": relation_digest,
            "topology_sha256": _hash((package / TOPOLOGY).read_bytes()),
            "preprocessed_root": key["preprocessed_root"],
            "row_roles": {
                "input_m31": {"kind": "pointwise_mul", "trace_row": 511},
                "inverse_product": {"kind": "mul", "trace_row": len(expected["add"]) + len(expected["sub"])},
                "complement": {"kind": "sub", "trace_row": len(expected["add"])},
                "inverse_difference": {"kind": "sub", "trace_row": len(expected["add"]) + 1},
                "inverse_zero_anchor": {"kind": "add", "trace_row": 0},
                "indicator_product": {"kind": "mul", "trace_row": len(expected["add"]) + len(expected["sub"]) + 1},
                "indicator_zero_anchor": {"kind": "add", "trace_row": 1},
                "public_indicator_copy": {"kind": "add", "trace_row": 3}},
            "gate_counts": {kind: len(rows) for kind, rows in expected.items()}}


def verify_artifact(package: Path, manifest: dict[str, Any]) -> bool:
    artifacts = manifest["artifacts"]
    path = package / ARTIFACT
    listed = ARTIFACT in artifacts
    present = path.exists() or path.is_symlink()
    eligible = ("source_text_sha256" in manifest and
                manifest.get("lowering") == "direct-gate" and
                admitted_source_package(package))
    if not eligible:
        if listed or present:
            raise ValueError("unsupported source carries scalar zero-test row certificate")
        return False
    topology = package / TOPOLOGY
    if (not listed or TOPOLOGY not in artifacts or not path.is_file() or
            not topology.is_file() or path.is_symlink() or topology.is_symlink()):
        raise ValueError("admitted scalar zero test lacks native row artifacts")
    actual = parse_canonical_json(path.read_bytes(), ARTIFACT)
    if not same_json_shape(actual, make_certificate(package)):
        raise ValueError("scalar zero-test row certificate differs from replay")
    return True


def expected_columns(value: int) -> tuple[list[list[int]], list[list[int]], list[int]]:
    """Reconstruct all honest base cells from source input and checked rows."""
    modulus = 2**31 - 1
    if type(value) is not int or not 0 <= value < modulus:
        raise ValueError("expected one canonical public M31 input")
    gates = expected_schedule()
    kinds = ("add", "sub", "mul", "pointwise_mul")
    reads: Counter[int] = Counter()
    for kind in kinds:
        for row in gates[kind]:
            reads[row["in0"]] += 1
            reads[row["in1"]] += 1
    reads.update((2, *range(3, 11)))
    rows = [[*(int(index == flag) for index in range(4)),
             row["in0"], row["in1"], row["out"], reads[row["out"]]]
            for flag, kind in enumerate(kinds) for row in gates[kind]]
    if len(rows) != 512 or sorted(row[6] for row in rows) != list(range(512)):
        raise ValueError("zero-test Gate schedule lacks unique producers")
    fixed = [[row[index] for row in rows] for index in range(8)]
    indicator = int(value == 0)
    inverse = 0 if value == 0 else pow(value, modulus - 2, modulus)
    zero = (0, 0, 0, 0)
    resolved: dict[int, tuple[int, int, int, int]] = {
        0: zero, 1: (1, 0, 0, 0), 2: U, 11: (value, 0, 0, 0),
        12: I, 13: IU, 14: (indicator, 0, 0, 0),
        15: (inverse, 0, 0, 0), 19: zero, 21: zero}
    producers = {row[6]: row for row in rows}
    visiting: set[int] = set()

    def resolve(address: int) -> tuple[int, int, int, int]:
        if address in resolved:
            return resolved[address]
        if address not in producers or address in visiting:
            raise ValueError("unanchored or cyclic scalar zero-test Gate address")
        visiting.add(address)
        row = producers[address]
        value_at = _operate(row[:4].index(1), resolve(row[4]), resolve(row[5]))
        visiting.remove(address)
        resolved[address] = value_at
        return value_at

    for address in range(512):
        resolve(address)
    main = [[0] * 512 for _ in range(12)]
    for index, row in enumerate(rows):
        left, right, output = (resolved[row[4]], resolved[row[5]], resolved[row[6]])
        if _operate(row[:4].index(1), left, right) != output:
            raise ValueError("zero-test asserted Gate equation failed")
        for offset, quad in ((0, left), (4, right), (8, output)):
            for coordinate in range(4):
                main[offset + coordinate][index] = quad[coordinate]
    public = [value, indicator, 0, 0, 0, 0, 0, 0]
    for address, word in enumerate(public, 3):
        if resolved[address] != (word, 0, 0, 0):
            raise ValueError("zero-test public word differs from source")
    return fixed, main, public


def check_export(value: int, physical: dict[str, Any], root: dict[str, Any]) -> str:
    """Compare all 512 fixed and 6144 main cells of an honest native export."""
    fixed, main, public = expected_columns(value)
    if (canonical_column_bytes(physical.get("fixed_columns"), 8) !=
            canonical_column_bytes(fixed, 8) or
            canonical_column_bytes(physical.get("main_columns"), 12) !=
            canonical_column_bytes(main, 12) or
            not same_json_shape(physical.get("public_words"), public) or
            not same_json_shape(root.get("public_words"), public)):
        raise ValueError("scalar zero-test native physical cells differ from source")
    digest = hashlib.sha256(canonical_column_bytes(main, 12)).hexdigest()
    if root.get("main_columns_sha256") != digest:
        raise ValueError("scalar zero-test native main digest differs")
    return digest
