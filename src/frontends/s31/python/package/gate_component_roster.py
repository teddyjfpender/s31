"""Package checks for the native-reconstructed gate AIR component roster.

The roster is an audited key extension, not a new proof transcript field. The
embedded native verifier rebuilds and compares it against the sealed source.
"""

from __future__ import annotations

import json
import hashlib
from pathlib import Path


KEY_SCHEMA = "s31-verification-key-gate-roster-v1"
ROSTER_SCHEMA = "s31-component-roster-gate-v1"
NAMES = (
    "eq", "qm31_ops", "triple_xor", "m_31_to_u_32", "blake_g_gate",
    "verify_bitwise_xor_8", "verify_bitwise_xor_12", "verify_bitwise_xor_4",
    "verify_bitwise_xor_7", "verify_bitwise_xor_9", "range_check_16",
)
# An independent copy of the verifier's circuit component facts. A package
# author must not be able to change lookup metadata by updating the roster,
# its internal digest, and the untrusted verification key together. Dynamic
# trace heights remain package-specific; these shapes and relation uses do not.
FACTS = (
    (4, 4, "eq_in0_address", (("Gate", 2),)),
    (12, 8, "qm31_ops_in0_address", (("Gate", 2),)),
    (20, 24, "triple_xor_input_addr_0", (("Gate", 3), ("VerifyBitwiseXor_8", 8))),
    (4, 12, "m31_to_u32_input_addr", (("Gate", 1), ("RangeCheck_16", 3))),
    (52, 52, "blake_g_gate_input_addr_a", (("Gate", 6),
        ("VerifyBitwiseXor_12", 2), ("VerifyBitwiseXor_4", 2),
        ("VerifyBitwiseXor_7", 2), ("VerifyBitwiseXor_8", 6),
        ("VerifyBitwiseXor_8_B", 2), ("VerifyBitwiseXor_9", 2))),
    (2, 4, "fixed", ()),
    (16, 32, "fixed", ()),
    (1, 4, "fixed", ()),
    (1, 4, "fixed", ()),
    (1, 4, "fixed", ()),
    (1, 4, "fixed", ()),
)
FIXED_LOGS = {5: 16, 6: 20, 7: 8, 8: 14, 9: 18, 10: 16}
ARTIFACT = "gate-component-roster.json"
TOP_FIELDS = {"schema", "profile", "program_sha256", "canonical_ir_sha256",
              "air_bundle_sha256", "preprocessed_root", "circuit_hash",
              "claimed_sums", "components", "preprocessed_columns"}
COMPONENT_FIELDS = {"name", "source_index", "proof_index", "claimed_sum_index",
                    "trace_log_size", "base_trace_columns", "interaction_trace_columns",
                    "log_size_source", "lookup_uses_per_row"}
COLUMN_FIELDS = {"id", "commitment_index", "log_size", "rows", "values_sha256"}


def digest(roster: dict) -> str:
    return digest_with_domain(roster, b"S31-GATE-COMPONENT-ROSTER-V1\x00")


def digest_with_domain(roster: dict, domain: bytes) -> str:
    """Match the Zig typed struct serialization, independent of file key order."""
    fields = ("schema", "profile", "program_sha256", "canonical_ir_sha256",
              "air_bundle_sha256", "preprocessed_root", "circuit_hash",
              "claimed_sums")
    component_fields = ("name", "source_index", "proof_index", "claimed_sum_index",
                        "trace_log_size", "base_trace_columns", "interaction_trace_columns",
                        "log_size_source")
    column_fields = ("id", "commitment_index", "log_size", "rows", "values_sha256")
    ordered = {field: roster[field] for field in fields}
    ordered["components"] = [
        {**{field: row[field] for field in component_fields},
         "lookup_uses_per_row": [
             {field: use[field] for field in ("relation_id", "uses")}
             for use in row["lookup_uses_per_row"]]}
        for row in roster["components"]
    ]
    ordered["preprocessed_columns"] = [
        {field: row[field] for field in column_fields}
        for row in roster["preprocessed_columns"]
    ]
    encoded = json.dumps(ordered, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(domain + encoded).hexdigest()


def validate(package: Path, lowering: str, artifacts: dict,
             key: dict, report: dict) -> None:
    schema = key.get("schema")
    present = ARTIFACT in artifacts or (package / ARTIFACT).exists()
    if lowering == "gate" and schema not in (
            KEY_SCHEMA, "s31-verification-key-v1", "s31-verification-key-blinded-v1"):
        raise ValueError("unsupported gate verification key schema")
    if lowering != "gate" or schema != KEY_SCHEMA:
        if (present or key.get("gate_component_roster_sha256") is not None or
                report.get("gate_component_roster") is not None or
                report.get("gate_component_roster_sha256") is not None):
            raise ValueError("unexpected gate component roster")
        return
    roster = report.get("gate_component_roster")
    if (ARTIFACT not in artifacts or not (package / ARTIFACT).is_file() or
            not isinstance(roster, dict) or roster.get("schema") != ROSTER_SCHEMA or
            roster.get("profile") != "circuit-v1" or
            roster.get("claimed_sums") != len(NAMES) or
            set(roster) != TOP_FIELDS):
        raise ValueError("gate component roster does not match sealed key")
    if any(roster.get(field) != key.get(field) for field in (
            "program_sha256", "canonical_ir_sha256", "air_bundle_sha256",
            "preprocessed_root", "circuit_hash")):
        raise ValueError("gate component roster identity differs from key")
    components = roster.get("components")
    if not isinstance(components, list) or len(components) != len(NAMES):
        raise ValueError("invalid gate component roster")
    for index, (name, component) in enumerate(zip(NAMES, components, strict=True)):
        if (not isinstance(component, dict) or set(component) != COMPONENT_FIELDS or
                component.get("name") != name or
                any(type(component.get(field)) is not int or component[field] != index
                    for field in ("source_index", "proof_index", "claimed_sum_index")) or
                type(component.get("trace_log_size")) is not int or
                component["trace_log_size"] < 0 or
                any(type(component.get(field)) is not int or component[field] <= 0
                    for field in ("base_trace_columns", "interaction_trace_columns")) or
                not isinstance(component.get("log_size_source"), str) or
                not isinstance(component.get("lookup_uses_per_row"), list)):
            raise ValueError("invalid gate component roster")
        for use in component["lookup_uses_per_row"]:
            if (not isinstance(use, dict) or set(use) != {"relation_id", "uses"} or
                    not isinstance(use.get("relation_id"), str) or
                    type(use.get("uses")) is not int or use["uses"] < 0):
                raise ValueError("invalid gate component lookup roster")
        base, interaction, source, uses = FACTS[index]
        if (component["base_trace_columns"] != base or
                component["interaction_trace_columns"] != interaction or
                component["log_size_source"] != source or
                component["lookup_uses_per_row"] != [
                    {"relation_id": relation, "uses": count}
                    for relation, count in uses] or
                (index in FIXED_LOGS and
                 component["trace_log_size"] != FIXED_LOGS[index])):
            raise ValueError("gate component facts differ from reviewed native AIR")
    columns = roster.get("preprocessed_columns")
    if not isinstance(columns, list) or len(columns) != 45:
        raise ValueError("invalid gate preprocessed column roster")
    column_ids = set()
    for index, column in enumerate(columns):
        if (not isinstance(column, dict) or set(column) != COLUMN_FIELDS or
                type(column.get("commitment_index")) is not int or
                column["commitment_index"] != index or
                not isinstance(column.get("id"), str) or not column["id"] or
                type(column.get("log_size")) is not int or
                column["log_size"] < 0 or column["log_size"] > 30 or
                type(column.get("rows")) is not int or
                column["rows"] != (1 << column["log_size"]) or
                not isinstance(column.get("values_sha256"), str) or
                len(column["values_sha256"]) != 64 or
                any(c not in "0123456789abcdef" for c in column["values_sha256"])):
            raise ValueError("invalid gate preprocessed column roster")
        if column["id"] in column_ids:
            raise ValueError("duplicate gate preprocessed column ID")
        column_ids.add(column["id"])
    for component in components:
        source = component["log_size_source"]
        if source != "fixed":
            matches = [column for column in columns if column["id"] == source]
            if len(matches) != 1 or matches[0]["log_size"] != component["trace_log_size"]:
                raise ValueError("gate component log size differs from fixed column")
    if json.loads((package / ARTIFACT).read_text()) != roster:
        raise ValueError("gate component roster artifact differs from key")
    try:
        expected = digest(roster)
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("invalid gate component roster digest input") from exc
    if (key.get("gate_component_roster_sha256") != expected or
            report.get("gate_component_roster_sha256") != expected):
        raise ValueError("gate component roster digest differs from key")
