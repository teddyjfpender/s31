"""Package checks for the source-derived sparse-gate AIR component roster."""

from __future__ import annotations

import json
from pathlib import Path

from package.gate_component_roster import (
    COLUMN_FIELDS, COMPONENT_FIELDS, TOP_FIELDS, digest_with_domain,
)

KEY_SCHEMA = "s31-verification-key-sparse-roster-v1"
ROSTER_SCHEMA = "s31-component-roster-sparse-gate-v1"
ARTIFACT = "sparse-component-roster.json"
FIELD = "sparse_component_roster"
DIGEST_FIELD = "sparse_component_roster_sha256"
DOMAIN = b"S31-SPARSE-GATE-COMPONENT-ROSTER-V1\x00"
# Source indices are the compiled AIR component enumeration. Proof indices are
# the compact sparse-v3 claim order, not those source indices.
COMPONENTS = (
    ("qm31_ops", 1, 12, 8, "qm31_ops_in0_address",
     (("Gate", 2),)),
    ("m_31_to_u_32", 3, 4, 12, "m31_to_u32_input_addr",
     (("Gate", 1), ("RangeCheck_16", 3))),
    ("range_check_16", 10, 1, 4, "fixed", ()),
)


def digest(roster: dict) -> str:
    return digest_with_domain(roster, DOMAIN)


def validate(package: Path, lowering: str, artifacts: dict,
             key: dict, report: dict) -> None:
    present = ARTIFACT in artifacts or (package / ARTIFACT).exists()
    if lowering != "sparse-gate":
        if (present or key.get(DIGEST_FIELD) is not None or
                report.get(FIELD) is not None or report.get(DIGEST_FIELD) is not None):
            raise ValueError("unexpected sparse component roster")
        return
    if key.get("schema") != KEY_SCHEMA:
        raise ValueError("unsupported sparse-gate verification key schema")
    roster = report.get(FIELD)
    if (ARTIFACT not in artifacts or not (package / ARTIFACT).is_file() or
            not isinstance(roster, dict) or set(roster) != TOP_FIELDS or
            roster.get("schema") != ROSTER_SCHEMA or
            roster.get("profile") != "sparse-v3" or
            roster.get("claimed_sums") != len(COMPONENTS)):
        raise ValueError("sparse component roster does not match sealed key")
    if any(roster.get(field) != key.get(field) for field in (
            "program_sha256", "canonical_ir_sha256", "air_bundle_sha256",
            "preprocessed_root", "circuit_hash")):
        raise ValueError("sparse component roster identity differs from key")
    rows = roster.get("components")
    if not isinstance(rows, list) or len(rows) != len(COMPONENTS):
        raise ValueError("invalid sparse component roster")
    columns = roster.get("preprocessed_columns")
    if not isinstance(columns, list) or len(columns) != 12:
        raise ValueError("invalid sparse fixed column roster")
    column_ids = set()
    for index, column in enumerate(columns):
        if (not isinstance(column, dict) or set(column) != COLUMN_FIELDS or
                not isinstance(column.get("id"), str) or not column["id"] or
                type(column.get("commitment_index")) is not int or
                column["commitment_index"] != index or
                type(column.get("log_size")) is not int or
                not 0 <= column["log_size"] <= 30 or
                type(column.get("rows")) is not int or
                column["rows"] != (1 << column["log_size"]) or
                not isinstance(column.get("values_sha256"), str) or
                len(column["values_sha256"]) != 64 or
                any(char not in "0123456789abcdef" for char in column["values_sha256"])):
            raise ValueError("invalid sparse fixed column roster")
        if column["id"] in column_ids:
            raise ValueError("duplicate sparse fixed column ID")
        column_ids.add(column["id"])
    for proof_index, (component, expected) in enumerate(zip(rows, COMPONENTS, strict=True)):
        name, source_index, base_width, interaction_width, source, uses = expected
        if (not isinstance(component, dict) or set(component) != COMPONENT_FIELDS or
                component.get("name") != name or
                type(component.get("source_index")) is not int or
                component["source_index"] != source_index or
                any(type(component.get(field)) is not int or component[field] != proof_index
                    for field in ("proof_index", "claimed_sum_index")) or
                type(component.get("base_trace_columns")) is not int or
                component["base_trace_columns"] != base_width or
                type(component.get("interaction_trace_columns")) is not int or
                component["interaction_trace_columns"] != interaction_width or
                type(component.get("trace_log_size")) is not int or
                component.get("log_size_source") != source or
                component.get("lookup_uses_per_row") != [
                    {"relation_id": relation, "uses": count} for relation, count in uses]):
            raise ValueError("invalid sparse component geometry")
        if source == "fixed":
            if component["trace_log_size"] != 16:
                raise ValueError("invalid sparse fixed table log size")
        elif (source not in column_ids or
              next(c["log_size"] for c in columns if c["id"] == source) !=
              component["trace_log_size"]):
            raise ValueError("sparse component log size differs from fixed column")
    if json.loads((package / ARTIFACT).read_text()) != roster:
        raise ValueError("sparse component roster artifact differs from key")
    try:
        expected_digest = digest(roster)
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("invalid sparse component roster digest input") from exc
    if key.get(DIGEST_FIELD) != expected_digest or report.get(DIGEST_FIELD) != expected_digest:
        raise ValueError("sparse component roster digest differs from key")
