"""Canonical typed digest for the bounded one-call direct-chip manifest v2.

The native compiler owns this format. This independent Python implementation
lets package inspection catch an altered digest before invoking a verifier.
"""

from __future__ import annotations

import hashlib


DOMAIN = b"S31-COMPONENT-MANIFEST-PRECOMMIT-V2\0"


def direct_chip_v2_digest(manifest: dict) -> str:
    if manifest.get("schema") != "s31-component-manifest-direct-chip-v2":
        raise ValueError("unsupported direct-chip manifest digest schema")
    h = hashlib.sha256(DOMAIN)

    def uint(value: int, width: int) -> None:
        if type(value) is not int or not 0 <= value < 1 << (8 * width):
            raise ValueError("invalid typed component manifest integer")
        h.update(value.to_bytes(width, "little"))

    def text(value: str) -> None:
        if type(value) is not str:
            raise ValueError("invalid typed component manifest string")
        data = value.encode("utf-8")
        uint(len(data), 8)
        h.update(data)

    def span(value: dict) -> None:
        if type(value) is not dict:
            raise ValueError("invalid typed component manifest span")
        for name in ("tree", "start", "end"):
            uint(value[name], 4)

    def optional_uint(value: int | None) -> None:
        uint(int(value is not None), 1)
        if value is not None:
            uint(value, 4)

    def optional_span(value: dict | None) -> None:
        uint(int(value is not None), 1)
        if value is not None:
            span(value)

    for name in ("schema", "profile", "program_sha256", "canonical_ir_sha256",
                 "air_bundle_sha256", "preprocessed_root"):
        text(manifest[name])
    # circuit_hash is intentionally omitted: it depends on this digest.
    uint(manifest["composition_plan_hash"], 8)
    uint(manifest["claimed_sums"], 4)
    components = manifest["components"]
    if type(components) is not list:
        raise ValueError("invalid typed component manifest roster")
    uint(len(components), 8)
    for component in components:
        text(component["name"])
        for name in ("source_index", "proof_index", "trace_log_size", "evaluation_log_size"):
            uint(component[name], 4)
        for name in ("base_trace_columns", "interaction_trace_columns"):
            uint(component[name], 8)
        for name in ("n_constraints", "random_coefficient_offset"):
            uint(component[name], 4)
        spans = component["trace_spans"]
        uint(len(spans), 8)
        for item in spans:
            span(item)
        indices = component["preprocessed_indices"]
        uint(len(indices), 8)
        for index in indices:
            uint(index, 4)
        text(component["program_binding_sha256"])
        optional_uint(component.get("claimed_sum_index"))
        optional_span(component.get("main_trace_span"))
        optional_span(component.get("interaction_trace_span"))
        optional_uint(component.get("max_constraint_log_degree_bound"))
        relations = component.get("lookup_relation_ids")
        uint(int(relations is not None), 1)
        if relations is not None:
            uint(len(relations), 8)
            for relation in relations:
                uint(relation, 4)
    columns = manifest["preprocessed_columns"]
    uint(len(columns), 8)
    for column in columns:
        text(column["id"])
        uint(column["commitment_index"], 8)
        uint(column["log_size"], 4)
        uint(column["rows"], 8)
        text(column["values_sha256"])
    call = manifest.get("chip_call")
    uint(int(call is not None), 1)
    if call is not None:
        for name in ("call_id", "relation_id", "rounds", "constant"):
            uint(call[name], 4)
        boundary = call.get("private_boundary")
        uint(int(boundary is not None), 1)
        if boundary is not None:
            for name in ("input", "output"):
                for address in boundary[name]:
                    uint(address, 4)
    return h.hexdigest()
