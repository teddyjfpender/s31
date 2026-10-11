"""Independent typed digest reader for the experimental V4 component roster.

The Zig inspector emits the source-owned manifest as JSON. This module hashes
that JSON with the documented V4 wire order so an auditor can compare the
result with the inspector report and the proof envelope without trusting Zig's
digest routine. It does not authenticate the inspector executable or prove AIR
soundness.
"""

from __future__ import annotations

import hashlib


DOMAIN = b"S31-BOUNDED-COMPONENT-MANIFEST-V4\0"
ROLES = {"circuit": 0, "chip": 1, "bridge": 2}
NATIVE_KINDS = {"tagged_chip": 0, "tagged_bridge": 1}
KINDS = {"u16": 0, "m31": 1}


def bounded_v4_digest(manifest: dict) -> str:
    """Return the lowercase SHA-256 of a typed V4 manifest JSON object."""
    if type(manifest) is not dict or manifest.get("schema_version") != "s31-component-manifest-bounded-call-plan-v4":
        raise ValueError("unsupported V4 component manifest schema")
    if manifest.get("proof_profile") != "direct-m31-bounded-call-plan-v4":
        raise ValueError("unsupported V4 proof profile")
    h = hashlib.sha256(DOMAIN)

    def uint(value: int, width: int) -> None:
        if type(value) is not int or not 0 <= value < 1 << (8 * width):
            raise ValueError("invalid V4 typed integer")
        h.update(value.to_bytes(width, "little"))

    def count(value: object, maximum: int) -> list:
        if type(value) is not list or len(value) > maximum:
            raise ValueError("invalid V4 list")
        uint(len(value), 4)
        return value

    def fixed_bytes(value: object) -> None:
        if type(value) is not list or len(value) != 32:
            raise ValueError("invalid V4 digest bytes")
        for byte in value:
            if type(byte) is not int or not 0 <= byte <= 255:
                raise ValueError("invalid V4 digest byte")
        h.update(bytes(value))

    def text(value: object) -> None:
        if type(value) is not str:
            raise ValueError("invalid V4 text")
        encoded = value.encode("utf-8")
        uint(len(encoded), 8)
        h.update(encoded)

    def span(value: object) -> None:
        if type(value) is not dict:
            raise ValueError("invalid V4 span")
        uint(value["tree"], 1)
        uint(value["start"], 4)
        uint(value["end"], 4)

    text(manifest["schema_version"])
    text(manifest["proof_profile"])
    for name in ("source_sha256", "canonical_ir_sha256", "bundle_sha256",
                 "native_template_sha256", "preprocessed_root"):
        fixed_bytes(manifest[name])

    calls = count(manifest["calls"], 8)
    if not calls:
        raise ValueError("empty V4 call roster")
    for call in calls:
        for name in ("call_id", "source_node_id", "input_node_id", "rounds", "constant"):
            uint(call[name], 4)
        endpoints = call["endpoints"]
        uint(int(endpoints is not None), 1)
        if endpoints is not None:
            for name in ("input", "output"):
                values = endpoints[name]
                if type(values) is not list or len(values) != 4:
                    raise ValueError("invalid V4 endpoint tuple")
                for address in values:
                    uint(address, 4)

    for output in count(manifest["public_outputs"], 8):
        text(output["name"])
        uint(output["canonical_node_id"], 4)
        uint(KINDS[output["kind"]], 1)
        for name in ("length", "word_offset"):
            uint(output[name], 4)
    uint(manifest["public_word_count"], 4)
    pcs = manifest["pcs"]
    for name in ("pow_bits", "log_blowup_factor", "last_layer_degree_bound", "queries", "fold_step"):
        uint(pcs[name], 4)
    uint(manifest["max_component_trace_log_size"], 4)
    geometry = manifest["native_preflight"]
    uint(int(geometry is not None), 1)
    if geometry is not None:
        for name in ("tree_columns", "sample_width_limits"):
            values = geometry[name]
            if type(values) is not list or len(values) != 4:
                raise ValueError("invalid V4 PCS tree geometry")
            for value in values:
                uint(value, 4)
        for name in ("max_column_log_size", "composition_log_size", "composition_split"):
            uint(geometry[name], 4)

    components = count(manifest["components"], 17)
    if len(components) != 1 + 2 * len(calls) or manifest["claimed_sums"] != len(components):
        raise ValueError("invalid V4 component count")
    for component in components:
        uint(ROLES[component["role"]], 1)
        call_id = component["call_id"]
        uint(int(call_id is not None), 1)
        if call_id is not None:
            uint(call_id, 4)
        source = component["source"]
        if type(source) is not dict or len(source) != 1:
            raise ValueError("invalid V4 component source")
        if "bundled_air" in source:
            bundled = source["bundled_air"]
            uint(0, 1)
            uint(bundled["index"], 4)
            fixed_bytes(bundled["bundle_sha256"])
            fixed_bytes(bundled["selected_program_sha256"])
        elif "native_air" in source:
            native = source["native_air"]
            uint(1, 1)
            uint(NATIVE_KINDS[native["kind"]], 1)
            fixed_bytes(native["program_binding_sha256"])
        else:
            raise ValueError("invalid V4 source kind")
        for name in ("proof_index", "claimed_sum_index", "trace_log_size", "evaluation_log_size"):
            uint(component[name], 4)
        span(component["main"])
        span(component["interaction"])
        for name in ("n_constraints", "random_coefficient_offset"):
            uint(component[name], 4)
        for index in count(component["preprocessed_indices"], 8):
            uint(index, 4)
        for relation_id in count(component["lookup_relation_ids"], 2):
            uint(relation_id, 4)
    for name in ("claimed_sums", "total_constraints", "main_columns", "interaction_columns"):
        uint(manifest[name], 4)
    return h.hexdigest()
