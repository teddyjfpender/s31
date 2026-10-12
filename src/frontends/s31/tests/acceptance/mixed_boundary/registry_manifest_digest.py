"""Recompute the version 1 mixed registry audit digest from a JSON report.

This is independent of the Zig serializer. It authenticates no verifier key:
the verifier still owns the source, AIR bundle, and fixed proof profile.
"""

from __future__ import annotations

import hashlib
import struct


KEY = {"bundled_circuit": 0, "pair_chip": 1, "pair_bridge": 2,
       "many_chip": 3, "many_bridge": 4}
ROLE = {"circuit": 0, "chip": 1, "bridge": 2}


def digest(report: dict) -> str:
    h = hashlib.sha256()
    h.update(b"S31-MIXED-REGISTRY-MANIFEST-V1\0")

    def u8(value: int) -> None:
        h.update(struct.pack("<B", value))

    def u32(value: int) -> None:
        h.update(struct.pack("<I", value))

    def sha(name: str, obj: dict) -> None:
        raw = bytes.fromhex(obj[name])
        assert len(raw) == 32, name
        h.update(raw)

    u32(report["registry_manifest_version"])
    u32(report["registry_version"])
    for name in ("source_sha256", "canonical_ir_sha256", "fixed_root",
                 "manifest_sha256", "descriptor_sha256"):
        sha(name, report)
    calls = report["calls"]
    assert len(calls) == report["call_count"]
    u8(len(calls))
    for call in calls:
        for name in ("call_id", "source_node_id", "input_node_id", "rounds", "constant"):
            u32(call[name])
        assert len(call["input"]) == len(call["output"]) == 4
        for value in (*call["input"], *call["output"]):
            u32(value)

    slots = report["slots"]
    assert len(slots) == report["slot_count"]
    u32(len(slots))
    for slot in slots:
        u8(KEY[slot["registry_key"]])
        u32(slot["registry_id"])
        u32(slot["registry_version"])
        u8(ROLE[slot["registry_role"]])
        call_id = slot["call_id"]
        u8(int(call_id is not None))
        if call_id is not None:
            u32(call_id)
        for name in ("proof_index", "claimed_sum_index", "trace_log_size",
                     "evaluation_log_size", "main_offset", "main_columns",
                     "interaction_offset", "interaction_columns",
                     "constraint_offset", "n_constraints"):
            u32(slot[name])
        fixed = slot["preprocessed_indices"]
        u8(len(fixed))
        for index in fixed:
            u32(index)
        relations = slot["relation_ids"]
        u8(len(relations))
        for relation in relations:
            u32(relation)
        sha("air_source_sha256", slot)
        sha("program_binding_sha256", slot)
    for name in ("main_columns", "interaction_columns", "total_constraints"):
        u32(report[name])
    return h.hexdigest()
