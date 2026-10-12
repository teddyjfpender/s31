"""Independent audit of the mixed chip/bridge program binding.

The digest joins the registered native AIR kind and source hash to the exact
source-derived call, including all private circuit input/output addresses.
It audits an inspection report; only the generated native verifier decides
whether a proof is valid.
"""

from __future__ import annotations

import hashlib
import struct


KIND = {
    "pair_chip": 1,
    "pair_bridge": 2,
    "many_chip": 3,
    "many_bridge": 4,
}
CALL_WORDS = ("call_id", "source_node_id", "input_node_id", "rounds", "constant")


def digest(kind: str, air_source_sha256: str, call: dict) -> str:
    if kind not in KIND:
        raise ValueError("unregistered native component kind")
    try:
        air_hash = bytes.fromhex(air_source_sha256)
    except (TypeError, ValueError) as exc:
        raise ValueError("invalid native AIR source digest") from exc
    if len(air_hash) != 32 or air_source_sha256 != air_hash.hex():
        raise ValueError("invalid native AIR source digest")
    h = hashlib.sha256(b"S31-MIXED-NATIVE-COMPONENT-PROTOTYPE-V1\0")
    h.update(struct.pack("<B", KIND[kind]))
    h.update(air_hash)
    try:
        words = [call[name] for name in CALL_WORDS] + call["input"] + call["output"]
    except (KeyError, TypeError) as exc:
        raise ValueError("invalid native call") from exc
    if (len(call["input"]) != 4 or len(call["output"]) != 4 or
            any(type(word) is not int or not 0 <= word < 1 << 32 for word in words)):
        raise ValueError("invalid native call words")
    for word in words:
        h.update(struct.pack("<I", word))
    return h.hexdigest()


def check_report(manifest: dict) -> None:
    """Check every native chip/bridge slot against its exact call tuple."""
    calls = manifest["calls"]
    slots = manifest["slots"]
    if (not 1 <= len(calls) <= 8 or manifest["call_count"] != len(calls) or
            len(slots) != 1 + 2 * len(calls)):
        raise AssertionError("mixed native binding roster differs")
    for index, slot in enumerate(slots[1:], 1):
        call_id = (index - 1) // 2
        kind = ("pair" if call_id < 2 else "many") + (
            "_chip" if index % 2 else "_bridge")
        if (slot["source_kind"] != kind or slot["registry_key"] != kind or
                slot["call_id"] != call_id):
            raise AssertionError("native component kind or call index differs")
        try:
            expected = digest(kind, slot["air_source_sha256"], calls[call_id])
        except ValueError as exc:
            raise AssertionError("invalid native program binding input") from exc
        if slot["program_binding_sha256"] != expected:
            raise AssertionError("native program binding differs from call endpoints")
