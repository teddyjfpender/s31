#!/usr/bin/env python3
"""Nonadmitting byte specification for a proposed versioned Gate BCS profile.

This module does not implement or select a native prover/verifier. It defines
the exact input framing that a future Zig profile would need to refine. It
does not establish a random-oracle reduction or assign native security bits.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from enum import IntEnum
from typing import Callable

DOMAIN = b"S31BCS2"
PROOF_MAGIC = b"S31NAT9F"
M31_MODULUS = (1 << 31) - 1
HEADER_BYTES = 7 + 1 + 8 + 8


class Role(IntEnum):
    FIELD_ABSORB = 1
    ROOT_ABSORB = 2
    NONCE_ABSORB = 3
    RAW_WORD_DRAW = 4
    POW_PREFIX = 5
    POW_TRIAL = 6
    MERKLE_LEAF = 7
    MERKLE_PARENT = 8
    TREE_CONTEXT = 9
    STATEMENT = 10


@dataclass(frozen=True)
class EventStep:
    name: str
    role: Role
    event: int


@dataclass(frozen=True)
class StatementBinding:
    """Candidate fixed 264-byte statement; all digests are verifier-derived.

    The eventual selector must derive these from a sealed key and checked
    geometry, never from unvalidated proof-controlled bytes.
    """

    key_digest: bytes
    circuit_digest: bytes
    fri_config_digest: bytes
    source_tree_descriptors: tuple[bytes, bytes, bytes, bytes]
    line_profile_digest: bytes

    def encode(self) -> bytes:
        if type(self.source_tree_descriptors) is not tuple or len(self.source_tree_descriptors) != 4:
            raise ValueError("statement needs four source-tree descriptors")
        parts = (self.key_digest, self.circuit_digest, self.fri_config_digest,
                 *self.source_tree_descriptors, self.line_profile_digest)
        return PROOF_MAGIC + b"".join(_bytes(part, "statement digest", 32) for part in parts)


def initial_digest(statement: StatementBinding) -> bytes:
    if type(statement) is not StatementBinding:
        raise ValueError("expected a statement binding")
    return hash_frame(Role.STATEMENT, 0, statement.encode())


def candidate_paired_gate_plan(fold_heights: tuple[int, ...]) -> tuple[EventStep, ...]:
    """Unselected P05 candidate order; event ordinals are verifier-derived.

    A future wire version must freeze the actual height roster and exact
    transcript stages. `fold_heights` is strictly descending; the final
    height has terminal coefficients instead of new pair commitments.
    """
    if (type(fold_heights) is not tuple or not fold_heights or
            any(type(h) is not int or not 0 <= h < 1 << 32 for h in fold_heights) or
            any(a <= b for a, b in zip(fold_heights, fold_heights[1:]))):
        raise ValueError("fold heights must be nonempty, u32 and descending")
    events: list[tuple[str, Role]] = [
        ("statement", Role.STATEMENT),
        ("fixed_root", Role.ROOT_ABSORB),
        ("circuit_identity", Role.ROOT_ABSORB),
        ("public_values", Role.FIELD_ABSORB),
        ("main_root", Role.ROOT_ABSORB),
        ("interaction_pow_prefix", Role.POW_PREFIX),
        ("interaction_pow_trial", Role.POW_TRIAL),
        ("interaction_nonce", Role.NONCE_ABSORB),
        ("lookup_pair", Role.RAW_WORD_DRAW),
        ("interaction_claim", Role.FIELD_ABSORB),
        ("interaction_root", Role.ROOT_ABSORB),
        ("composition_gamma", Role.RAW_WORD_DRAW),
        ("composition_root", Role.ROOT_ABSORB),
        ("oods_seed", Role.RAW_WORD_DRAW),
        ("sampled_values", Role.FIELD_ABSORB),
        ("batch_lambda", Role.RAW_WORD_DRAW),
    ]
    for height in fold_heights:
        events.append((f"fold_alpha_h{height}", Role.RAW_WORD_DRAW))
        if height != fold_heights[-1]:
            events.append((f"original_root_h{height}", Role.ROOT_ABSORB))
            events.append((f"own_quotient_root_h{height}", Role.ROOT_ABSORB))
    events.extend((
        ("original_terminal_coefficients", Role.FIELD_ABSORB),
        ("own_quotient_terminal_coefficients", Role.FIELD_ABSORB),
        ("fri_pow_prefix", Role.POW_PREFIX),
        ("fri_pow_trial", Role.POW_TRIAL),
        ("fri_nonce", Role.NONCE_ABSORB),
        ("raw_queries", Role.RAW_WORD_DRAW),
    ))
    return tuple(EventStep(name, role, i) for i, (name, role) in enumerate(events))


def _u32(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 32:
        raise ValueError("value is not a u32")
    return value.to_bytes(4, "little")


def _u64(value: int) -> bytes:
    if type(value) is not int or not 0 <= value < 1 << 64:
        raise ValueError("value is not a u64")
    return value.to_bytes(8, "little")


def _bytes(value: bytes, label: str, size: int | None = None) -> bytes:
    if type(value) is not bytes or (size is not None and len(value) != size):
        raise ValueError(f"{label} must be {size or 'a byte string'}")
    return value


def frame(role: Role, event: int, payload: bytes) -> bytes:
    """One injective tagged message: magic | role | lenLE64 | eventLE64 | body."""
    if type(role) is not Role:
        raise ValueError("unknown BCS frame role")
    _bytes(payload, "payload")
    return DOMAIN + bytes([role]) + _u64(len(payload)) + _u64(event) + payload


def parse_frame(message: bytes) -> tuple[Role, int, bytes]:
    """Reject malformed, unknown-role, or noncanonical-length messages."""
    _bytes(message, "message")
    if len(message) < HEADER_BYTES or message[:7] != DOMAIN:
        raise ValueError("invalid BCS frame domain or length")
    try:
        role = Role(message[7])
    except ValueError as exc:
        raise ValueError("unknown BCS frame role") from exc
    size = int.from_bytes(message[8:16], "little")
    event = int.from_bytes(message[16:24], "little")
    if len(message) - HEADER_BYTES != size:
        raise ValueError("BCS frame length mismatch")
    return role, event, message[24:]


def hash_frame(role: Role, event: int, payload: bytes) -> bytes:
    return hashlib.blake2s(frame(role, event, payload), digest_size=32).digest()


def absorb_field(digest: bytes, event: int, limbs: tuple[int, ...]) -> bytes:
    """Only canonical M31 limbs; four limbs per QM31 value."""
    _bytes(digest, "digest", 32)
    if type(limbs) is not tuple or len(limbs) % 4 or any(
            type(x) is not int or not 0 <= x < M31_MODULUS for x in limbs):
        raise ValueError("noncanonical QM31 array")
    return hash_frame(Role.FIELD_ABSORB, event,
                      digest + b"".join(_u32(x) for x in limbs))


def absorb_root(digest: bytes, event: int, root: bytes) -> bytes:
    return hash_frame(Role.ROOT_ABSORB, event,
                      _bytes(digest, "digest", 32) + _bytes(root, "root", 32))


def absorb_nonce(digest: bytes, event: int, nonce: int) -> bytes:
    return hash_frame(Role.NONCE_ABSORB, event,
                      _bytes(digest, "digest", 32) + _u64(nonce))


def raw_words(digest: bytes, event: int, counter: int) -> tuple[int, ...]:
    block = hash_frame(Role.RAW_WORD_DRAW, event,
                       _bytes(digest, "digest", 32) + _u32(counter))
    return tuple(int.from_bytes(block[i:i + 4], "little") for i in range(0, 32, 4))


CHALLENGE_BLOCK_CAP = 8


def canonical_m31_block(words: tuple[int, ...]) -> tuple[int, ...] | None:
    """Reject the entire block when a word is outside the two-preimage range."""
    if type(words) is not tuple or len(words) != 8 or any(
            type(x) is not int or not 0 <= x < 1 << 32 for x in words):
        raise ValueError("expected eight raw u32 words")
    if any(x >= 2 * M31_MODULUS for x in words):
        return None
    return tuple(x - M31_MODULUS if x >= M31_MODULUS else x for x in words)


def draw_challenge_m31_limbs(
    digest: bytes, event: int, first_counter: int = 0,
    oracle: Callable[[bytes, int, int], tuple[int, ...]] = raw_words,
) -> tuple[tuple[int, ...], int]:
    """Two QM31s as eight limbs, plus next checked block counter.

    The optional oracle is for deterministic rejection tests only. Native
    execution always uses the framed BLAKE2s raw-word oracle.
    """
    _bytes(digest, "digest", 32)
    _u64(event)
    _u32(first_counter)
    for attempt in range(CHALLENGE_BLOCK_CAP):
        counter = first_counter + attempt
        if counter >= 1 << 32:
            raise ValueError("challenge block counter exhausted")
        canonical = canonical_m31_block(oracle(digest, event, counter))
        if canonical is not None:
            return canonical, counter + 1
    raise ValueError("challenge block cap exhausted")


def pow_trial(digest: bytes, prefix_event: int, trial_event: int,
              difficulty: int, nonce: int) -> bytes:
    """Two scheduled oracle events; caller still proves grinding law/budget."""
    if prefix_event == trial_event:
        raise ValueError("PoW prefix and trial must have distinct events")
    prefix = hash_frame(Role.POW_PREFIX, prefix_event,
                        _bytes(digest, "digest", 32) + _u32(difficulty))
    return hash_frame(Role.POW_TRIAL, trial_event, prefix + _u64(nonce))


def tree_context(descriptor: bytes) -> bytes:
    """Descriptor must bind tree kind, height, column roster, and protocol key."""
    return hash_frame(Role.TREE_CONTEXT, 0, _bytes(descriptor, "descriptor"))


def merkle_leaf(context: bytes, row: tuple[int, ...]) -> bytes:
    _bytes(context, "context", 32)
    if type(row) is not tuple or any(type(x) is not int or not 0 <= x < M31_MODULUS
                                     for x in row):
        raise ValueError("noncanonical Merkle row")
    return hash_frame(Role.MERKLE_LEAF, 0,
                      context + b"".join(_u32(x) for x in row))


def merkle_parent(context: bytes, level: int, left: bytes, right: bytes) -> bytes:
    if type(level) is not int or not 0 <= level < 1 << 32:
        raise ValueError("invalid Merkle parent level")
    return hash_frame(Role.MERKLE_PARENT, level,
                      _bytes(context, "context", 32) +
                      _bytes(left, "left child", 32) + _bytes(right, "right child", 32))


def report() -> dict:
    return {
        "schema": "s31-proposed-framed-bcs-v2-byte-spec-v1",
        "status": "candidate_encoding_only_no_native_selector_or_rom_theorem",
        "new_proof_magic_reserved": PROOF_MAGIC.decode("ascii"),
        "domain_hex": DOMAIN.hex(),
        "frame": "domain[7] || role[1] || payload_len_u64_le[8] || event_u64_le[8] || payload",
        "role_values": {role.name.lower(): int(role) for role in Role},
        "paired_gate_candidate_example_plan": [
            {"name": step.name, "role": step.role.name.lower(), "event": step.event}
            for step in candidate_paired_gate_plan((17, 16))
        ],
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "requirements_before_selection": [
            "versioned Zig prover/verifier and package/key dispatch with old magic unchanged",
            "sealed-key derivation and checked geometry for all eight statement digests",
            "source-bound parity for every root, field, nonce, query, PoW, leaf and parent call",
            "exact nonterminal M31 rejection, eight-block cap and adaptive exhaustion accounting",
            "tree descriptor binding, canonical row encoding and Merkle path refinement",
            "adaptive ROM/BCS reduction including two grinding barriers and T hash work",
            "matching degree-corrected PCS/FRI theorem and complete P09 round ledger",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-native-soundness", action="store_true")
    args = parser.parse_args()
    if args.require_native_soundness:
        parser.error("framed BCS v2 has no native selector or ROM theorem")
    print(json.dumps(report(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
