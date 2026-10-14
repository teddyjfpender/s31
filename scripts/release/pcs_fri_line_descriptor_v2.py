#!/usr/bin/env python3
"""Candidate line-tree descriptor bytes for the unselected S31NAT9F profile.

This fixes an auditable encoding and event map. It does not establish sealed
key custody, Merkle binding, a random-oracle reduction, or release admission.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import IntEnum

from scripts.release.pcs_fri_framed_bcs_v2 import (
    Role, StatementBinding, _bytes, _u32, _u64, candidate_paired_gate_plan,
    hash_frame,
)

TREE_MAGIC = b"S31LTDV2"
MANIFEST_MAGIC = b"S31LTMV2"
PROFILE_BYTES = b"S31LINE2S31P2LEFS31P2PARM31LE32|P64"
MAX_FOLD_HEIGHTS = 64
MAX_COLUMNS = 256
MAX_MANIFEST_BYTES = 1 << 19


class Track(IntEnum):
    ORIGINAL = 1
    OWN_QUOTIENT = 2


def line_hash_profile_digest() -> bytes:
    """Fixed leaf/parent personalization profile; not a tree descriptor."""
    return hash_frame(Role.TREE_CONTEXT, 0, PROFILE_BYTES)


@dataclass(frozen=True)
class LineTreeDescriptorV2:
    key_digest: bytes
    profile_digest: bytes
    track: Track
    fold_height: int
    tree_log_size: int
    root_event: int
    column_descriptors: tuple[bytes, ...]

    def encoded_size(self) -> int:
        if type(self.track) is not Track:
            raise ValueError("unknown line track")
        if type(self.tree_log_size) is not int or not 0 <= self.tree_log_size < 64:
            raise ValueError("tree log size must fit a u64 path index")
        if type(self.column_descriptors) is not tuple or not 1 <= len(self.column_descriptors) <= MAX_COLUMNS:
            raise ValueError("line tree needs a bounded nonempty column roster")
        columns = tuple(_bytes(d, "column descriptor", 32)
                        for d in self.column_descriptors)
        if len(set(columns)) != len(columns):
            raise ValueError("column identity descriptors must be unique")
        _u32(self.fold_height)
        _u64(self.root_event)
        _bytes(self.key_digest, "key digest", 32)
        _bytes(self.profile_digest, "profile digest", 32)
        return 93 + 32 * len(columns)

    def encode(self) -> bytes:
        self.encoded_size()
        return (TREE_MAGIC + bytes([self.track]) + _u32(self.fold_height) +
                _u32(self.tree_log_size) + _u64(self.root_event) +
                _bytes(self.key_digest, "key digest", 32) +
                _bytes(self.profile_digest, "profile digest", 32) +
                _u32(len(self.column_descriptors)) +
                b"".join(self.column_descriptors))


@dataclass(frozen=True)
class LineTreeManifestV2:
    key_digest: bytes
    fold_heights: tuple[int, ...]
    trees: tuple[LineTreeDescriptorV2, ...]

    def validate(self) -> None:
        _bytes(self.key_digest, "key digest", 32)
        if (type(self.fold_heights) is not tuple or
                not 1 <= len(self.fold_heights) <= MAX_FOLD_HEIGHTS or
                any(type(h) is not int or not 0 <= h < 1 << 32
                    for h in self.fold_heights) or
                any(a <= b for a, b in zip(self.fold_heights, self.fold_heights[1:]))):
            raise ValueError("fold heights must be bounded, u32 and descending")
        if type(self.trees) is not tuple or len(self.trees) != 2 * (len(self.fold_heights) - 1):
            raise ValueError("wrong number of nonterminal line trees")
        plan = candidate_paired_gate_plan(self.fold_heights)
        root_events = tuple(step for step in plan if step.name.startswith(
            ("original_root_h", "own_quotient_root_h")))
        if len(root_events) != len(self.trees):
            raise ValueError("candidate line-root event count mismatch")
        profile = line_hash_profile_digest()
        for i, (tree, step) in enumerate(zip(self.trees, root_events)):
            if type(tree) is not LineTreeDescriptorV2:
                raise ValueError("invalid line descriptor")
            tree.encoded_size()
            expected_track = Track.ORIGINAL if i % 2 == 0 else Track.OWN_QUOTIENT
            expected_height = self.fold_heights[i // 2]
            if (tree.key_digest != self.key_digest or tree.profile_digest != profile or
                    tree.track != expected_track or tree.fold_height != expected_height or
                    tree.root_event != step.event or step.role is not Role.ROOT_ABSORB):
                raise ValueError("line descriptor does not match verifier-owned event plan")

    def encode(self) -> bytes:
        self.validate()
        profile = line_hash_profile_digest()
        size = (8 + 32 + 32 + 4 + 4 * len(self.fold_heights) + 4 +
                sum(4 + tree.encoded_size() for tree in self.trees))
        if size > MAX_MANIFEST_BYTES:
            raise ValueError("line manifest exceeds protocol byte cap")
        return (MANIFEST_MAGIC + self.key_digest + profile +
                _u32(len(self.fold_heights)) +
                b"".join(_u32(h) for h in self.fold_heights) +
                _u32(len(self.trees)) +
                b"".join(_u32(len(encoded)) + encoded
                         for encoded in (tree.encode() for tree in self.trees)))

    def digest(self) -> bytes:
        return hash_frame(Role.TREE_CONTEXT, 0, self.encode())

    def matches_statement(self, statement: StatementBinding) -> bool:
        if type(statement) is not StatementBinding:
            raise ValueError("expected StatementBinding")
        return (statement.key_digest == self.key_digest and
                statement.line_profile_digest == self.digest())
