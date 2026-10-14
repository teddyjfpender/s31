#!/usr/bin/env python3
"""Pin the audit-only XDM04 Zig loop reviewed against the Lean recurrence.

The exact SHA-256 and function-local order checks prevent a silent change to
the reviewed capture/check/audit handoff. This is source evidence, not a
Zig-to-Lean semantics proof or a production verifier admission gate.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.release.pcs_fri_cas05_source_profile import _function, _ordered


AUDIT_SOURCE = ROOT / "formal/s31/tests/lib/pcs_xdm04_mixed_certificate.zig"
AUDIT_SHA256 = "be8ebf65be1ee2a50abb99662c4e696a1a2dce6e6ef5115597f5d4121f3a91eb"


def check_audit_source(source: bytes, *, require_digest: bool = True) -> None:
    if require_digest and hashlib.sha256(source).hexdigest() != AUDIT_SHA256:
        raise ValueError("reviewed XDM04 audit-only Zig source changed")
    decoded = source.decode("utf-8")
    _ordered(_function(decoded, "pub fn check(self: Opening)"),
             "opening depth, transposed index, and root",
             "self.native_index <",
             "self.steps.len == self.native_level",
             "self.path_position == pathPosition(",
             "sameHash(self.replay(), self.root)")
    _ordered(_function(decoded, "pub fn openingAt(self: *const Capture,"),
             "capture row and mixed-path fields",
             "const index = xdm.pairBase(self.raw_queries[query], height) + j;",
             "const row_values = try self.queriedRow(height, query, j);",
             "const first_row = try self.row(height, index);",
             "if (!value.eql(earlier)) return error.InvalidXdm04Certificate;",
             "const sibling_index = topology.sibling(@intCast(at_level), at_index);",
             "const parent_index = topology.parent(@intCast(at_level), at_index);",
             "step.* = .{",
             ".sibling = sibling,",
             ".inserted_row = if (parent_height > 0 and parent_height < self.profile.height_count)",
             ".path_position = pathPosition(level, index),")
    audit = _function(decoded, "pub fn auditAt(self: *const Capture,")
    _ordered(audit,
             "capture parent recurrence",
             "var opening = try self.openingAt(height, query, j);",
             "if (!opening.check()) return error.InvalidXdm04Certificate;",
             "var current = if (opening.children)",
             "tree.hashInserted(children.left, children.right, opening.row)",
             "tree.hashLeaf(opening.row);",
             "for (opening.steps) |step| {",
             "const left = if (position & 1 == 0) current else step.sibling;",
             "const right = if (position & 1 == 0) step.sibling else current;",
             "current = if (step.inserted_row)",
             "tree.hashInserted(left, right, inserted)",
             "tree.hashUpper(left, right);",
             "at_index = topology.parent(@intCast(at_level), at_index);",
             "position >>= 1;")
    node_guard = "if (!sameHash(current, self.nodes.get(key(at_level, at_index))"
    if (audit.count(node_guard) != 2 or
        not (audit.index(node_guard) < audit.index("for (opening.steps) |step| {") <
             audit.index("position >>= 1;") < audit.rindex(node_guard))):
        raise ValueError("reviewed XDM04 audit node guards changed")
    _ordered(_function(decoded, "pub fn auditAll(self: *const Capture)"),
             "all returned rows audited",
             "for (self.raw_queries, 0..) |_, query| {",
             "for (0..self.profile.height_count) |height| {",
             "for (0..2) |j| try self.auditAt(height, query, j);")
    _ordered(_function(decoded, "pub fn verifyAndCapture(allocator:"),
             "native success before independent capture audit",
             "var opened = try xdm.verifyAndCollect(",
             "try parseHeader(&cursor, expected, expected_root);",
             "try putNode(&nodes, k, base + j, tree.hashLeaf(",
             "tree.hashInserted(left, right, opened.values[height][offset..][0..cols])",
             "try putNode(&nodes, level - 1, parent, tree.hashUpper(left, right));",
             "try capture.auditAll();",
             "return capture;")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=AUDIT_SOURCE)
    args = parser.parse_args()
    check_audit_source(args.source.read_bytes())
    print("reviewed XDM04 audit-only Zig loop: source pin and handoff OK")


if __name__ == "__main__":
    main()
