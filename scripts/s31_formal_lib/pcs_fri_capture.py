"""Pinned native lifted-multiproof control-flow contract for the Lean model.

This checks selected source stages and their order; it does not prove Zig
execution refines `MultiproofCapture.follow` or any cryptographic assumption.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_capture_source(source: str) -> None:
    verify = region(source, "fn verifyImpl(", "fn lessByLogSize(")
    ordered_once(
        verify, "lifted Merkle query and capture",
        "if (queried_values.len != self.column_log_sizes.len)",
        "if (self.height < @bitSizeOf(usize))",
        "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
        "const query_order = try allocator.alloc(usize, query_positions.len);",
        "std.sort.heap(\n                usize,\n                query_order,",
        "for (query_order) |original_index| {",
        "if (unique_positions.items.len == 0 or",
        "std.sort.heap(usize, col_indices, self.column_log_sizes, lessByLogSize);",
        "if (sorted_index == 0 or position != query_positions[query_order[sorted_index - 1]]) {",
        "return MerkleVerificationError.DuplicateQueryMismatch;",
        "hasher.updateLeaf(row);",
        "const first = prev_layer.items[p];",
        "if (p + 1 < prev_layer.items.len and (first.idx ^ 1) == prev_layer.items[p + 1].idx)",
        "siblings[p] = second.hash;",
        "chunk_len = 2;",
        "if (witness_idx >= decommitment.hash_witness.len)",
        "const witness = decommitment.hash_witness[witness_idx];",
        "witness_idx += 1;",
        "if ((first.idx & 1) == 0)",
        "siblings[p] = witness;",
        ".idx = first.idx >> 1,",
        ".hash = H.hashChildren(.{ .left = left_hash, .right = right_hash }),",
        "p += chunk_len;",
        "const ancestor = position >> @intCast(layer);",
        "std.debug.assert(prev_layer.items[node_index].idx == ancestor);",
        "paths[unique_index * path_depth + layer] = siblings[node_index];",
        "prev_layer.clearRetainingCapacity();",
        "try prev_layer.appendSlice(allocator, curr.items);",
        "if (witness_idx != decommitment.hash_witness.len)",
        "if (prev_layer.items.len != 1) return MerkleVerificationError.RootMismatch;",
        "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))",
        "const source_start = unique_index * path_depth;",
        "const destination_start = original_index * path_depth;",
        "@memcpy(\n                        capture.siblings[destination_start..][0..path_depth],",
        "unique_path_siblings.?[source_start..][0..path_depth],",
        "destination.* = capture;",
    )


def check_pcs_fri_capture(root: Path) -> None:
    path = root / "deps/stwo-zig/src/core/vcs_lifted/verifier.zig"
    check_capture_source(path.read_text())
