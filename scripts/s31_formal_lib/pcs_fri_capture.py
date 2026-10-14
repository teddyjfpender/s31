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
        "if (self.column_log_sizes.len == 0) {",
        "if (query_positions.len != 0) return MerkleVerificationError.InvalidQueryShape;",
        "if (decommitment.hash_witness.len != 0) return MerkleVerificationError.WitnessTooLong;",
        "if (column.len != query_positions.len) return MerkleVerificationError.InvalidQueryShape;",
        "if (self.height < @bitSizeOf(usize))",
        "const domain_size: usize = @as(usize, 1) << @intCast(self.height);",
        "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
        "const lhs_position = context.positions[lhs];",
        "const rhs_position = context.positions[rhs];",
        "return lhs_position < rhs_position or",
        "(lhs_position == rhs_position and lhs < rhs);",
        "const query_order = try allocator.alloc(usize, query_positions.len);",
        "std.sort.heap(\n                usize,\n                query_order,",
        "for (query_order) |original_index| {",
        "if (unique_positions.items.len == 0 or",
        "try unique_positions.append(allocator, position);",
        "std.sort.heap(usize, col_indices, self.column_log_sizes, lessByLogSize);",
        "if (sorted_index == 0 or position != query_positions[query_order[sorted_index - 1]]) {",
        "} else if (!dedup.items[dedup.items.len - 1].eql(col[original_index])) {",
        "return MerkleVerificationError.DuplicateQueryMismatch;",
        "for (unique_positions.items) |pos| {",
        "row[col_i] = col[col_pos[col_i]];",
        "col_pos[col_i] += 1;",
        "hasher.updateLeaf(row);",
        "const path_depth: usize = @intCast(self.height);",
        "try allocator.alloc(H.Hash, unique_positions.items.len * path_depth)",
        "const first = prev_layer.items[p];",
        "if (p + 1 < prev_layer.items.len and (first.idx ^ 1) == prev_layer.items[p + 1].idx)",
        "siblings[p] = second.hash;",
        "chunk_len = 2;",
        "if (witness_idx >= decommitment.hash_witness.len)",
        "const witness = decommitment.hash_witness[witness_idx];",
        "witness_idx += 1;",
        "if ((first.idx & 1) == 0) {\n                            left_hash = first.hash;\n                            right_hash = witness;\n                        } else {\n                            left_hash = witness;\n                            right_hash = first.hash;\n                        }",
        "siblings[p] = witness;",
        ".idx = first.idx >> 1,",
        ".hash = H.hashChildren(.{ .left = left_hash, .right = right_hash }),",
        "p += chunk_len;",
        "const ancestor = position >> @intCast(layer);",
        "while (node_index < prev_layer.items.len and",
        "prev_layer.items[node_index].idx < ancestor)",
        "std.debug.assert(prev_layer.items[node_index].idx == ancestor);",
        "paths[unique_index * path_depth + layer] = siblings[node_index];",
        "prev_layer.clearRetainingCapacity();",
        "try prev_layer.appendSlice(allocator, curr.items);",
        "if (witness_idx != decommitment.hash_witness.len)",
        "if (prev_layer.items.len != 1) return MerkleVerificationError.RootMismatch;",
        "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))",
        ".positions = try allocator.dupe(usize, query_positions),",
        "query_positions.len * path_depth,",
        "var unique_index: usize = 0;",
        "if (sorted_index != 0 and\n                        query_positions[original_index] !=\n                            query_positions[query_order[sorted_index - 1]])",
        "unique_index += 1;",
        "const source_start = unique_index * path_depth;",
        "const destination_start = original_index * path_depth;",
        "@memcpy(\n                        capture.siblings[destination_start..][0..path_depth],",
        "unique_path_siblings.?[source_start..][0..path_depth],",
        "destination.* = capture;",
    )
    column_order = region(source, "fn lessByLogSize(", "fn maxLogSize(")
    ordered_once(
        column_order, "lifted Merkle column order",
        "const lhs_size = log_sizes[lhs];",
        "const rhs_size = log_sizes[rhs];",
        "if (lhs_size == rhs_size) return lhs < rhs;",
        "return lhs_size < rhs_size;",
    )


def check_pcs_fri_capture(root: Path) -> None:
    path = root / "deps/stwo-zig/src/core/vcs_lifted/verifier.zig"
    check_capture_source(path.read_text())
    check_selected_gate_trace_source({
        name: (root / name).read_text() for name in GATE_TRACE_FILES
    })


# These are the selected raw Gate path's query-count and height provenance,
# not an assertion about arbitrary direct callers or FRI-layer Merkle trees.
GATE_TRACE_FILES = (
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/runtime/native_verifier.zig",
    "src/frontends/s31/runtime/pcs_lifted_capture_admission.zig",
    "deps/stwo-zig/src/core/pcs/config_v2.zig",
    "deps/stwo-zig/src/core/pcs/verifier.zig",
    "deps/stwo-zig/src/core/pcs/utils.zig",
    "deps/stwo-zig/src/core/fri.zig",
    "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig",
    "deps/stwo-zig/src/core/crypto/blake2s_backend.zig",
)


def check_selected_gate_trace_source(sources: dict[str, str]) -> None:
    mvp, native, admission, config, pcs, utils, fri, merkle, blake = (
        sources[name] for name in GATE_TRACE_FILES)
    profile = region(mvp, "fn showcasePcsConfig(", "fn recursivePcsConfig(")
    ordered_once(profile, "selected Gate trace profile",
                 "PcsConfigV2.fromFriAndTraceSize(",
                 "FriConfigV2.init(26, 0, 1, 70, fri_fold_step), trace_log_size)")
    if mvp.count("native.verifyRawGate(allocator, &layout, &bundle, try showcasePcsConfig(key.trace_log_size)") != 1:
        raise ValueError("selected Gate verifier call changed")
    ordered_once(native, "selected Gate Merkle digest type",
                 "const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;",
                 "if (H != MC.MerkleHasher or H != RawMC.MerkleHasher)")
    if merkle.count("pub const Hash = blake2_hash.Blake2sHash;") != 1 or \
            blake.count("pub const Blake2sHash = [32]u8;") != 1:
        raise ValueError("selected Gate 32-byte digest type changed")
    ordered_once(config, "selected Gate PCS height and count",
                 ".n_queries = n_queries,",
                 "return fromFriAndLiftingSize(config, trace_log_size + config.log_blowup_factor);",
                 ".trace_lifting_log_size = lifting_log_size,",
                 "return self.trace_lifting_log_size;",
                 "return height;")
    ordered_once(fri, "selected Gate raw query count",
                 "pub fn sampleQueryPositionsWithRaw(",
                 "self.config.n_queries,",
                 ".raw = raw,")
    pcs_capture = region(pcs,
                         "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(",
                         "const fri_answers = try quotients.friAnswers(")
    ordered_once(pcs_capture, "selected Gate raw Merkle capture",
                 "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(",
                 "const raw_tree_positions = try pcs_utils.prepareTreeQueryPositions(\n                        allocator,\n                        query_capture.raw,",
                 "tree.verifyWithPathCapture(",
                 "raw_tree_positions,",
                 "raw_columns.items,")
    ordered_once(utils, "selected Gate projected query length",
                 "pub fn prepareTreeQueryPositions(",
                 "const out = try allocator.alloc(usize, query_positions.len);")
    ordered_once(admission, "selected Gate capture admission",
                 "raw.len != pcs.fri_config.n_queries or",
                 "const height = pcs.treeHeight(tree_index, logs) catch",
                 "path.positions.len != raw.len or",
                 "path.siblings.len != std.math.mul(usize, raw.len, @as(usize, height)) catch")
