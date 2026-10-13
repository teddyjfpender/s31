"""Pin the packed FRI leaf geometry used by the conditional Lean binding join.

Selected source structure is checked, not Zig semantics or hash security.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(fri: str, merkle_queries: str, vcs: str) -> None:
    packed = region(merkle_queries, "pub fn build(", "pub fn findSubsetIndex(")
    ordered_once(
        packed, "FRI packed Merkle rows",
        "const leaf_size: usize = @as(usize, 1) << @intCast(leaf_log_size);",
        "const merkle_position = decommitment_positions[first_index] >> @intCast(leaf_log_size);",
        "(position & (leaf_size - 1)) != offset",
        "if (leaf_index > 0 and positions[leaf_index - 1] >= merkle_position)",
        "@memcpy(flattened_values[value_index..][0..subset.len], subset);",
        "const column_count = qm31.SECURE_EXTENSION_DEGREE * leaf_size;",
        "const coords = flattened_values[leaf_index * leaf_size + offset].toM31Array();",
        "columns[offset * qm31.SECURE_EXTENSION_DEGREE + coordinate][leaf_index] = coord;",
        ".positions = positions,",
        ".columns = columns,",
    )

    capture = region(fri, "fn buildFriLayerQueryCapture(", "pub fn FriLayerProofAux(")
    ordered_once(
        capture, "FRI subset and Merkle path capture",
        "leaf_log_size > fold_step",
        "const authenticated_subtree_height = fold_step - leaf_log_size;",
        "merkle_capture.path_depth - authenticated_subtree_height;",
        "decommitment_positions.len != subset_count * fold_width",
        "const subset_start = (position >> @intCast(fold_step)) << @intCast(fold_step);",
        "const subset_index = findSubsetIndex(",
        "sparse.subset_evals[subset_index],",
        "const leaf_position = subset_start >> @intCast(leaf_log_size);",
        "const merkle_index = findPosition(",
        "const source_path = merkle_capture.path(merkle_index)[authenticated_subtree_height..];",
        "capture.siblings[raw_index * path_depth ..][0..path_depth],",
        "const expected_path_depth = evaluation_log_size - fold_step;",
        "if (capture.path_depth != expected_path_depth)",
    )

    verifier = region(vcs, "fn verifyImpl(", "fn lessByLogSize(")
    ordered_once(
        verifier, "lifted Merkle authentication before FRI publication",
        "hasher.updateLeaf(row);",
        "if (witness_idx >= decommitment.hash_witness.len)",
        ".hash = H.hashChildren(.{ .left = left_hash, .right = right_hash }),",
        "if (witness_idx != decommitment.hash_witness.len)",
        "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))",
        "destination.* = capture;",
    )


def check_pcs_fri_merkle_binding(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources(
        (core / "fri.zig").read_text(),
        (core / "fri/merkle_queries.zig").read_text(),
        (core / "vcs_lifted/verifier.zig").read_text(),
    )
