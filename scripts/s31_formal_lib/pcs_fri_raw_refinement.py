"""Source anchors for the raw-slot FRI capture refinement experiment.

These selected stages connect native success to a captured raw-slot trace.
They do not prove the Zig-success-to-`rawAccepts` extraction lemma, Merkle
binding, or the independent native audit's correctness.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(fri: str, native_audit: str) -> None:
    verify = region(fri, "fn decommitImpl(", "fn decommitLastLayer(")
    ordered_once(
        verify, "FRI raw-slot publication after complete verification",
        "if (!std.mem.eql(usize, positions, sampled))",
        "self.first_layer.verifyImpl(",
        "first_layer_sparse_eval.foldCircleSubsets(",
        "for (self.inner_layers, 0..) |layer, layer_index|",
        "layer.verifyAndFoldImpl(",
        "layer_query_evals = folded.evals;",
        "try self.decommitLastLayer(allocator, layer_queries, layer_query_evals);",
        "destination.* = .{ .layers = capture_layers.? };",
    )
    builder = region(fri, "fn buildFriLayerQueryCapture(", "pub fn FriLayerProofAux(")
    ordered_once(
        builder, "FRI raw-slot capture projection",
        "const captured_positions = try allocator.dupe(usize, raw_query_positions);",
        "for (raw_query_positions, 0..) |position, raw_index|",
        "const subset_start = (position >> @intCast(fold_step)) << @intCast(fold_step);",
        "const subset_index = findSubsetIndex(",
        "sparse.subset_evals[subset_index],",
        "const merkle_index = findPosition(",
        "merkle_capture.path(merkle_index)[authenticated_subtree_height..];",
        "if (capture.path_depth != expected_path_depth) return error.ShapeMismatch;",
    )
    audit = region(native_audit, "fn audit(", "fn runSchedule(")
    ordered_once(
        audit, "independent raw-slot transition audit",
        "capture.layers.len != 1 + verifier.inner_layers.len",
        "layer.fold_step != step or",
        "if (!left.eql(right)) return error.InconsistentGroup;",
        "if (layer.positions[slot] != position) return error.BadRawPosition;",
        "if (!subset[position % width].eql(current)) return error.BadCurrentValue;",
        "try referenceCircle(",
        "try referenceInner(",
        "if (!current.eql(expected)) return error.BadTerminalValue;",
    )


def check_pcs_fri_raw_refinement(root: Path) -> None:
    check_sources(
        (root / "deps/stwo-zig/src/core/fri.zig").read_text(),
        (root / "formal/s31/tests/pcs_fri_raw_refinement_native.zig").read_text(),
    )
