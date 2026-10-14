"""Mutation controls for the pinned lifted-multiproof decoder contract."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_capture import (
    GATE_TRACE_FILES,
    check_capture_source,
    check_selected_gate_trace_source,
)


SOURCE = (Path(__file__).resolve().parents[2] /
          "deps/stwo-zig/src/core/vcs_lifted/verifier.zig").read_text()
ROOT = Path(__file__).resolve().parents[2]
GATE_SOURCES = {name: (ROOT / name).read_text() for name in GATE_TRACE_FILES}


def change_once(before: str, after: str) -> str:
    if SOURCE.count(before) != 1:
        raise AssertionError(f"mutation anchor count for {before!r}: {SOURCE.count(before)}")
    return SOURCE.replace(before, after, 1)


class PcsFriCaptureTest(unittest.TestCase):
    def test_pinned_source(self) -> None:
        check_capture_source(SOURCE)

    def test_selected_gate_trace_source(self) -> None:
        check_selected_gate_trace_source(GATE_SOURCES)

    def test_selected_gate_query_budget_changed(self) -> None:
        name = "src/frontends/s31/runtime/mvp_runtime.zig"
        changed = dict(GATE_SOURCES)
        changed[name] = changed[name].replace(
            "FriConfigV2.init(26, 0, 1, 70, fri_fold_step), trace_log_size)",
            "FriConfigV2.init(26, 0, 1, 71, fri_fold_step), trace_log_size)", 1)
        with self.assertRaisesRegex(ValueError, "selected Gate"):
            check_selected_gate_trace_source(changed)

    def test_selected_gate_tree_projection_loses_raw_draws(self) -> None:
        name = "deps/stwo-zig/src/core/pcs/verifier.zig"
        changed = dict(GATE_SOURCES)
        changed[name] = changed[name].replace(
            "const raw_tree_positions = try pcs_utils.prepareTreeQueryPositions(\n                        allocator,\n                        query_capture.raw,",
            "const raw_tree_positions = try pcs_utils.prepareTreeQueryPositions(\n                        allocator,\n                        query_capture.unique,", 1)
        with self.assertRaisesRegex(ValueError, "selected Gate"):
            check_selected_gate_trace_source(changed)

    def test_selected_gate_capture_count_guard_removed(self) -> None:
        name = "src/frontends/s31/runtime/pcs_lifted_capture_admission.zig"
        changed = dict(GATE_SOURCES)
        changed[name] = changed[name].replace(
            "raw.len != pcs.fri_config.n_queries or", "false or", 1)
        with self.assertRaisesRegex(ValueError, "selected Gate"):
            check_selected_gate_trace_source(changed)

    def test_selected_gate_lifting_height_formula_changed(self) -> None:
        name = "deps/stwo-zig/src/core/pcs/config_v2.zig"
        changed = dict(GATE_SOURCES)
        changed[name] = changed[name].replace(
            "trace_log_size + config.log_blowup_factor",
            "trace_log_size + config.log_blowup_factor + 1", 1)
        with self.assertRaisesRegex(ValueError, "selected Gate"):
            check_selected_gate_trace_source(changed)

    def test_selected_gate_digest_width_changed(self) -> None:
        name = "deps/stwo-zig/src/core/crypto/blake2s_backend.zig"
        changed = dict(GATE_SOURCES)
        changed[name] = changed[name].replace(
            "pub const Blake2sHash = [32]u8;",
            "pub const Blake2sHash = [64]u8;", 1)
        with self.assertRaisesRegex(ValueError, "selected Gate"):
            check_selected_gate_trace_source(changed)

    def test_out_of_domain_alias_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
                "if (false) return MerkleVerificationError.InvalidQueryShape;"))

    def test_domain_shift_uses_declared_height(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "const domain_size: usize = @as(usize, 1) << @intCast(self.height);",
                "const domain_size: usize = @as(usize, 1) << @intCast(self.height - 1);"))

    def test_column_shape_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (column.len != query_positions.len) return MerkleVerificationError.InvalidQueryShape;",
                "if (false) return MerkleVerificationError.InvalidQueryShape;"))

    def test_unique_position_append_skipped(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "try unique_positions.append(allocator, position);",
                "// unique position lost"))

    def test_unique_path_allocation_uses_wrong_count(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "try allocator.alloc(H.Hash, unique_positions.items.len * path_depth)",
                "try allocator.alloc(H.Hash, query_positions.len * path_depth)"))

    def test_caller_capture_allocation_uses_wrong_count(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "query_positions.len * path_depth,",
                "unique_positions.items.len * path_depth,"))

    def test_sibling_pair_condition_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "(first.idx ^ 1) == prev_layer.items[p + 1].idx",
                "(first.idx ^ 2) == prev_layer.items[p + 1].idx"))

    def test_sorted_query_order_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "std.sort.heap(\n                usize,\n                query_order,",
                "// query order left unsorted\n            std.sort.heap(\n                usize,\n                omitted_order,"))

    def test_query_tie_breaker_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "(lhs_position == rhs_position and lhs < rhs);",
                "(lhs_position == rhs_position and lhs > rhs);"))

    def test_empty_tree_witness_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (decommitment.hash_witness.len != 0) return MerkleVerificationError.WitnessTooLong;",
                "if (false) return MerkleVerificationError.WitnessTooLong;"))

    def test_duplicate_query_consistency_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "return MerkleVerificationError.DuplicateQueryMismatch;",
                "return MerkleVerificationError.RootMismatch;"))

    def test_duplicate_row_comparison_uses_original_query_slot(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "} else if (!dedup.items[dedup.items.len - 1].eql(col[original_index])) {",
                "} else if (!dedup.items[dedup.items.len - 1].eql(col[0])) {"))

    def test_leaf_row_assembly_keeps_column_cursor(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "row[col_i] = col[col_pos[col_i]];",
                "row[col_i] = col[0];"))

    def test_leaf_row_cursor_advances(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "col_pos[col_i] += 1;",
                "col_pos[col_i] += 0;"))

    def test_paired_chunk_fails_to_advance_by_two(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once("chunk_len = 2;", "chunk_len = 1;"))

    def test_witness_cursor_fails_to_advance(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once("witness_idx += 1;", "witness_idx += 0;"))

    def test_odd_child_order_reversed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "left_hash = witness;\n                            right_hash = first.hash;",
                "left_hash = first.hash;\n                            right_hash = witness;"))

    def test_trailing_witness_accepted(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (witness_idx != decommitment.hash_witness.len)",
                "if (witness_idx > decommitment.hash_witness.len)"))

    def test_capture_ancestor_check_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "std.debug.assert(prev_layer.items[node_index].idx == ancestor);",
                "// ancestor correspondence unchecked"))

    def test_capture_sibling_index_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "paths[unique_index * path_depth + layer] = siblings[node_index];",
                "paths[unique_index * path_depth + layer] = siblings[0];"))

    def test_column_tie_order_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (lhs_size == rhs_size) return lhs < rhs;",
                "if (lhs_size == rhs_size) return lhs > rhs;"))

    def test_parent_index_shift_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                ".idx = first.idx >> 1,", ".idx = first.idx >> 2,"))

    def test_original_order_path_copy_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "const source_start = unique_index * path_depth;",
                "const source_start = original_index * path_depth;"))

    def test_unique_path_copy_skips_duplicate_group_change(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "unique_index += 1;", "unique_index += 2;"))

    def test_publication_loses_original_position_order(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                ".positions = try allocator.dupe(usize, query_positions),",
                ".positions = try allocator.dupe(usize, unique_positions.items),"))

    def test_publish_before_root_check_rejected(self) -> None:
        publication = "destination.* = capture;"
        root_check = "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))"
        self.assertEqual(SOURCE.count(publication), 1)
        self.assertEqual(SOURCE.count(root_check), 1)
        changed = SOURCE.replace(publication, "// deferred publication", 1)
        changed = changed.replace(root_check, publication + "\n            " + root_check, 1)
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(changed)


if __name__ == "__main__":
    unittest.main()
