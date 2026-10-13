"""Mutation controls for the pinned lifted-multiproof decoder contract."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_capture import check_capture_source


SOURCE = (Path(__file__).resolve().parents[2] /
          "deps/stwo-zig/src/core/vcs_lifted/verifier.zig").read_text()


def change_once(before: str, after: str) -> str:
    if SOURCE.count(before) != 1:
        raise AssertionError(f"mutation anchor count for {before!r}: {SOURCE.count(before)}")
    return SOURCE.replace(before, after, 1)


class PcsFriCaptureTest(unittest.TestCase):
    def test_pinned_source(self) -> None:
        check_capture_source(SOURCE)

    def test_out_of_domain_alias_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
                "if (false) return MerkleVerificationError.InvalidQueryShape;"))

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

    def test_duplicate_query_consistency_guard_removed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "return MerkleVerificationError.DuplicateQueryMismatch;",
                "return MerkleVerificationError.RootMismatch;"))

    def test_paired_chunk_fails_to_advance_by_two(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once("chunk_len = 2;", "chunk_len = 1;"))

    def test_witness_cursor_fails_to_advance(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once("witness_idx += 1;", "witness_idx += 0;"))

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

    def test_parent_index_shift_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                ".idx = first.idx >> 1,", ".idx = first.idx >> 2,"))

    def test_original_order_path_copy_changed(self) -> None:
        with self.assertRaisesRegex(ValueError, "lifted Merkle"):
            check_capture_source(change_once(
                "const source_start = unique_index * path_depth;",
                "const source_start = original_index * path_depth;"))

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
