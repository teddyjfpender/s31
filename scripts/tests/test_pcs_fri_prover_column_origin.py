"""Adversarial controls for the pinned lifted prover-to-row source guard."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_prover_origin import (
    SOURCE_PATHS, check_prover_origin_texts,
)

ROOT = Path(__file__).resolve().parents[2]


class ProverColumnOriginTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {key: (ROOT / path).read_text()
                       for key, path in SOURCE_PATHS.items()}

    def test_reviewed_source_path_is_pinned(self) -> None:
        check_prover_origin_texts(self.sources)

    def test_mutated_column_origin_stages_reject(self) -> None:
        changes = (
            ("columns", "lhs.original_index < rhs.original_index",
             "lhs.original_index > rhs.original_index"),
            ("prover", "const leaves = try liftLeaves(layer_alloc, column_leaves, height - max_col_log_size);",
             "const leaves = column_leaves;"),
            ("prover", "self.* = rebuilt;", "self.* = undefined;"),
            ("prover", "@memset(leaves, leaf_hash);", "@memset(leaves, H.Hash{0} ** 32);"),
            ("leaves", "const source_index = ((position >> shift_amt) << 1) + (position & 1);",
             "const source_index = position;"),
            ("leaves", "words[lane * ctx.sorted_columns.len + column_index] = column.values[source_index];",
             "words[lane * ctx.sorted_columns.len + column_index] = column.values[0];"),
            ("expand", "ctx.dst[at] = if ((at & 1) == 0) even else odd;",
             "ctx.dst[at] = even;"),
            ("backend", "const index = (position >> shift) << 1;",
             "const index = position >> shift;"),
            ("layers", ".right = prev_layer[2 * i + 1],",
             ".right = prev_layer[2 * i],"),
            ("decommit", "value.* = column[column_index];",
             "value.* = column[0];"),
            ("revision", "tree.commitment.liftTo(allocator, height) catch |err| switch (err) {",
             "tree.commitment.liftTo(allocator, height - 1) catch |err| switch (err) {"),
            ("cpu_backend", "return lifted_merkle.MerkleProverLifted(H);",
             "return UnreviewedMerkleTree(H);"),
            ("s31_integration", "prover.pcs.tiled_commit.commit(CpuBackend, Hasher, scheme, allocator, columns, .owned, .{}, channel)",
             "prover.pcs.tiled_commit.commit(CpuBackend, Hasher, scheme, allocator, columns[0..1], .owned, .{}, channel)"),
            ("tiled", "const leaves = try LeafOps.buildBatched(allocator, allocator, refs, 1024);",
             "const leaves = try LeafOps.buildBatched(allocator, allocator, refs[0..1], 1024);"),
            ("tree_builders", "const root = retained.root();",
             "const root = tree.root();"),
            ("verifier", "row[col_i] = col[col_pos[col_i]];",
             "row[col_i] = col[0];"),
        )
        for key, original, mutated in changes:
            with self.subTest(stage=key, mutation=original):
                self.assertIn(original, self.sources[key])
                source = dict(self.sources)
                source[key] = source[key].replace(original, mutated, 1)
                with self.assertRaises(ValueError):
                    check_prover_origin_texts(source)


if __name__ == "__main__":
    unittest.main()
