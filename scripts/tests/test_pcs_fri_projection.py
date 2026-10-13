"""Independent circle-index regression checks for pinned lifted PCS queries."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_projection import (
    check_pcs_fri_projection, require, tree_query_position,
)

ROOT = Path(__file__).resolve().parents[2]
QUERY_SOURCE = ROOT / "deps/stwo-zig/src/core/pcs/utils.zig"
SMALLER = "out[i] = (pos >> @intCast(max_log_size - tree_log_size + 1) << 1) + (pos & 1);"
LARGER = "out[i] = (pos >> 1 << @intCast(tree_log_size - max_log_size + 1)) + (pos & 1);"


class PcsFriProjectionTest(unittest.TestCase):
    def test_pinned_sources_and_circle_geometry(self) -> None:
        self.assertEqual(check_pcs_fri_projection(ROOT), 20460)

    def test_pair_bit_and_shift_mutants_refused(self) -> None:
        source = QUERY_SOURCE.read_text()
        self.assertIn(SMALLER, source)
        self.assertIn(LARGER, source)
        for anchor in (SMALLER, LARGER):
            for mutant in (anchor.replace(" + (pos & 1)", ""),
                           anchor.replace(" + 1", " + 2")):
                with self.subTest(anchor=anchor, mutant=mutant):
                    with self.assertRaisesRegex(ValueError, "pinned source mapping changed"):
                        require(source.replace(anchor, mutant, 1), anchor, "query projection")

    def test_opposite_pair_bits_and_both_tree_directions(self) -> None:
        for big, small in ((5, 3), (10, 2), (8, 8)):
            for even in range(0, 1 << big, 2):
                self.assertEqual(tree_query_position(even + 1, big, small),
                                 tree_query_position(even, big, small) + 1)
        for source, tree in ((3, 5), (2, 10)):
            for raw in range(1 << source):
                expanded = tree_query_position(raw, source, tree)
                self.assertEqual(tree_query_position(expanded, tree, source), raw)


if __name__ == "__main__":
    unittest.main()
