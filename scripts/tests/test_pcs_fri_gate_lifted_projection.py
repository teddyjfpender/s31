"""Controls for the sealed gate tree/column projection diagnostic."""

import copy
import unittest
from pathlib import Path

from scripts.release.pcs_fri_gate_lifted_projection import (
    check_group_projection, gate_tree_groups,
)
from scripts.s31_formal_lib.pcs_fri_projection import check_projection_sources, require

ROOT = Path(__file__).resolve().parents[2]
VCS = ROOT / "deps/stwo-zig/src/core/vcs_lifted/verifier.zig"
PCS = ROOT / "deps/stwo-zig/src/core/pcs/verifier.zig"


def geometry():
    return {
        "gate_final_domain": {"fri_input_domain_log": 5,
                              "composition_split_depth": 1,
                              "committed_composition_column_log_size": 4},
        "fri": {"log_blowup_factor": 1},
        "components": [{"name": "small", "trace_log_size": 2},
                       {"name": "large", "trace_log_size": 4}],
        "preprocessed_columns": [{"id": "small_fixed", "log_size": 2},
                                 {"id": "large_fixed", "log_size": 4}],
    }


def roster():
    return {
        "components": [
            {"name": "small", "trace_log_size": 2,
             "base_trace_columns": 2, "interaction_trace_columns": 3},
            {"name": "large", "trace_log_size": 4,
             "base_trace_columns": 1, "interaction_trace_columns": 2},
        ],
        "preprocessed_columns": [
            {"id": "small_fixed", "log_size": 2},
            {"id": "large_fixed", "log_size": 4},
        ],
    }


class GateLiftedProjectionTests(unittest.TestCase):
    def test_every_column_group_and_two_stage_index(self):
        trees = gate_tree_groups(roster(), geometry())
        self.assertEqual([t["column_count"] for t in trees], [2, 3, 5, 8])
        self.assertEqual([t["natural_column_height_log"] for t in trees], [5, 5, 5, 5])
        self.assertEqual(trees[1]["groups"][0]["column_start"], 0)
        self.assertEqual(trees[1]["groups"][0]["count"], 2)
        self.assertEqual(trees[1]["groups"][0]["extended_column_log"], 3)
        self.assertEqual(trees[1]["groups"][1]["column_start"], 2)
        self.assertEqual(trees[1]["leaf_hash_column_order"], [0, 1, 2])
        check_group_projection(trees, list(range(32)))
        self.assertEqual(trees[3]["groups"][0]["extended_column_log"], 5)

    def test_explicit_height_above_natural_height(self):
        small_roster = roster()
        small_geometry = geometry()
        small_roster["components"][1]["trace_log_size"] = 2
        small_geometry["components"][1]["trace_log_size"] = 2
        small_roster["preprocessed_columns"][1]["log_size"] = 2
        small_geometry["preprocessed_columns"][1]["log_size"] = 2
        trees = gate_tree_groups(small_roster, small_geometry)
        self.assertEqual([t["natural_column_height_log"] for t in trees], [3, 3, 3, 5])
        check_group_projection(trees, list(range(32)))

    def test_leaf_hash_tie_order_preserves_original_column_index(self):
        tied_roster = roster()
        tied_geometry = geometry()
        tied_roster["preprocessed_columns"].append({"id": "late_small", "log_size": 2})
        tied_geometry["preprocessed_columns"].append({"id": "late_small", "log_size": 2})
        trees = gate_tree_groups(tied_roster, tied_geometry)
        self.assertEqual(trees[0]["leaf_hash_column_order"], [0, 2, 1])

    def test_roster_and_projection_mutants_reject(self):
        changed = roster()
        changed["components"][0]["base_trace_columns"] = 0
        with self.assertRaisesRegex(ValueError, "column width"):
            gate_tree_groups(changed, geometry())
        changed = roster()
        changed["preprocessed_columns"][0]["log_size"] = 4
        with self.assertRaisesRegex(ValueError, "roster differs"):
            gate_tree_groups(changed, geometry())
        trees = gate_tree_groups(roster(), geometry())
        with self.assertRaisesRegex(ValueError, "outside lifted domain"):
            check_group_projection(trees, [32])
        changed_trees = copy.deepcopy(trees)
        changed_trees[0]["natural_column_height_log"] = 2
        with self.assertRaisesRegex(ValueError, "projection mismatch"):
            check_group_projection(changed_trees, [7])

    @unittest.skipUnless(VCS.is_file() and PCS.is_file(), "pinned engine not checked out")
    def test_capture_branch_source_mutants_reject(self):
        check_projection_sources(ROOT)
        for path, anchor, mutant in (
                (VCS, "if (position >= domain_size) return MerkleVerificationError.InvalidQueryShape;",
                 "if (position > domain_size) return MerkleVerificationError.InvalidQueryShape;"),
                (VCS, "row[col_i] = col[col_pos[col_i]];", "row[col_i] = M31.zero();"),
                (VCS, ".positions = try allocator.dupe(usize, query_positions),",
                 ".positions = try allocator.dupe(usize, unique_positions.items),"),
                (PCS, "tree.verifyWithPathCapture(", "tree.verify("),
                (PCS, "return if (height == 0) null else height;",
                 "return if (height == 0) null else height - 1;"),
        ):
            with self.subTest(path=path.name, anchor=anchor):
                text = path.read_text()
                self.assertIn(anchor, text)
                with self.assertRaisesRegex(ValueError, "pinned source mapping changed"):
                    require(text.replace(anchor, mutant, 1), anchor, "captured path")


if __name__ == "__main__":
    unittest.main()
