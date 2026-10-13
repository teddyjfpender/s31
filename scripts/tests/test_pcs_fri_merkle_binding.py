"""Mutation controls for packed FRI Merkle leaf and path custody."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_merkle_binding import check_sources


CORE = Path(__file__).resolve().parents[2] / "deps/stwo-zig/src/core"


class FriMerkleBindingControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "fri": (CORE / "fri.zig").read_text(),
            "packed": (CORE / "fri/merkle_queries.zig").read_text(),
            "vcs": (CORE / "vcs_lifted/verifier.zig").read_text(),
        }

    @staticmethod
    def check(sources: dict[str, str]) -> None:
        check_sources(sources["fri"], sources["packed"], sources["vcs"])

    def test_pinned_source(self) -> None:
        self.check(self.sources)

    def test_critical_mutations_fail(self) -> None:
        mutations = (
            ("packed", "(position & (leaf_size - 1)) != offset", "false"),
            ("packed", "flattened_values[leaf_index * leaf_size + offset]", "flattened_values[leaf_index * leaf_size]"),
            ("packed", "columns[offset * qm31.SECURE_EXTENSION_DEGREE + coordinate][leaf_index] = coord;", "columns[coordinate * leaf_size + offset][leaf_index] = coord;"),
            ("fri", "sparse.subset_evals[subset_index],", "sparse.subset_evals[0],"),
            ("fri", "merkle_capture.path(merkle_index)[authenticated_subtree_height..]", "merkle_capture.path(merkle_index)[0..]"),
            ("fri", "const leaf_position = subset_start >> @intCast(leaf_log_size);", "const leaf_position = position >> @intCast(leaf_log_size);"),
            ("vcs", "if (!vcs_hash.eql(prev_layer.items[0].hash, self.root))", "if (false)"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                self.assertIn(old, self.sources[name])
                changed = dict(self.sources)
                changed[name] = changed[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    self.check(changed)


if __name__ == "__main__":
    unittest.main()
