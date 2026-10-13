"""Hostile source controls for the lifted PCS opening admission."""
import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_lifted_capture import check_sources

ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"
S31 = ROOT / "src/frontends/s31/runtime"


class LiftedCaptureSourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "verifier": (S31 / "native_verifier.zig").read_text(),
            "admission": (S31 / "pcs_lifted_capture_admission.zig").read_text(),
            "pcs": (CORE / "pcs/verifier.zig").read_text(),
            "lifted": (CORE / "vcs_lifted/verifier.zig").read_text(),
            "config": (CORE / "pcs/config_v2.zig").read_text(),
            "hasher": (CORE / "vcs_lifted/blake2_merkle.zig").read_text(),
            "collision": (ROOT / "formal/s31/tests/lib/pcs_merkle_collision_reduction.zig").read_text(),
        }

    def check(self, sources: dict[str, str]) -> None:
        check_sources(*(sources[name] for name in
                        ("verifier", "admission", "pcs", "lifted", "config", "hasher", "collision")))

    def test_pinned_source(self) -> None:
        self.check(self.sources)

    def test_mutations_fail(self) -> None:
        mutations = (
            ("verifier", "try pcs_lifted_capture_admission.validate(allocator, pcs, roots, &capture);",
             "// lifted PCS admission skipped"),
            ("admission", "if (!std.mem.eql(u8, &root, &capture.commitments[tree_index]))",
             "if (false)"),
            ("admission", "if (path.positions[slot] != tree_position)", "if (false)"),
            ("admission", "const entry = try seen.getOrPut(column_position);",
             "const entry = try seen.getOrPut(position);"),
            ("admission", "if (!entry.value_ptr.*.eql(value)) return error.InvalidPcsLiftedCapture;",
             "if (false) return error.InvalidPcsLiftedCapture;"),
            ("admission", "hasher.updateLeaf(row);", "hasher.updateLeaf(&.{});"),
            ("admission", "for (path.path(slot)) |sibling| {", "for (&.{}) |sibling| {"),
            ("admission", "!std.mem.eql(u8, &hash, &root)", "false"),
            ("admission", "return ((position >> @intCast(source_log - target_log + 1)) << 1) | (position & 1);",
             "return position;"),
            ("pcs", "if (!std.meta.eql(tree.root, commitment))", "if (false)"),
            ("pcs", ".commitments = commitments,", ".commitments = &.{},"),
            ("lifted", "row[col_i] = col[col_pos[col_i]];", "row[col_i] = M31.zero();"),
            ("config", "const height = self.liftingLogSize(tree_index);", "const height = 0;"),
            ("hasher", "self.inner.update(std.mem.sliceAsBytes(column_values));",
             "self.inner.update(&.{});"),
            ("collision", "if (!childrenEq(first_children, second_children) and",
             "if (childrenEq(first_children, second_children) and"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                self.assertIn(old, self.sources[name])
                modified = dict(self.sources)
                modified[name] = modified[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    self.check(modified)


if __name__ == "__main__":
    unittest.main()
