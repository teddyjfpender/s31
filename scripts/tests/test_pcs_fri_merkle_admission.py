"""Hostile source mutations for the post-success FRI Merkle barrier."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_merkle_admission import check_sources


ROOT = Path(__file__).resolve().parents[2]


class FriMerkleAdmissionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.verifier = (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text()
        cls.admission = (ROOT / "src/frontends/s31/runtime/fri_merkle_admission.zig").read_text()
        cls.qm31 = (ROOT / "deps/stwo-zig/src/core/fields/qm31.zig").read_text()
        cls.hasher = (ROOT / "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig").read_text()
        cls.fri = (ROOT / "deps/stwo-zig/src/core/fri.zig").read_text()

    def test_pinned_source(self) -> None:
        check_sources(self.verifier, self.admission, self.qm31, self.hasher,
                      self.fri)

    def test_mutations_fail(self) -> None:
        mutations = (
            ("verifier", "try fri_merkle_admission.validate(allocator, capture.queries.raw, capture.fri);", "// FRI Merkle gate omitted"),
            ("admission", "if (layer.positions[slot] != position or", "if (false or"),
            ("admission", "row[offset * 4 + coordinate] = coords[coordinate];", "row[coordinate * 4 + offset] = coords[coordinate];"),
            ("admission", "hasher.updateLeaf(row[0 .. leaf_width * 4]);", "hasher.updateLeaf(row[0..0]);"),
            ("admission", "nodes[i] = H.hashChildren(.{ .left = nodes[2 * i], .right = nodes[2 * i + 1] });", "nodes[i] = nodes[2 * i];"),
            ("admission", "for (layer.queryPath(slot)) |sibling| {", "for (&.{}) |sibling| {"),
            ("admission", "!std.mem.eql(u8, hash[0..], layer.commitment[0..])", "false"),
            ("admission", "positions[slot] = position >> @intCast(step);", "positions[slot] = position;"),
            ("qm31", "return .{ self.c0.a, self.c0.b, self.c1.a, self.c1.b };", "return .{ self.c0.b, self.c0.a, self.c1.a, self.c1.b };"),
            ("hasher", "self.inner.update(std.mem.sliceAsBytes(column_values));", "self.inner.update(&.{});"),
            ("fri", "                    self.proof.commitment,", "                    [_]u8{0} ** 32,"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                source = getattr(self, name)
                self.assertIn(old, source)
                changed = source.replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(
                        changed if name == "verifier" else self.verifier,
                        changed if name == "admission" else self.admission,
                        changed if name == "qm31" else self.qm31,
                        changed if name == "hasher" else self.hasher,
                        changed if name == "fri" else self.fri,
                    )


if __name__ == "__main__":
    unittest.main()
