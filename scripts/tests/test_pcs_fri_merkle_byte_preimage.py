import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_merkle_byte_preimage import (
    FILES, check, check_sources, source_texts,
)


ROOT = Path(__file__).resolve().parents[2]


class MerkleBytePreimageTest(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check(ROOT)

    def test_hostile_source_mutations(self) -> None:
        originals = source_texts(ROOT)
        mutations = (
            (FILES[0], "Blake2sPlainMerkleHasher", "Blake2sMerkleHasher"),
            (FILES[1], "children.left, children.right", "children.right, children.left"),
            (FILES[1], "std.mem.sliceAsBytes(column_values)", "std.mem.sliceAsBytes(column_values[1..])"),
            (FILES[2],
             "pub fn concatAndHashWithMode(mode: BackendMode, v1: Blake2sHash, v2: Blake2sHash) Blake2sHash {\n"
             "            var payload: [64]u8 = undefined;\n"
             "            @memcpy(payload[0..32], v1[0..]);",
             "pub fn concatAndHashWithMode(mode: BackendMode, v1: Blake2sHash, v2: Blake2sHash) Blake2sHash {\n"
             "            var payload: [64]u8 = undefined;\n"
             "            @memcpy(payload[0..32], v2[0..]);"),
            (FILES[3], "@intCast((x >> 24) & 0xff)", "@intCast((x >> 16) & 0xff)"),
            (FILES[4], "Blake2sPlainMerkleHasher", "Blake2sMerkleHasher"),
            (FILES[5], "hasher.updateLeaf(row);", "hasher.updateLeaf(row[1..]);"),
        )
        for name, before, after in mutations:
            with self.subTest(name=name, before=before):
                self.assertIn(before, originals[name])
                modified = dict(originals)
                modified[name] = modified[name].replace(before, after, 1)
                with self.assertRaises(ValueError):
                    check_sources(modified)


if __name__ == "__main__":
    unittest.main()
