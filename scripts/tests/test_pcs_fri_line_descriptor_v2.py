"""Exact candidate line-tree descriptor and statement-binding controls."""

from dataclasses import replace
import unittest

from scripts.release.pcs_fri_framed_bcs_v2 import StatementBinding
from scripts.release.pcs_fri_line_descriptor_v2 import (
    LineTreeDescriptorV2, LineTreeManifestV2, Track,
    line_hash_profile_digest,
)


def fixture() -> LineTreeManifestV2:
    key = bytes(range(32))
    profile = line_hash_profile_digest()
    original = LineTreeDescriptorV2(
        key, profile, Track.ORIGINAL, 17, 17, 17,
        (bytes([0x11]) * 32, bytes([0x12]) * 32),
    )
    own = LineTreeDescriptorV2(
        key, profile, Track.OWN_QUOTIENT, 17, 17, 18,
        (bytes([0x21]) * 32,),
    )
    return LineTreeManifestV2(key, (17, 16), (original, own))


class LineDescriptorTests(unittest.TestCase):
    def test_exact_tree_and_manifest_bytes_bind_statement(self) -> None:
        manifest = fixture()
        original, own = manifest.trees
        original_bytes = original.encode()
        self.assertEqual(len(original_bytes), 157)
        self.assertEqual(original_bytes[:25],
                         b"S31LTDV2\x01" + (17).to_bytes(4, "little") * 2 +
                         (17).to_bytes(8, "little"))
        self.assertEqual(original_bytes[25:57], manifest.key_digest)
        self.assertEqual(original_bytes[57:89], line_hash_profile_digest())
        self.assertEqual(original_bytes[89:93], (2).to_bytes(4, "little"))
        self.assertEqual(original_bytes[93:], bytes([0x11]) * 32 + bytes([0x12]) * 32)
        self.assertEqual(len(own.encode()), 125)
        encoded = manifest.encode()
        self.assertEqual(len(encoded), 378)
        self.assertEqual(encoded[:8], b"S31LTMV2")
        self.assertEqual(encoded[88:92], (157).to_bytes(4, "little"))
        self.assertEqual(encoded[92:249], original_bytes)
        self.assertEqual(encoded[249:253], (125).to_bytes(4, "little"))
        self.assertEqual(encoded[253:], own.encode())
        self.assertEqual(line_hash_profile_digest().hex(),
                         "cfe6fd8b3c4b3996d878f9234c61945263c6403fd16fb1e9db6d63af55718fac")
        self.assertEqual(manifest.digest().hex(),
                         "ee5d374d300ab5aaf8f01794f9c9c67f4f6f3ffd20e0433c8ae74496bfecab2c")

        zero = bytes(32)
        statement = StatementBinding(manifest.key_digest, zero, zero,
                                     (zero, zero, zero, zero), manifest.digest())
        self.assertTrue(manifest.matches_statement(statement))
        self.assertFalse(manifest.matches_statement(replace(statement,
            line_profile_digest=zero)))
        self.assertFalse(manifest.matches_statement(replace(statement, key_digest=zero)))

    def test_ordinal_track_roster_and_key_changes_reject(self) -> None:
        manifest = fixture()
        original, own = manifest.trees
        for bad in (
            replace(original, root_event=18),
            replace(original, track=Track.OWN_QUOTIENT),
            replace(original, fold_height=16),
            replace(original, key_digest=bytes(32)),
            replace(original, profile_digest=bytes(32)),
            replace(original, tree_log_size=64),
            replace(original, column_descriptors=()),
            replace(original, column_descriptors=(b"short",)),
            replace(original, column_descriptors=(bytes([0x11]) * 32,) * 2),
            replace(original, column_descriptors=tuple(
                i.to_bytes(32, "little") for i in range(257))),
        ):
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    replace(manifest, trees=(bad, own)).digest()
        for bad in (
            replace(manifest, fold_heights=(16, 17)),
            replace(manifest, fold_heights=(17, 17)),
            replace(manifest, fold_heights=(17,)),
            replace(manifest, trees=(own, original)),
        ):
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    bad.digest()

    def test_distinct_roster_and_terminal_height_change_digest(self) -> None:
        manifest = fixture()
        original, own = manifest.trees
        changed_row = replace(original,
                              column_descriptors=(bytes([0x11]) * 32,
                                                  bytes([0x13]) * 32))
        self.assertNotEqual(manifest.digest(),
                            replace(manifest, trees=(changed_row, own)).digest())
        self.assertNotEqual(manifest.digest(),
                            replace(manifest, fold_heights=(17, 15)).digest())
        self.assertNotEqual(manifest.digest(),
                            replace(manifest, trees=(replace(original, tree_log_size=16), own)).digest())

    def test_second_nonterminal_fold_has_derived_root_events(self) -> None:
        first = fixture()
        profile = line_hash_profile_digest()
        column = (bytes([0x31]) * 32,)
        next_original = LineTreeDescriptorV2(
            first.key_digest, profile, Track.ORIGINAL, 16, 16, 20, column)
        next_own = LineTreeDescriptorV2(
            first.key_digest, profile, Track.OWN_QUOTIENT, 16, 16, 21, column)
        manifest = replace(first, fold_heights=(17, 16, 15),
                           trees=first.trees + (next_original, next_own))
        self.assertEqual(len(manifest.digest()), 32)
        with self.assertRaises(ValueError):
            replace(manifest, trees=first.trees +
                    (replace(next_original, root_event=19), next_own)).digest()

    def test_manifest_byte_cap_rejects_before_materializing_payload(self) -> None:
        key = bytes(32)
        profile = line_hash_profile_digest()
        columns = tuple(i.to_bytes(32, "little") for i in range(256))
        heights = tuple(range(64, 0, -1))
        trees = tuple(
            LineTreeDescriptorV2(key, profile, track, height, min(height, 63),
                                 17 + 3 * i + (0 if track is Track.ORIGINAL else 1),
                                 columns)
            for i, height in enumerate(heights[:-1])
            for track in (Track.ORIGINAL, Track.OWN_QUOTIENT)
        )
        with self.assertRaisesRegex(ValueError, "byte cap"):
            LineTreeManifestV2(key, heights, trees).encode()


if __name__ == "__main__":
    unittest.main()
