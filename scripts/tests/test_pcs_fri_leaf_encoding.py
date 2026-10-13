"""Finite independent leaf/root replay and production-source mutation controls."""
from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_leaf_encoding import (
    ORACLE, P, SOURCE_ANCHORS, check_oracle, check_pcs_fri_leaf_encoding,
    check_sources, digest, encode_row, path, replay, row, source_index,
    source_texts, tree,
)

ROOT = Path(__file__).resolve().parents[2]


class PcsFriLeafEncodingTest(unittest.TestCase):
    def test_three_rust_roots_and_twelve_full_openings(self) -> None:
        self.assertEqual(check_pcs_fri_leaf_encoding(ROOT), 12)
        self.assertEqual(check_oracle(ROOT), 12)

    def test_stable_log_size_sort_and_conjugate_projection(self) -> None:
        # Input order is 3,2,3; hash order is 2,3,3 (ties retain input order).
        self.assertEqual(row(7, 3), (2022, 1050, 3050))
        self.assertEqual(row(15, 4), (2022, 1050, 3050))
        self.assertEqual(source_index(15, 4, 2), 3)
        self.assertEqual(source_index(14, 4, 2), 2)
        with self.assertRaisesRegex(ValueError, "outside domain"):
            source_index(16, 4, 2)

    def test_canonical_little_endian_row_and_plain_domain(self) -> None:
        encoded = encode_row((2022, 1050, 3050))
        self.assertEqual(encoded.hex(), "e60700001a040000ea0b0000")
        self.assertNotEqual(digest(encoded), digest(b"leaf" + bytes(60) + encoded))
        self.assertNotEqual(digest(encoded), digest(b"".join(
            value.to_bytes(4, "big") for value in (2022, 1050, 3050))))
        for bad in (-1, P, 1 << 31):
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, "noncanonical"):
                encode_row((bad,))

    def test_full_path_replay_mutations_change_root(self) -> None:
        height, root_hex, positions, _ = ORACLE[1]
        layers = tree(height)
        root_digest = bytes.fromhex(root_hex)
        position = positions[0]
        values = row(position, height)
        siblings = path(layers, position)
        self.assertEqual(replay(values, position, siblings), root_digest)
        self.assertNotEqual(replay(values[::-1], position, siblings), root_digest)
        self.assertNotEqual(replay((values[0] + 1, *values[1:]), position, siblings), root_digest)
        self.assertNotEqual(replay(values, position ^ 1, siblings), root_digest)
        bad_sibling = (bytes([siblings[0][0] ^ 1]) + siblings[0][1:], *siblings[1:])
        self.assertNotEqual(replay(values, position, bad_sibling), root_digest)
        with self.assertRaisesRegex(ValueError, "exceeds path height"):
            replay(values, position + (1 << height), siblings)

    def test_mutated_production_sources_fail_binding(self) -> None:
        sources = source_texts(ROOT)
        check_sources(sources)
        for name, anchors in SOURCE_ANCHORS.items():
            for anchor in anchors:
                with self.subTest(name=name, anchor=anchor):
                    mutated = dict(sources)
                    mutated[name] = sources[name].replace(anchor, "// removed leaf contract", 1)
                    with self.assertRaisesRegex(ValueError, "Merkle leaf source changed"):
                        check_sources(mutated)


if __name__ == "__main__":
    unittest.main()
