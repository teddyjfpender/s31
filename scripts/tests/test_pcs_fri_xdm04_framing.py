"""Hostile controls for independent XDM04 byte framing and path replay."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "release"))
import pcs_fri_xdm04_framing as xdm  # noqa: E402


class FramingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        fixture_path = Path(__file__).resolve().parents[2] / "formal/s31/tests/fixtures/xdm04-native-framing.json"
        cls.fixture = json.loads(fixture_path.read_text())

    def reject(self, mutate) -> None:
        fixture = copy.deepcopy(self.fixture)
        mutate(fixture)
        with self.assertRaises(xdm.AuditError):
            xdm.check_fixture(fixture)

    def test_exact_preimages_and_transposed_side(self) -> None:
        row = [1, 256]
        body = b"\x02\x00\x01\x00\x00\x00\x00\x01\x00\x00"
        self.assertEqual(xdm.leaf_preimage(row), b"S31XDL03" + body)
        left, right = bytes(range(32)), bytes(range(32, 64))
        self.assertEqual(xdm.upper_preimage(left, right), b"S31XDU03" + left + right)
        self.assertEqual(xdm.inserted_preimage(left, right, row),
                         b"S31XDI03" + xdm.digest(xdm.upper_preimage(left, right)) + body)
        self.assertNotEqual(xdm.inserted(left, right, row),
                            xdm.digest(b"S31XDI03" + left + right + body))
        self.assertEqual(xdm.children(4, 2), (4, 6))
        self.assertEqual(xdm.sibling(4, 2), 0)
        self.assertEqual(xdm.parent(4, 2), 0)
        self.assertEqual(xdm.path_position(4, 2), 1)
        self.assertNotEqual(xdm.path_position(4, 2) & 1, 2 & 1)

    def test_native_fixture(self) -> None:
        self.assertEqual(xdm.check_fixture(self.fixture),
                         {"queries": 3, "heights": 3, "openings": 18,
                          "witness_hashes": 10})

    def test_header_and_word_mutations(self) -> None:
        self.reject(lambda f: f.__setitem__("root", "00" * 32))
        self.reject(lambda f: f.__setitem__("wire", "00" + f["wire"][2:]))

        def reverse_first_row_word(f):
            wire = bytearray.fromhex(f["wire"])
            # 8 magic + 20 fixed header + 2*height_count column bytes + 32 root
            # + first raw query word.
            offset = 8 + 20 + 2 * f["height_count"] + 32 + 4
            wire[offset:offset + 4] = wire[offset:offset + 4][::-1]
            f["wire"] = wire.hex()

        self.reject(reverse_first_row_word)

    def test_witness_and_capture_mutations(self) -> None:
        def flip_last_witness_byte(f):
            wire = bytearray.fromhex(f["wire"])
            wire[-1] ^= 1
            f["wire"] = wire.hex()

        self.reject(flip_last_witness_byte)
        self.reject(lambda f: f["openings"][0].__setitem__("path_position", 0))
        self.reject(lambda f: f["openings"][0].__setitem__("start", "00" * 32))
        self.reject(lambda f: f["openings"][0]["steps"][0].__setitem__("sibling", "00" * 32))
        self.reject(lambda f: f["openings"][0]["steps"][0].__setitem__("inserted_row", None))
        self.reject(lambda f: f["topology"][5].__setitem__("path_position", 0))

    def test_source_and_duplicate_mutations(self) -> None:
        self.reject(lambda f: f["source_columns"][0][0].__setitem__(4, 10))
        self.reject(lambda f: f["openings"][-1]["row"].__setitem__(0, 10))

    def test_admission_and_resource_bound(self) -> None:
        self.reject(lambda f: f.__setitem__("largest_log_size", 23))
        with self.assertRaisesRegex(xdm.AuditError, "resource cap"):
            xdm.check_fixture(self.fixture, max_nodes=32)


if __name__ == "__main__":
    unittest.main()
