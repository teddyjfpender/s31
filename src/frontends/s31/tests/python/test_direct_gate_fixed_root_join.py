"""Bounded proof-header decoding controls for the package-level root join."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "python"))

from package.fixed_root_join import proof_roots  # noqa: E402


def header() -> bytes:
    # Direct-Gate envelope, nonce, one QM31 sum, PCS config, optional None,
    # four commitment roots. Only the first two roots are interpreted here.
    return (b"S31NAT7G" + bytes(8 + 16) + bytes((26, 1, 70, 0, 1, 0, 4)) +
            bytes(range(128)))


class DirectGateProofHeaderTest(unittest.TestCase):
    def test_first_roots_have_exact_offsets(self) -> None:
        raw = header()
        fixed, main, main_offset = proof_roots(raw)
        self.assertEqual(fixed, bytes(range(32)))
        self.assertEqual(main, bytes(range(32, 64)))
        self.assertEqual(main_offset, 8 + 8 + 16 + 7 + 32)
        self.assertEqual(raw[main_offset - 32:main_offset], fixed)

    def test_changed_profile_and_root_count_fail_closed(self) -> None:
        raw = bytearray(header())
        for offset, message in ((0, "profile"), (32, "config"), (38, "count")):
            changed = raw.copy()
            changed[offset] ^= 1
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, message):
                proof_roots(bytes(changed))

    def test_noncanonical_varint_is_rejected(self) -> None:
        raw = header()
        # Encode the initial 26 as 0x9a 0x00 while preserving the remaining
        # config. A postcard decoder must not admit the nonminimal encoding.
        changed = raw[:32] + bytes((0x9a, 0)) + raw[33:]
        with self.assertRaisesRegex(ValueError, "noncanonical proof varint"):
            proof_roots(changed)


if __name__ == "__main__":
    unittest.main()
