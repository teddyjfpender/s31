"""The package key, never the proof, selects production PCS admission."""

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.pcs_mode import key_fields_for_lowering, require_production


class PackagePcsModeTests(unittest.TestCase):
    def test_separate_sha_verifiers_keep_their_strict_legacy_key_bytes(self) -> None:
        self.assertEqual(key_fields_for_lowering("gate"), {"pcs_mode": "legacy_postcard"})
        for lowering in ("sha-joint", "sha-shift", "sha-fused"):
            with self.subTest(lowering=lowering):
                self.assertEqual(key_fields_for_lowering(lowering), {})

    def test_existing_and_explicit_legacy_keys(self) -> None:
        self.assertEqual(require_production({}), "legacy_postcard")
        self.assertEqual(require_production({"pcs_mode": "legacy_postcard"}), "legacy_postcard")

    def test_candidate_and_malformed_modes_fail_closed(self) -> None:
        for value in ("cas05_sparse_v6", "legacy", None, 1, {}, True):
            with self.subTest(value=value):
                with self.assertRaisesRegex(ValueError, "unsupported production PCS mode"):
                    require_production({"pcs_mode": value})


if __name__ == "__main__":
    unittest.main()
