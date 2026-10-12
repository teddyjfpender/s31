"""The package's raw source parser agrees with native duplicate-key admission."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.context import load_source, parse_source_json


class RecordSourceJsonTests(unittest.TestCase):
    def test_valid_raw_source_preserves_original_bytes(self) -> None:
        encoded = b'{"version":2,"name":"record","public_abi":{"schema":"v2"}}\n'
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.s31.json"
            path.write_bytes(encoded)
            source, original = load_source(path)
        self.assertEqual(source["public_abi"], {"schema": "v2"})
        self.assertEqual(original, encoded)

    def test_duplicate_top_level_or_nested_record_abi_key_rejects(self) -> None:
        for encoded in (
            b'{"version":2,"version":1,"name":"record"}',
            b'{"version":2,"name":"record","public_abi":'
            b'{"schema":"v2","schema":"v1"}}',
        ):
            with self.subTest(encoded=encoded), self.assertRaisesRegex(ValueError, "duplicate S31 source JSON key"):
                parse_source_json(encoded)


if __name__ == "__main__":
    unittest.main()
