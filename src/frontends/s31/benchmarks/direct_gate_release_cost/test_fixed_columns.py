"""Fast byte-level checks for the native square4 fixed-column snapshot."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from fixed_columns import (FIXTURE, WORDS, check_formal_rows, read_fixture,
                           read_formal_rows)


class FixedColumnsFixtureTests(unittest.TestCase):
    def test_complete_shape_and_handwritten_source_rows(self) -> None:
        metadata, columns = read_fixture()
        self.assertEqual(len(columns), 8)
        self.assertTrue(all(len(column) == 512 for column in columns))
        self.assertEqual(metadata["gate_counts"],
                         {"add": 474, "sub": 1, "mul": 27, "pointwise_mul": 10})
        self.assertEqual(metadata["source_fixed_rows"], [
            {"id": 1, "op": "mul", "circuit_row": 6, "trace_row": 502},
            {"id": 2, "op": "mul", "circuit_row": 7, "trace_row": 503},
        ])
        self.assertEqual([column[502] for column in columns],
                         [0, 0, 0, 1, 22, 22, 23, 2])
        self.assertEqual([column[503] for column in columns],
                         [0, 0, 0, 1, 23, 23, 24, 4])
        self.assertEqual([column[473] for column in columns],
                         [1, 0, 0, 0, 1, 1, 511, 0])

    def test_changed_fixed_word_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            metadata_path = root / FIXTURE.name
            words_path = root / WORDS.name
            metadata_path.write_bytes(FIXTURE.read_bytes())
            altered = bytearray(WORDS.read_bytes())
            altered[0] ^= 1
            words_path.write_bytes(altered)
            with self.assertRaisesRegex(ValueError, "binary digest differs"):
                read_fixture(metadata_path, words_path)

    def test_all_native_cells_match_independent_formal_export(self) -> None:
        _, columns = read_fixture()
        rows = read_formal_rows()
        self.assertEqual(len(rows), 512)
        self.assertEqual(sum(len(row) for row in rows), 4096)
        check_formal_rows(columns)


if __name__ == "__main__":
    unittest.main()
