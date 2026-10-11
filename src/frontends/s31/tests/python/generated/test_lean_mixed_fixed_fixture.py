"""Adversarial checks for the native-to-Lean fixed-row exporter gate."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))

from render_lean_mixed_fixed_fixture import (P, ROOTS, ROWS_SHA256, SOURCE,
                                             decode_native_json, expected_rows,
                                             validated_cases)


def synthetic_export() -> dict:
    cases = []
    for count in (1, 8):
        add_end = 468 - 7 * count
        point_start = add_end + 1 + 30 + 3 * count
        rows = []
        for index in range(512):
            op = (0 if index < add_end else 1 if index == add_end else
                  2 if index < point_start else 3)
            rows.append([int(column == op) for column in range(4)] + [0] * 4)
        for index, values in expected_rows(count).items():
            rows[index] = list(values)
        cases.append({"count": count, "source_sha256": SOURCE[count],
                      "fixed_root": ROOTS[count], "rows": rows})
    return {"schema": "s31-mixed-fixed-native-v1", "cases": cases}


def allow_changed_full_digest(data: dict) -> None:
    """Reach the independent schedule checker after mutating a fixture."""
    for case in data["cases"]:
        ROWS_SHA256[case["count"]] = hashlib.sha256(
            json.dumps(case["rows"], separators=(",", ":")).encode()).hexdigest()


class MixedFixedFixtureTest(unittest.TestCase):
    def setUp(self) -> None:
        # Synthetic rows exercise the checker without requiring Zig. The
        # production digest constants remain pinned and are tested by the
        # renderer against the actual native export.
        digests = {case["count"]: hashlib.sha256(
            json.dumps(case["rows"], separators=(",", ":")).encode()).hexdigest()
            for case in synthetic_export()["cases"]}
        self.digest_patch = patch.dict(ROWS_SHA256, digests)
        self.digest_patch.start()

    def tearDown(self) -> None:
        self.digest_patch.stop()

    def test_accepts_exact_schedule(self) -> None:
        self.assertEqual(set(validated_cases(synthetic_export())), {1, 8})

    def test_rejects_selected_address_and_multiplicity(self) -> None:
        for column in (4, 5, 6, 7):
            with self.subTest(column=column):
                data = synthetic_export()
                data["cases"][1]["rows"][0][column] += 1
                allow_changed_full_digest(data)
                with self.assertRaisesRegex(ValueError, "selected row"):
                    validated_cases(data)

    def test_rejects_selected_and_unselected_opcode(self) -> None:
        for index in (0, 300):
            with self.subTest(index=index):
                data = synthetic_export()
                data["cases"][0]["rows"][index][0] ^= 1
                allow_changed_full_digest(data)
                with self.assertRaisesRegex(ValueError, "opcode partition"):
                    validated_cases(data)

    def test_rejects_source_root_and_noncanonical_cell(self) -> None:
        for field in ("source_sha256", "fixed_root"):
            with self.subTest(field=field):
                data = synthetic_export()
                data["cases"][0][field] = "0" * 64
                with self.assertRaisesRegex(ValueError, "source|fixed root"):
                    validated_cases(data)
        data = synthetic_export()
        data["cases"][0]["rows"][300][4] = P
        with self.assertRaisesRegex(ValueError, "canonical cells"):
            validated_cases(data)

    def test_rejects_unselected_cell_even_with_unchanged_root_metadata(self) -> None:
        data = synthetic_export()
        data["cases"][0]["rows"][300][4] = 42
        with self.assertRaisesRegex(ValueError, "complete row digest"):
            validated_cases(data)

    def test_rejects_duplicate_or_missing_case(self) -> None:
        data = synthetic_export()
        data["cases"].append(copy.deepcopy(data["cases"][0]))
        with self.assertRaisesRegex(ValueError, "cases"):
            validated_cases(data)
        data = synthetic_export()
        data["cases"].pop()
        with self.assertRaisesRegex(ValueError, "cases"):
            validated_cases(data)

    def test_rejects_duplicate_json_key(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            decode_native_json('{"schema":"one","schema":"two"}')


if __name__ == "__main__":
    unittest.main()
