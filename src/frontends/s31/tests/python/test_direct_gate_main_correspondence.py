"""Pure source-to-full-main checks against four earlier native exports."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
HERE = S31 / "tests/acceptance/compiler_correspondence"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(HERE))

import full_native_roster as roster  # noqa: E402
from package.direct_gate_main_correspondence import (  # noqa: E402
    P, canonical_column_bytes, check_export, expected_main_columns,
    source_values,
)


class DirectGateMainCorrespondenceTests(unittest.TestCase):
    def test_full_source_derived_main_matches_four_native_fixtures(self) -> None:
        for sample, prefix in roster.selected_samples():
            with self.subTest(prefix=prefix):
                _, syntax, _, _ = roster.source_plan(sample)
                physical = json.loads((roster.FIXTURES / f"{prefix}-full-native-roster.json")
                                      .read_bytes())["physical"]
                digest = hashlib.sha256(canonical_column_bytes(
                    physical["main_columns"], 12)).hexdigest()
                root_report = {"public_words": physical["public_words"],
                               "main_columns_sha256": digest}
                checked = check_export(syntax, roster.INPUT, physical, root_report)
                self.assertEqual(checked["source_derived_main_cells"], 6144)
                self.assertEqual(checked["source_derived_main_columns_sha256"], digest)
                expected, public = expected_main_columns(syntax, roster.INPUT)
                self.assertEqual(expected, physical["main_columns"])
                self.assertEqual(public, physical["public_words"])

                for label in ("cell", "column-order", "claim", "digest"):
                    changed = copy.deepcopy(physical)
                    changed_root = copy.deepcopy(root_report)
                    if label == "cell":
                        changed["main_columns"][0][0] = (
                            changed["main_columns"][0][0] + 1) % P
                    elif label == "column-order":
                        changed["main_columns"][0], changed["main_columns"][1] = (
                            changed["main_columns"][1], changed["main_columns"][0])
                    elif label == "claim":
                        changed["public_words"][7] = (changed["public_words"][7] + 1) % P
                    else:
                        changed_root["main_columns_sha256"] = "00" * 32
                    with self.subTest(mutation=label), self.assertRaises(ValueError):
                        check_export(syntax, roster.INPUT, changed, changed_root)

    def test_optimized_cse_source_evaluates_its_return(self) -> None:
        source = ("circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { "
                  "let a = x + x; let b = x .* x; let c = a + b; "
                  "let d = b + a; d }\n")
        from package.correspondence import parse_source_optimized
        _, syntax = parse_source_optimized(source.encode())
        values, claimed = source_values(syntax, (0, 1, 2, 7))
        self.assertEqual(syntax["source_to_canonical"], [0, 1, 2, 3, 3])
        self.assertEqual(len(values), 4)
        self.assertEqual(claimed, (0, 3, 8, 63))
        main, public = expected_main_columns(syntax, (0, 1, 2, 7))
        self.assertEqual(len(main), 12)
        self.assertTrue(all(len(column) == 512 for column in main))
        self.assertEqual(public, [0, 1, 2, 7, 0, 3, 8, 63])

    def test_ordered_subtraction_reconstructs_complete_main_trace(self) -> None:
        from package.correspondence import parse_source

        example = S31 / "examples/functional/release_sub4"
        _, direct = parse_source((example / "manual.s31").read_bytes())
        _, helper = parse_source((example / "functional.s31").read_bytes())
        self.assertEqual(direct, helper)
        self.assertEqual([item["op"] for item in direct["instructions"]],
                         ["add", "sub", "sub"])
        words = (0, 1, 2, 7)
        values, claimed = source_values(direct, words)
        self.assertEqual(values[-1], claimed)
        self.assertEqual(claimed, (0, P - 2, P - 4, P - 14))
        main, public = expected_main_columns(direct, words)
        self.assertEqual(len(main), 12)
        self.assertTrue(all(len(column) == 512 for column in main))
        self.assertEqual(public, [*words, *claimed])


if __name__ == "__main__":
    unittest.main()
