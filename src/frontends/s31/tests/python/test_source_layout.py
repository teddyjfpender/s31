"""Source-layout inspection binds nominal names to exact erased relations."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from inspection.source_layout import source_layout
from package.context import lower_text


class SourceLayoutTests(unittest.TestCase):
    def test_record_layout_and_digest_match_compiler_output(self) -> None:
        source = S31 / "examples/arithmetic/record_square_sum_destructure.s31"
        layout = source_layout(source)
        _, encoded, _ = lower_text(source)
        self.assertEqual(layout["normalized_relation_sha256"],
                         hashlib.sha256(encoded).hexdigest())
        self.assertEqual(layout["source_sha256"],
                         hashlib.sha256(source.read_bytes()).hexdigest())
        self.assertEqual(layout["records"], [{
            "name": "Powers",
            "fields": [
                {"name": "square", "type": {"kind": "m31", "length": 4}},
                {"name": "doubled", "type": {"kind": "m31", "length": 4}},
            ],
            "flattened_leaves": [
                {"path": ["square"], "type": {"kind": "m31", "length": 4},
                 "relation_kind": "m31", "relation_length": 4},
                {"path": ["doubled"], "type": {"kind": "m31", "length": 4},
                 "relation_kind": "m31", "relation_length": 4},
            ],
            "flattened_leaf_count": 2,
            "layout_depth": 2,
        }])
        manual = source.with_name("record_square_sum_manual.s31")
        self.assertEqual(layout["normalized_relation_sha256"],
                         source_layout(manual)["normalized_relation_sha256"])

    def test_cli_reports_fixed_width_record_without_building_a_package(self) -> None:
        source = S31 / "examples/math/division/record_i32_division.s31"
        result = subprocess.run([sys.executable, str(S31 / "python/s31.py"),
                                 "source-layout", str(source)],
                                check=True, capture_output=True, text=True)
        layout = json.loads(result.stdout)
        self.assertEqual(layout["schema"], "s31-source-layout-v1")
        self.assertEqual(layout["circuit"], "record_i32_division")
        self.assertEqual(layout["records"][0]["flattened_leaves"], [
            {"path": [name], "type": {"kind": "i32", "length": 2},
             "relation_kind": "u16", "relation_length": 2}
            for name in ("quotient", "remainder")
        ])
        self.assertEqual(layout["functions"][0]["result"], {"struct": "DivResult"})

    def test_nested_paths_are_unambiguous_and_in_declaration_order(self) -> None:
        source = """struct Inner { value: [m31; 1] }
struct Outer { nested: Inner, pair: (Inner, [m31; 2]) }
circuit p(private x: [m31; 1]) -> public [m31; 1] { x }
"""
        with tempfile.TemporaryDirectory(prefix="s31-layout-") as directory:
            path = Path(directory) / "nested.s31"
            path.write_text(source)
            layout = source_layout(path)
        outer = layout["records"][1]
        self.assertEqual([leaf["path"] for leaf in outer["flattened_leaves"]], [
            ["nested", "value"], ["pair", 0, "value"], ["pair", 1],
        ])
        self.assertEqual(outer["flattened_leaf_count"], 3)
        self.assertEqual(outer["fields"][0]["type"], {"struct": "Inner"})


if __name__ == "__main__":
    unittest.main()
