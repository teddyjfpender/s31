"""Static source and typed-boundary controls for the public one-call chip."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import flat_assignment_from_typed, statement_from_assignment
from abi.record_v2 import AbiError
from package.context import abi, public_record_chip_source
from text_frontend import compile_text


SOURCE = """struct Lanes { words: [m31; 4] }
struct Result { words: [m31; 4], again: [m31; 4] }
fn step(v: [m31; 4]) -> [m31; 4] {
    v .* v + splat<4>(7_m31)
}
circuit record_chip(public x: Lanes) -> public Result {
    let y = iterate<16>(step, x.words);
    Result { words: y, again: y }
}
"""


class RecordChipV2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source, _ = compile_text(SOURCE)

    def test_record_paths_flatten_to_exact_public_chip_shape(self) -> None:
        source = self.source
        self.assertEqual(source["version"], 2)
        self.assertTrue(public_record_chip_source(source))
        self.assertEqual(len(source["inputs"]), 1)
        self.assertEqual(len(source["nodes"]), 1)
        self.assertEqual(len(source["public_outputs"]), 1)
        descriptor = abi(source, "direct-chip")
        self.assertEqual(descriptor["schema"], "s31-public-abi-v2")
        self.assertEqual(descriptor["boundary"]["inputs"][0]["leaves"][0]["path"],
                         [{"root": "x"}, {"field": "words"}])
        self.assertEqual(descriptor["boundary"]["result"]["leaves"][0]["path"],
                         [{"root": "result"}, {"field": "words"}])

    def test_typed_assignment_has_eight_public_words_and_canonical_claim(self) -> None:
        source = self.source
        assignment = {
            "version": 2, "public_inputs": {"x": {"words": [0, 1, 2, 3]}},
            "private_inputs": {}, "result": {"words": [7, 8, 9, 10],
                                                 "again": [7, 8, 9, 10]},
        }
        import json
        encoded = (json.dumps(assignment, sort_keys=True, separators=(",", ":")) + "\n").encode()
        flat = flat_assignment_from_typed(source, encoded)
        self.assertEqual(list(flat["public_inputs"].values()), [[0, 1, 2, 3]])
        self.assertEqual(list(flat["public_outputs"].values()), [[7, 8, 9, 10]])
        statement = statement_from_assignment(source, flat)
        self.assertEqual(json.loads(statement)["leaves"], [
            {"path": [{"root": "x"}, {"field": "words"}], "words": [0, 1, 2, 3]},
            {"path": [{"root": "result"}, {"field": "words"}], "words": [7, 8, 9, 10]},
            {"path": [{"root": "result"}, {"field": "again"}], "words": [7, 8, 9, 10]},
        ])
        assignment["result"]["again"][0] = 11
        with self.assertRaises(AbiError):
            flat_assignment_from_typed(source, (json.dumps(
                assignment, sort_keys=True, separators=(",", ":")) + "\n").encode())

    def test_fail_closed_shape_and_visibility(self) -> None:
        variants = []
        for mutate in (
            lambda source: source["inputs"][0].update(visibility="private"),
            lambda source: source["inputs"][0].update(length=3),
            lambda source: source["nodes"][0].update(rounds=15),
            lambda source: source["nodes"][0]["body"][1].update(constant=(1 << 31) - 1),
            lambda source: source["nodes"].append(copy.deepcopy(source["nodes"][0])),
        ):
            changed = copy.deepcopy(self.source)
            mutate(changed)
            variants.append(changed)
        for changed in variants:
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                abi(changed, "direct-chip")
        with self.assertRaises(ValueError):
            abi(self.source, "chip")

    def test_descriptor_is_derived_from_source_not_package_metadata(self) -> None:
        changed = copy.deepcopy(self.source)
        changed["public_abi"]["result"]["leaves"][0]["path"][1]["field"] = "forged"
        with self.assertRaises(AbiError):
            abi(changed, "direct-chip")
        changed = copy.deepcopy(self.source)
        changed["public_abi"]["inputs"][0]["visibility"] = "private"
        with self.assertRaises(AbiError):
            abi(changed, "direct-chip")


if __name__ == "__main__":
    unittest.main()
