"""Canonical public-record codec controls before the v2 proof protocol exists."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from abi.record_v2 import AbiError, decode_statement, encode_statement, layout_digest
from language.parser import Parser
from language.syntax import RecordType, TupleType
from s31_stdlib import Type


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


class RecordAbiV2Tests(unittest.TestCase):
    def setUp(self) -> None:
        self.inner = RecordType("Inner", (("word", Type("m31", 1)),))
        self.outer = RecordType("Outer", (
            ("nested", self.inner),
            ("pair", TupleType((Type("int_u8", 1), Type("bit", 1)))),
        ))
        self.value = {"pair": ([255], [1]), "nested": {"word": [7]}}

    def test_nested_roundtrip_and_ordered_tagged_paths(self) -> None:
        encoded = encode_statement(self.outer, "result", self.value)
        statement = json.loads(encoded)
        self.assertEqual(decode_statement(self.outer, "result", encoded),
                         {"nested": {"word": [7]}, "pair": ([255], [1])})
        self.assertEqual([leaf["path"] for leaf in statement["leaves"]], [
            [{"root": "result"}, {"field": "nested"}, {"field": "word"}],
            [{"root": "result"}, {"field": "pair"}, {"tuple": 0}],
            [{"root": "result"}, {"field": "pair"}, {"tuple": 1}],
        ])
        self.assertEqual(encoded, encode_statement(self.outer, "result", {
            "nested": {"word": [7]}, "pair": ([255], [1]),
        }))

    def test_real_source_declarations_feed_the_codec(self) -> None:
        source = """struct Inner { word: [m31; 1] }
struct Outer { nested: Inner, pair: (u8, bit) }
circuit example(private x: [m31; 1]) -> public [m31; 1] { x }
"""
        parser = Parser(source, "abi-fixture.s31")
        parser.parse()
        parsed_type = parser.records["Outer"]
        self.assertEqual(layout_digest(parsed_type, "result"),
                         layout_digest(self.outer, "result"))
        self.assertEqual(decode_statement(parsed_type, "result",
                         encode_statement(parsed_type, "result", self.value)),
                         {"nested": {"word": [7]}, "pair": ([255], [1])})

    def test_nominal_layout_and_field_order_change_digest(self) -> None:
        same_shape = RecordType("Other", self.outer.fields)
        reversed_order = RecordType("Outer", tuple(reversed(self.outer.fields)))
        encoded = encode_statement(self.outer, "result", self.value)
        for typ in (same_shape, reversed_order):
            with self.subTest(typ=typ), self.assertRaisesRegex(AbiError, "layout differs"):
                decode_statement(typ, "result", encoded)
            self.assertNotEqual(layout_digest(self.outer, "result"),
                                layout_digest(typ, "result"))
        with self.assertRaisesRegex(AbiError, "layout differs"):
            decode_statement(self.outer, "other", encoded)

    def test_missing_extra_duplicate_and_reordered_leaves_reject(self) -> None:
        statement = json.loads(encode_statement(self.outer, "result", self.value))
        variants = []
        variants.append({**statement, "leaves": statement["leaves"][:-1]})
        variants.append({**statement, "leaves": statement["leaves"] + statement["leaves"][-1:]})
        variants.append({**statement, "leaves": list(reversed(statement["leaves"]))})
        changed = json.loads(canonical(statement))
        changed["leaves"][0]["path"][1] = {"tuple": 0}
        variants.append(changed)
        for variant in variants:
            with self.subTest(leaves=variant["leaves"]), self.assertRaises(AbiError):
                decode_statement(self.outer, "result", canonical(variant))

    def test_noncanonical_value_words_reject_at_both_edges(self) -> None:
        for typ, bad in ((Type("bit", 1), [2]), (Type("int_u8", 1), [256]),
                         (Type("m31", 1), [2**31 - 1]), (Type("u16", 1), [65536]),
                         (Type("m31", 1), [True])):
            with self.subTest(typ=typ), self.assertRaisesRegex(AbiError, "noncanonical"):
                encode_statement(typ, "result", bad)
            valid = json.loads(encode_statement(typ, "result", [0]))
            valid["leaves"][0]["words"] = bad
            with self.assertRaisesRegex(AbiError, "noncanonical"):
                decode_statement(typ, "result", canonical(valid))

    def test_json_canonicality_and_duplicate_object_keys_reject(self) -> None:
        encoded = encode_statement(self.outer, "result", self.value)
        with self.assertRaisesRegex(AbiError, "noncanonical"):
            decode_statement(self.outer, "result", encoded.rstrip(b"\n"))
        with self.assertRaisesRegex(AbiError, "duplicate JSON key"):
            decode_statement(self.outer, "result", encoded.replace(
                b'"version":2', b'"version":2,"version":2'))
        with self.assertRaisesRegex(AbiError, "wrong public statement version"):
            value = json.loads(encoded)
            value["version"] = True
            decode_statement(self.outer, "result", canonical(value))

    def test_source_value_shape_rejects_unknown_fields_and_arity(self) -> None:
        with self.assertRaisesRegex(AbiError, "every declared field"):
            encode_statement(self.outer, "result", {"nested": {"word": [7]}})
        with self.assertRaisesRegex(AbiError, "wrong arity"):
            encode_statement(self.outer, "result", {"nested": {"word": [7]},
                                                     "pair": ([255],)})

    def test_invalid_nominal_layouts_reject_before_hashing(self) -> None:
        duplicate = RecordType("Bad", (("x", Type("m31", 1)),
                                       ("x", Type("bit", 1))))
        with self.assertRaisesRegex(AbiError, "duplicate"):
            layout_digest(duplicate, "result")
        inconsistent = RecordType("Outer", (("first", RecordType(
            "Repeated", (("x", Type("m31", 1)),))),
                                            ("second", RecordType(
            "Repeated", (("x", Type("bit", 1)),)))))
        with self.assertRaisesRegex(AbiError, "same nominal record name"):
            layout_digest(inconsistent, "result")
        with self.assertRaisesRegex(AbiError, "invalid root name"):
            layout_digest(self.outer, "result.dot")

    def test_current_public_word_budget_is_enforced(self) -> None:
        too_wide = Type("m31", 9)
        with self.assertRaisesRegex(AbiError, "exceeds eight words"):
            encode_statement(too_wide, "result", [0] * 9)
        encoded = encode_statement(Type("m31", 8), "result", [0] * 8)
        statement = json.loads(encoded)
        statement["layout_sha256"] = layout_digest(too_wide, "result")
        statement["leaves"][0]["words"].append(0)
        with self.assertRaisesRegex(AbiError, "exceeds eight words"):
            decode_statement(too_wide, "result", canonical(statement))


if __name__ == "__main__":
    unittest.main()
