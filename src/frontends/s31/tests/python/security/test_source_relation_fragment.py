"""Independent bounded source/relation checks, including re-sealed forgeries."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.source_relation_fragment import (CAPABILITY, UnsupportedSourceRelationFragment,
                                              check_package_source_relation,
                                              check_source_relation,
                                              parse_source_fragment)
from text_frontend import compile_text

SOURCE = """circuit checked(public x: [m31; 4], private y: [m31; 4]) -> public [m31; 4] {
    let bias = splat<4>(7_m31);
    let twice = x + x;
    assert_eq(y, twice);
    let product = y .* x;
    let result = product + bias;
    result
}
"""


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class SourceRelationFragmentTests(unittest.TestCase):
    def test_honest_source_matches_production_relation(self) -> None:
        sources = [
            SOURCE,
            "circuit affine(private x: [m31; 4]) -> public [m31; 4] { "
            "let square = x .* x; let result = square + splat<4>(7_m31); result }",
            "circuit mul(private x: [m31; 4]) -> public [m31; 4] { "
            "let c = splat<4>(2147483646_m31); let result = c .* x; result }",
            "circuit alias(public x: [m31; 4]) -> public [m31; 4] { "
            "let a = x; let result = a + x; result }",
        ]
        for source in sources:
            with self.subTest(source=source[:35]):
                expected = parse_source_fragment(source.encode())
                actual, _ = compile_text(source)
                self.assertEqual(expected, actual)
                self.assertEqual(check_source_relation(source.encode(), encoded(actual))["capability"],
                                 CAPABILITY)

    def test_resealed_relation_and_abi_forgery_rejected(self) -> None:
        source_bytes = SOURCE.encode()
        relation, _ = compile_text(SOURCE)
        with tempfile.TemporaryDirectory() as root:
            package = Path(root)
            (package / "source.s31").write_bytes(source_bytes)

            def reseal(changed: dict, abi: dict) -> None:
                relation_bytes = encoded(changed)
                abi_bytes = encoded(abi)
                (package / "source.s31.json").write_bytes(relation_bytes)
                (package / "public-abi.json").write_bytes(abi_bytes)
                manifest = {
                    "schema": "s31-package-v1", "name": changed["name"],
                    "lowering": "direct-gate", "source_text_sha256": digest(source_bytes),
                    "program_sha256": digest(relation_bytes),
                    "artifacts": {
                        "source.s31": digest(source_bytes),
                        "source.s31.json": digest(relation_bytes),
                        "public-abi.json": digest(abi_bytes),
                    },
                }
                (package / "manifest.json").write_bytes(encoded(manifest))

            abi = {"schema": "s31-public-abi-v1",
                   "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
                   "public_inputs": [{"name": "x", "kind": "m31", "length": 4}],
                   "public_outputs": [{"name": "result", "kind": "m31", "length": 4}]}
            reseal(relation, abi)
            self.assertEqual(check_package_source_relation(package)["capability"], CAPABILITY)

            variants: dict[str, dict] = {}
            wrong_op = copy.deepcopy(relation)
            wrong_op["nodes"][1]["op"] = "add"
            variants["wrong-op"] = wrong_op
            wrong_constant = copy.deepcopy(relation)
            wrong_constant["nodes"][2]["constant"] = 8
            variants["wrong-constant"] = wrong_constant
            dropped_assertion = copy.deepcopy(relation)
            dropped_assertion["assertions"] = []
            variants["dropped-assertion"] = dropped_assertion
            visibility = copy.deepcopy(relation)
            visibility["inputs"][0]["visibility"] = "private"
            variants["changed-visibility"] = visibility
            order = copy.deepcopy(relation)
            order["inputs"].reverse()
            variants["changed-input-order"] = order
            for label, changed in variants.items():
                with self.subTest(forgery=label):
                    reseal(changed, abi)
                    with self.assertRaisesRegex(ValueError, "relation differs"):
                        check_package_source_relation(package)

            reseal(relation, {**abi, "public_inputs": []})
            with self.assertRaisesRegex(ValueError, "public ABI differs"):
                check_package_source_relation(package)
            reseal(relation, {**abi, "public_outputs": [{"name": "x", "kind": "m31", "length": 4}]})
            with self.assertRaisesRegex(ValueError, "public ABI differs"):
                check_package_source_relation(package)
            float_abi = copy.deepcopy(abi)
            float_abi["public_inputs"][0]["length"] = 4.0
            reseal(relation, float_abi)
            with self.assertRaisesRegex(ValueError, "public ABI differs"):
                check_package_source_relation(package)

    def test_unknown_relation_field_and_duplicate_json_key_rejected(self) -> None:
        relation, _ = compile_text(SOURCE)
        changed = copy.deepcopy(relation)
        changed["nodes"][0]["unused"] = 0
        with self.assertRaisesRegex(ValueError, "relation differs"):
            check_source_relation(SOURCE.encode(), encoded(changed))
        duplicate = encoded(relation).replace(b'"version": 1\n', b'"version": 1, "version": 1\n')
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            check_source_relation(SOURCE.encode(), duplicate)

    def test_json_numeric_types_cannot_alias_expected_integers(self) -> None:
        relation, _ = compile_text(SOURCE)
        for path, changed in (
            ("version", True),
            ("version", 1.0),
            ("constant", 7.0),
        ):
            with self.subTest(path=path, changed=changed):
                forged = copy.deepcopy(relation)
                if path == "version":
                    forged["version"] = changed
                else:
                    forged["nodes"][2]["constant"] = changed
                with self.assertRaisesRegex(ValueError, "relation differs"):
                    check_source_relation(SOURCE.encode(), encoded(forged))

    def test_unsupported_source_rejected_closed(self) -> None:
        unsupported = [
            SOURCE.replace("7_m31", "2147483647_m31"),
            SOURCE.replace("7_m31", "07_m31"),
            SOURCE.replace("let bias", "let x"),
            SOURCE.replace("let result = product + bias;", "let result = product + missing;"),
            SOURCE.replace("result\n}", "result\n} junk"),
            SOURCE.replace("private y", "public y"),
            SOURCE.replace("let product = y .* x;", "let product = y .* x .* x;"),
            SOURCE.replace("let product = y .* x;", "let product = y[0] .* x;"),
            SOURCE.replace("circuit checked", "circuit enum"),
            SOURCE.replace("circuit checked", "circuit match"),
            SOURCE.replace("let product", "let enum"),
            "use std; " + SOURCE,
            SOURCE.replace("assert_eq(y, twice);", "assert_eq(y, splat<4>(0_m31));"),
            SOURCE.replace("assert_eq(y, twice);", "assert_eq(y, twice); assert_eq(twice, y);"),
        ]
        for source in unsupported:
            with self.subTest(source=source[:50]), self.assertRaises(UnsupportedSourceRelationFragment):
                parse_source_fragment(source.encode())
        with self.assertRaises(UnsupportedSourceRelationFragment):
            parse_source_fragment(SOURCE.encode() + b"\xff")


if __name__ == "__main__":
    unittest.main()
