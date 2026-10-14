"""Source-byte, typed-rule, and normalized-relation controls for field programs."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from package.pure_field_derivation import (ARTIFACT, UnsupportedPureField,
                                           admitted, derive, make_certificate,
                                           verify_artifact)
from text_frontend import compile_text


def encoded(relation: dict) -> bytes:
    return (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()


SCALAR = b"""use std@1;
circuit choose(public x: [m31; 1], public a: [m31; 1],
               public b: [m31; 1]) -> public [m31; 1] {
    let z = std::field::is_zero(x);
    let copy = z;
    let result = std::field::select(copy, a, b);
    result
}
"""

MIXED = b"""use std@1;
circuit mixed(public x: [m31; 1], private a: [m31; 4],
              private b: [m31; 4]) -> public [m31; 4] {
    let squared = a .* a;
    let z = std::field::is_zero(x);
    let chosen = select(z, squared, b);
    let result = std::math::inv(chosen);
    result
}
"""


class PureFieldDerivationTests(unittest.TestCase):
    def test_compositional_normalization_and_alias(self) -> None:
        for source, ops in ((SCALAR, ["is_zero", "select"]),
                            (MIXED, ["mul", "is_zero", "select", "inv"])):
            with self.subTest(source=source[:35]):
                independent, rules = derive(source)
                production, _ = compile_text(source.decode())
                self.assertEqual(independent, production)
                self.assertEqual([node["op"] for node in independent["nodes"]], ops)
                self.assertEqual(len(rules["steps"]), len(ops) + (source is SCALAR))
                relation_bytes = encoded(production)
                self.assertTrue(admitted(source, relation_bytes))
                certificate = make_certificate(source, relation_bytes)
                self.assertEqual(certificate["derivation"], rules)
                with tempfile.TemporaryDirectory() as directory:
                    package = Path(directory)
                    (package / "source.s31").write_bytes(source)
                    (package / "source.s31.json").write_bytes(relation_bytes)
                    raw = encoded(certificate)
                    (package / ARTIFACT).write_bytes(raw)
                    import hashlib
                    manifest = {"source_text_sha256": hashlib.sha256(source).hexdigest(),
                                "artifacts": {ARTIFACT: hashlib.sha256(raw).hexdigest()}}
                    verify_artifact(package, manifest)
                    changed = json.loads(raw)
                    changed["derivation"]["steps"][-1]["resolved_operands"][-1] = "x"
                    raw = encoded(changed)
                    (package / ARTIFACT).write_bytes(raw)
                    manifest["artifacts"][ARTIFACT] = hashlib.sha256(raw).hexdigest()
                    with self.assertRaisesRegex(ValueError, "differs from exact source"):
                        verify_artifact(package, manifest)

    def test_arbitrary_straight_line_length_under_resource_bound(self) -> None:
        lets = ["let z = std::field::is_zero(x);", "let picked = select(z, a, b);"]
        previous = "picked"
        for index in range(26):
            next_name = f"v{index}"
            lets.append(f"let {next_name} = {previous} + a;")
            previous = next_name
        source = ("use std@1; circuit long(public x:[m31;1], public a:[m31;1], "
                  "public b:[m31;1]) -> public [m31;1] { " + " ".join(lets) +
                  " " + previous + " }").encode()
        independent, derivation = derive(source)
        production, _ = compile_text(source.decode())
        self.assertEqual(independent, production)
        self.assertEqual(len(derivation["steps"]), 28)
        self.assertEqual(len(independent["nodes"]), 28)

    def test_array_lengths_and_private_operands(self) -> None:
        for lanes in (1, 2, 4, 8):
            with self.subTest(lanes=lanes):
                source = (f"use std@1; circuit lanes{lanes}(private x:[m31;{lanes}]) "
                          f"-> public [m31;{lanes}] {{ let y = std::math::inv(x); "
                          "let z = y .* x; z }").encode()
                independent, rules = derive(source)
                production, _ = compile_text(source.decode())
                self.assertEqual(independent, production)
                self.assertEqual([step["result"]["length"] for step in rules["steps"]],
                                 [lanes, lanes])

    def test_fail_closed_wrong_relation_and_source(self) -> None:
        relation, _ = compile_text(SCALAR.decode())
        wrong = json.loads(encoded(relation))
        wrong["nodes"][-1]["rhs"] = "a"
        self.assertFalse(admitted(SCALAR, encoded(wrong)))
        with self.assertRaisesRegex(ValueError, "normalized relation differs"):
            make_certificate(SCALAR, encoded(wrong))
        for source in (SCALAR.replace(b"is_zero(x)", b"is_zero(a)"),
                       SCALAR.replace(b"select(copy, a, b)", b"select(a, a, b)"),
                       SCALAR.replace(b"use std@1;", b""),
                       SCALAR + b" trailing",
                       SCALAR.replace(b"let copy = z;", b"let copy = future;")):
            with self.subTest(source=source[:50]):
                if b"is_zero(a)" in source:
                    self.assertFalse(admitted(source, encoded(relation)))
                else:
                    with self.assertRaises(UnsupportedPureField):
                        derive(source)
        repeated = b"""use std@1; circuit repeated(public x:[m31;1]) -> public [m31;1] {
            let first = std::math::inv(x);
            let second = std::math::inv(x);
            second
        }"""
        with self.assertRaisesRegex(UnsupportedPureField, "reused inverse"):
            derive(repeated)


if __name__ == "__main__":
    unittest.main()
