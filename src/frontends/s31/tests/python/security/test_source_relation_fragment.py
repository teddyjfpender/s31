"""Independent bounded source/relation checks, including re-sealed forgeries."""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.source_relation_fragment import (CAPABILITY, CERTIFICATE_SCHEMA,
                                              LEAN_EFFECTS_PROFILE, LEAN_SEMANTIC_PROFILE,
                                              MAX_CERTIFICATE_BYTES,
                                              UnsupportedSourceRelationFragment,
                                              check_package_source_relation,
                                              check_source_relation_certificate,
                                              check_source_relation,
                                              make_source_relation_certificate,
                                              parse_source_fragment,
                                              verify_source_relation_artifact)
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
SUB5_FUNCTIONAL = """fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }
circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {
    let out = difference(a, b);
    out
}
"""


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class SourceRelationFragmentTests(unittest.TestCase):
    def test_formal_fixture_is_exact_source_derived_certificate(self) -> None:
        fixture = S31.parents[2] / "formal/s31/fixtures/correspondence"
        source = (fixture / "source_relation_ssa_v1.s31").read_bytes()
        relation = (fixture / "source_relation_ssa_v1.relation.json").read_bytes()
        certificate = (fixture / "source_relation_ssa_v1.json").read_bytes()
        self.assertEqual(encoded(compile_text(source.decode())[0]), relation)
        self.assertEqual(encoded(make_source_relation_certificate(source, relation)),
                         certificate)
        self.assertEqual(check_source_relation_certificate(source, relation, certificate)
                         ["lean_semantic_profile"], LEAN_SEMANTIC_PROFILE)

    def test_multiple_pure_helpers_compose_without_trusting_specializer(self) -> None:
        source = ("fn delta(x: [m31; 3], y: [m31; 3]) -> [m31; 3] { x - y }\n"
                  "fn square(x: [m31; 3], y: [m31; 3]) -> [m31; 3] { x .* y }\n"
                  "circuit calc(public a: [m31; 3], private b: [m31; 3]) "
                  "-> public [m31; 3] { let d = delta(a, b); "
                  "let out = square(d, d); out }")
        produced, _ = compile_text(source)
        checked = parse_source_fragment(source.encode())
        self.assertEqual(checked, produced)
        self.assertEqual([node["op"] for node in checked["nodes"]], ["sub", "mul"])
        certificate = make_source_relation_certificate(source.encode(), encoded(produced))
        self.assertEqual(certificate["lean_semantic_profile"], LEAN_SEMANTIC_PROFILE)
        self.assertEqual(certificate["ssa"]["nodes"][1]["lhs"], 2)
        self.assertEqual(certificate["ssa"]["nodes"][1]["rhs"], 2)
        imported = "use std@1;\n" + source
        self.assertEqual(parse_source_fragment(imported.encode()),
                         compile_text(imported)[0])
        for changed in (source.replace("fn square", "fn delta"),
                        source.replace("let out = square", "let out = unknown"),
                        source.replace("let out = square(d, d);", "let out = d + d;")):
            with self.subTest(changed=changed[:80]), self.assertRaises(
                    UnsupportedSourceRelationFragment):
                parse_source_fragment(changed.encode())

    def test_unary_pure_helper_replays_duplicate_operand(self) -> None:
        source = ("use std@1;\n"
                  "fn square(v: [m31; 4]) -> [m31; 4] { v .* v }\n"
                  "circuit calc(public x: [m31; 4]) -> public [m31; 4] "
                  "{ let out = square(x); out }")
        relation, _ = compile_text(source)
        self.assertEqual(parse_source_fragment(source.encode()), relation)
        certificate = make_source_relation_certificate(source.encode(), encoded(relation))
        self.assertEqual(certificate["ssa"]["nodes"],
                         [{"id": 1, "name": "out", "op": "mul", "lhs": 0, "rhs": 0}])


    def test_package_artifact_admission_rejects_missing_and_resealed_claims(self) -> None:
        source = ("circuit bound(public x: [m31; 2]) -> public [m31; 2] "
                  "{ let squared = x .* x; squared }")
        source_bytes = source.encode()
        relation_bytes = encoded(compile_text(source)[0])
        certificate = make_source_relation_certificate(source_bytes, relation_bytes)
        with tempfile.TemporaryDirectory() as root:
            package = Path(root)
            (package / "source.s31").write_bytes(source_bytes)
            (package / "source.s31.json").write_bytes(relation_bytes)
            artifact = package / "source-relation-certificate.json"
            manifest = {"lowering": "direct-gate", "source_text_sha256": digest(source_bytes),
                        "artifacts": {}}
            with self.assertRaisesRegex(ValueError, "requires a source relation certificate"):
                verify_source_relation_artifact(package, manifest)
            artifact.write_bytes(encoded(certificate))
            manifest["artifacts"][artifact.name] = digest(artifact.read_bytes())
            verify_source_relation_artifact(package, manifest)
            oversized = b" " * (MAX_CERTIFICATE_BYTES + 1)
            artifact.write_bytes(oversized)
            manifest["artifacts"][artifact.name] = digest(oversized)
            with self.assertRaisesRegex(ValueError, "exceeds byte bound"):
                verify_source_relation_artifact(package, manifest)
            with self.assertRaisesRegex(ValueError, "exceeds byte bound"):
                check_source_relation_certificate(source_bytes, relation_bytes, oversized)
            artifact.write_bytes(encoded(certificate))
            manifest["artifacts"][artifact.name] = digest(artifact.read_bytes())
            manifest["lowering"] = "gate"
            verify_source_relation_artifact(package, manifest)
            manifest["lowering"] = "direct-gate"
            manifest["correspondence_schema"] = "s31-direct-gate-correspondence-v3"
            with self.assertRaisesRegex(ValueError, "requires conservative text source"):
                verify_source_relation_artifact(package, manifest)
            del manifest["correspondence_schema"]

            forged = copy.deepcopy(certificate)
            forged["ssa"]["nodes"][0]["rhs"] = 1
            artifact.write_bytes(encoded(forged))
            manifest["artifacts"][artifact.name] = digest(artifact.read_bytes())
            with self.assertRaisesRegex(ValueError, "certificate differs"):
                verify_source_relation_artifact(package, manifest)
            artifact.write_bytes(encoded(certificate))
            manifest["artifacts"][artifact.name] = "0" * 64
            with self.assertRaisesRegex(ValueError, "artifact hash differs"):
                verify_source_relation_artifact(package, manifest)

            # An unrecognized source cannot claim the checked fragment even
            # when its package manifest lists a self-consistent certificate.
            (package / "source.s31").write_bytes(b"use std; " + source_bytes)
            manifest["artifacts"][artifact.name] = digest(artifact.read_bytes())
            with self.assertRaisesRegex(ValueError, "unsupported source carries"):
                verify_source_relation_artifact(package, manifest)
            artifact.unlink()
            del manifest["artifacts"][artifact.name]
            verify_source_relation_artifact(package, manifest)

    def test_emitted_indexed_ssa_is_source_bound_and_honest_about_scope(self) -> None:
        pure = ("fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }\n"
                "circuit calc(private a: [m31; 5], private b: [m31; 5]) "
                "-> public [m31; 5] { let delta = difference(a, b); "
                "let doubled = delta + delta; doubled }")
        relation, _ = compile_text(pure)
        source_bytes, relation_bytes = pure.encode(), encoded(relation)
        certificate = make_source_relation_certificate(source_bytes, relation_bytes)
        self.assertEqual(certificate["schema"], CERTIFICATE_SCHEMA)
        self.assertEqual(certificate["lean_semantic_profile"], LEAN_SEMANTIC_PROFILE)
        self.assertEqual(certificate["unmodeled_features"], [])
        self.assertEqual(certificate["ssa"], {
            "lane_count": 5,
            "inputs": [{"id": 0, "name": "a", "visibility": "private"},
                       {"id": 1, "name": "b", "visibility": "private"}],
            "nodes": [{"id": 2, "name": "delta", "op": "sub", "lhs": 0, "rhs": 1},
                      {"id": 3, "name": "doubled", "op": "add", "lhs": 2, "rhs": 2}],
            "assertions": [], "output": 3,
        })
        self.assertEqual(check_source_relation_certificate(
            source_bytes, relation_bytes, encoded(certificate)), certificate)

        # A matching digest and valid JSON shape do not rescue changed SSA.
        forged = copy.deepcopy(certificate)
        forged["ssa"]["nodes"][0]["op"] = "add"
        with self.assertRaisesRegex(ValueError, "certificate differs"):
            check_source_relation_certificate(source_bytes, relation_bytes, encoded(forged))
        forged = copy.deepcopy(certificate)
        forged["lean_semantic_profile"] = None
        with self.assertRaisesRegex(ValueError, "certificate differs"):
            check_source_relation_certificate(source_bytes, relation_bytes, encoded(forged))
        for field, changed in (("lane_count", 4), ("output", 2)):
            with self.subTest(field=field):
                forged = copy.deepcopy(certificate)
                forged["ssa"][field] = changed
                with self.assertRaisesRegex(ValueError, "certificate differs"):
                    check_source_relation_certificate(source_bytes, relation_bytes,
                                                      encoded(forged))
        with self.assertRaisesRegex(ValueError, "relation differs"):
            check_source_relation_certificate(source_bytes, encoded({**relation, "nodes": []}),
                                              encoded(certificate))

        richer_relation, _ = compile_text(SOURCE)
        richer = make_source_relation_certificate(SOURCE.encode(), encoded(richer_relation))
        self.assertEqual(richer["lean_semantic_profile"], LEAN_EFFECTS_PROFILE)
        self.assertEqual(richer["unmodeled_features"], [])
        self.assertEqual(len(richer["ssa"]["assertions"]), 1)
        self.assertEqual(richer["ssa"]["nodes"][2]["constant"], 7)

    def test_effectful_profile_records_constant_and_assertion_semantics(self) -> None:
        cases = [
            ("let out = x + splat<2>(7_m31); out", "add_const", 7, []),
            ("let out = x .* splat<2>(9_m31); out", "mul_const", 9, []),
            ("let out = x - x; assert_eq(out, x); out", "sub", None, [[1, 0]]),
            ("let out = x - splat<2>(7_m31); assert_eq(out, x); out",
             "add_const", 2147483640, [[1, 0]]),
        ]
        for body, op, constant, assertions in cases:
            with self.subTest(body=body):
                source = ("circuit calc(private x: [m31; 2]) -> public [m31; 2] "
                          "{ " + body + " }")
                relation, _ = compile_text(source)
                cert = make_source_relation_certificate(source.encode(), encoded(relation))
                self.assertEqual(cert["lean_semantic_profile"], LEAN_EFFECTS_PROFILE)
                self.assertEqual(cert["unmodeled_features"], [])
                self.assertEqual(cert["ssa"]["nodes"][0]["op"], op)
                self.assertEqual(cert["ssa"]["assertions"], assertions)
                if constant is not None:
                    self.assertEqual(cert["ssa"]["nodes"][0]["constant"], constant)
                self.assertEqual(check_source_relation_certificate(
                    source.encode(), encoded(relation), encoded(cert)), cert)
                for mutate in (lambda forged: forged["ssa"]["nodes"][0].update(op="add"),
                               lambda forged: forged.update(lean_semantic_profile=LEAN_SEMANTIC_PROFILE),
                               lambda forged: forged["ssa"].update(assertions=[])):
                    forged = copy.deepcopy(cert)
                    mutate(forged)
                    if forged != cert:
                        with self.assertRaisesRegex(ValueError, "certificate differs"):
                            check_source_relation_certificate(
                                source.encode(), encoded(relation), encoded(forged))

    def test_lean_subtraction_fixture_matches_native_acceptance_source(self) -> None:
        formal = S31.parents[2] / "formal/s31/S31/Gadgets/Functional/Correspondence/SourceFunctionBytes.lean"
        source = formal.read_text()
        definition = re.search(r"def subtract5Source : String :=\s*(.*?)\s*def subtract5Parsed",
                               source, re.DOTALL)
        self.assertIsNotNone(definition)
        lean_literals = re.findall(r'"(?:[^"\\]|\\.)*"', definition.group(1))
        self.assertEqual("".join(ast.literal_eval(value) for value in lean_literals), SUB5_FUNCTIONAL)
        native = (S31 / "tests/acceptance/math/field_subtraction_partial.py").read_text()
        acceptance_literal = re.search(r'FUNCTIONAL_SOURCE = (""".*?""")', native, re.DOTALL)
        self.assertIsNotNone(acceptance_literal)
        self.assertEqual(ast.literal_eval(acceptance_literal.group(1)), SUB5_FUNCTIONAL)

    def test_independent_function_erasure_and_short_packed_subtraction(self) -> None:
        for length in (1, 2, 3, 4, 5, 7, 8):
            with self.subTest(length=length):
                header = (f"circuit subtract(private a: [m31; {length}], "
                          f"private b: [m31; {length}]) -> public [m31; {length}] {{")
                direct = header + " let out = a - b; out }"
                function = (f"fn difference(x: [m31; {length}], y: [m31; {length}]) "
                            f"-> [m31; {length}] {{ x - y }}\n" +
                            header + " let out = difference(a, b); out }")
                for source in (direct, function):
                    expected = parse_source_fragment(source.encode())
                    actual, _ = compile_text(source)
                    self.assertEqual(expected, actual)
                    self.assertEqual(expected["nodes"],
                                     [{"name": "out", "lhs": "a", "op": "sub", "rhs": "b"}])
                    self.assertEqual(check_source_relation(source.encode(), encoded(actual))["capability"],
                                     CAPABILITY)

    def test_noncommutative_function_order_and_resealed_relation_forgery(self) -> None:
        source = SUB5_FUNCTIONAL.replace("x - y", "y - x")
        relation, _ = compile_text(source)
        self.assertEqual(parse_source_fragment(source.encode()), relation)
        self.assertEqual(relation["nodes"],
                         [{"name": "out", "lhs": "b", "op": "sub", "rhs": "a"}])
        forged = copy.deepcopy(relation)
        forged["nodes"][0]["op"] = "add"
        with self.assertRaisesRegex(ValueError, "relation differs"):
            check_source_relation(source.encode(), encoded(forged))
        with self.assertRaisesRegex(ValueError, "relation differs"):
            check_source_relation(SUB5_FUNCTIONAL.encode(), encoded(relation))

    def test_pure_helper_add_and_multiply_lower_to_one_node(self) -> None:
        for token, operation in (("+", "add"), (".*", "mul")):
            with self.subTest(operation=operation):
                source = (
                    f"fn combine(x: [m31; 3], y: [m31; 3]) -> [m31; 3] {{ x {token} y }}\n"
                    "circuit calc(private a: [m31; 3], private b: [m31; 3]) "
                    "-> public [m31; 3] { let out = combine(a, b); out }"
                )
                expected = parse_source_fragment(source.encode())
                actual, _ = compile_text(source)
                self.assertEqual(expected, actual)
                self.assertEqual(expected["nodes"],
                                 [{"name": "out", "lhs": "a", "op": operation, "rhs": "b"}])

    def test_five_lane_functional_package_abi_reseal_rejected(self) -> None:
        source_bytes = SUB5_FUNCTIONAL.encode()
        relation_bytes = encoded(compile_text(SUB5_FUNCTIONAL)[0])
        abi = {"schema": "s31-public-abi-v1",
               "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
               "public_inputs": [],
               "public_outputs": [{"name": "out", "kind": "m31", "length": 5}]}
        with tempfile.TemporaryDirectory() as root:
            package = Path(root)
            (package / "source.s31").write_bytes(source_bytes)
            (package / "source.s31.json").write_bytes(relation_bytes)

            def reseal(output_abi: dict) -> None:
                abi_bytes = encoded(output_abi)
                (package / "public-abi.json").write_bytes(abi_bytes)
                manifest = {
                    "schema": "s31-package-v1", "name": "subtract5",
                    "lowering": "direct-gate", "source_text_sha256": digest(source_bytes),
                    "program_sha256": digest(relation_bytes),
                    "artifacts": {
                        "source.s31": digest(source_bytes),
                        "source.s31.json": digest(relation_bytes),
                        "public-abi.json": digest(abi_bytes),
                    },
                }
                (package / "manifest.json").write_bytes(encoded(manifest))

            reseal(abi)
            self.assertEqual(check_package_source_relation(package)["capability"], CAPABILITY)
            forged = copy.deepcopy(abi)
            forged["public_outputs"][0]["length"] = 4
            reseal(forged)
            with self.assertRaisesRegex(ValueError, "public ABI differs"):
                check_package_source_relation(package)

    def test_subtraction_constant_and_function_fragment_rejections(self) -> None:
        source = SUB5_FUNCTIONAL
        bad_sources = [
            source.replace("x - y", "x + y + x"),
            source.replace("x - y", "splat<5>(1_m31) - y"),
            source.replace("fn difference(x:", "fn difference(y:"),
            source.replace("fn difference(x:", "fn difference(difference:"),
            source.replace("fn difference(x:", "fn difference(x: [m31; 4], unused:"),
            source.replace("let out = difference(a, b);", "let out = a - b;"),
            source.replace("let out = difference(a, b);", "let difference = a; let out = difference(a, b);"),
            source.replace("private b: [m31; 5]", "private b: [m31; 4]"),
            source.replace("-> public [m31; 5]", "-> public [m31; 4]"),
            source.replace("[m31; 5] { x - y }", "[m31; 6] { x - y }"),
            source.replace("[m31; 5] { x - y }", "[m31; 05] { x - y }"),
            source.replace("let out = difference(a, b);", "let out = splat<5>(7_m31) - b;"),
        ]
        for bad in bad_sources:
            with self.subTest(source=bad[:100]), self.assertRaises(UnsupportedSourceRelationFragment):
                parse_source_fragment(bad.encode())

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
