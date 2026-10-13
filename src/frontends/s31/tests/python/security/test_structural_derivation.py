"""Resealed source-erasure forgeries and a shared typed projection rule."""

from __future__ import annotations

import copy
import hashlib
import json
import unittest

from package.context import abi
from package.source_relation_fragment import (UnsupportedSourceRelationFragment,
                                              parse_source_fragment)
from package.structural_derivation import (UnsupportedStructuralDerivation,
                                           check_certificate, derive_relation,
                                           evaluate_assignment, make_certificate)
from text_frontend import compile_text

TUPLE = """circuit paired(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let p = (x, y);
    let z = p.0 - p.1;
    z
}
"""
HELPER = """fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
circuit paired(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let z = subtract(x, y);
    z
}
"""
COMBINED = """fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
circuit paired(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let p = (x, y);
    let a = p.0;
    let b = p.1;
    let z = subtract(a, b);
    z
}
"""
RECORD = """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit paired(public x: Pair, private y: Pair) -> public Pair {
    let z = x.left .* y.right;
    Pair { right: x.right, left: z }
}
"""
EFFECTFUL = """circuit constrained(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let z = x + splat<2>(7_m31);
    assert_eq(z, y);
    z
}
"""


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def fixture(source: str) -> tuple[dict, bytes, bytes, bytes]:
    relation, _ = compile_text(source)
    relation_bytes = encoded(relation)
    abi_bytes = encoded(abi(relation, "direct-gate"))
    certificate = make_certificate(source.encode(), relation_bytes, abi_bytes, "direct-gate")
    check_certificate(source.encode(), relation_bytes, abi_bytes,
                      "direct-gate", encoded(certificate))
    return certificate, source.encode(), relation_bytes, abi_bytes


class StructuralDerivationTests(unittest.TestCase):
    def test_tuple_helper_and_combined_erasure(self) -> None:
        expected = None
        for source in (TUPLE, HELPER, COMBINED):
            certificate, data, relation_bytes, abi_bytes = fixture(source)
            if expected is None:
                expected = relation_bytes
            self.assertEqual(expected, relation_bytes)
            assignment = encoded({
                "public_inputs": {"x": [7, 11], "y": [3, 5]},
                "private_inputs": {}, "public_outputs": {"z": [4, 6]},
            })
            self.assertEqual(evaluate_assignment(certificate, assignment)["public_words"],
                             [7, 11, 3, 5, 4, 6, 0, 0])
            self.assertEqual(certificate["source_sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual(certificate["public_abi_sha256"],
                             hashlib.sha256(abi_bytes).hexdigest())
        with self.assertRaises(UnsupportedSourceRelationFragment):
            parse_source_fragment(COMBINED.encode())

    def test_record_field_projection_and_declared_output_order(self) -> None:
        certificate, _, relation_bytes, _ = fixture(RECORD)
        relation = json.loads(relation_bytes)
        self.assertEqual(relation["public_outputs"], ["z", "_s31_abi_input_1"])
        self.assertEqual([leaf["path"][-1]["field"] for leaf in
                          relation["public_abi"]["result"]["leaves"]], ["left", "right"])
        assignment = encoded({
            "public_inputs": {"_s31_abi_input_0": [2], "_s31_abi_input_1": [3]},
            "private_inputs": {"_s31_abi_input_2": [5], "_s31_abi_input_3": [7]},
            "public_outputs": {"z": [14], "_s31_abi_input_1": [3]},
        })
        self.assertEqual(evaluate_assignment(certificate, assignment)["public_words"],
                         [2, 3, 14, 3, 0, 0, 0, 0])
        changed = json.loads(assignment)
        changed["public_outputs"]["z"] = [15]
        with self.assertRaisesRegex(ValueError, "claimed public result"):
            evaluate_assignment(certificate, encoded(changed))

    def test_effectful_constant_and_assertion_replay(self) -> None:
        certificate, _, relation_bytes, _ = fixture(EFFECTFUL)
        relation = json.loads(relation_bytes)
        self.assertEqual(relation["nodes"], [{"name": "z", "lhs": "x",
                                              "op": "add_const", "constant": 7}])
        self.assertEqual(relation["assertions"], [{"lhs": "z", "rhs": "y"}])
        assignment = {"public_inputs": {"x": [1, 2]},
                      "private_inputs": {"y": [8, 9]},
                      "public_outputs": {"z": [8, 9]}}
        self.assertEqual(evaluate_assignment(certificate, encoded(assignment))["public_words"],
                         [1, 2, 8, 9, 0, 0, 0, 0])
        assignment["private_inputs"]["y"] = [8, 10]
        with self.assertRaisesRegex(ValueError, "source assertion is false"):
            evaluate_assignment(certificate, encoded(assignment))

    def test_resealed_wrong_tuple_projection_rejected(self) -> None:
        certificate, source, _, _ = fixture(TUPLE)
        forged = copy.deepcopy(certificate)
        forged["program"]["steps"][1]["expr"]["lhs"]["field"] = "1"
        relation = derive_relation(forged["program"])
        relation_bytes = encoded(relation)
        abi_bytes = encoded(abi(relation, "direct-gate"))
        forged["relation_sha256"] = hashlib.sha256(relation_bytes).hexdigest()
        forged["public_abi_sha256"] = hashlib.sha256(abi_bytes).hexdigest()
        with self.assertRaisesRegex(ValueError, "differs from source relation"):
            check_certificate(source, relation_bytes, abi_bytes, "direct-gate",
                              encoded(forged))

    def test_resealed_wrong_helper_body_rejected(self) -> None:
        certificate, source, _, _ = fixture(HELPER)
        forged = copy.deepcopy(certificate)
        forged["program"]["helpers"][0]["body"]["lhs"]["name"] = "b"
        forged["program"]["helpers"][0]["body"]["rhs"]["name"] = "a"
        relation = derive_relation(forged["program"])
        relation_bytes = encoded(relation)
        abi_bytes = encoded(abi(relation, "direct-gate"))
        forged["relation_sha256"] = hashlib.sha256(relation_bytes).hexdigest()
        forged["public_abi_sha256"] = hashlib.sha256(abi_bytes).hexdigest()
        with self.assertRaisesRegex(ValueError, "differs from source relation"):
            check_certificate(source, relation_bytes, abi_bytes, "direct-gate",
                              encoded(forged))

    def test_resealed_wrong_record_field_rejected(self) -> None:
        certificate, source, _, _ = fixture(RECORD)
        forged = copy.deepcopy(certificate)
        forged["program"]["steps"][0]["expr"]["lhs"]["field"] = "right"
        relation = derive_relation(forged["program"])
        relation_bytes = encoded(relation)
        abi_bytes = encoded(abi(relation, "direct-gate"))
        forged["relation_sha256"] = hashlib.sha256(relation_bytes).hexdigest()
        forged["public_abi_sha256"] = hashlib.sha256(abi_bytes).hexdigest()
        with self.assertRaisesRegex(ValueError, "differs from source relation"):
            check_certificate(source, relation_bytes, abi_bytes, "direct-gate",
                              encoded(forged))

    def test_unsupported_source_and_noncanonical_assignment_rejected(self) -> None:
        with self.assertRaises(UnsupportedStructuralDerivation):
            make_certificate(b"circuit c() -> public [m31; 1] { if true { 1 } else { 2 } }",
                             b"{}\n", b"{}\n", "direct-gate")
        certificate, _, _, _ = fixture(TUPLE)
        assignment = b'{"public_inputs":{"x":[7,11],"x":[7,11],"y":[3,5]},"private_inputs":{},"public_outputs":{"z":[4,6]}}'
        with self.assertRaisesRegex(ValueError, "duplicate structural assignment key"):
            evaluate_assignment(certificate, assignment)
        bad_bool = encoded({"public_inputs": {"x": [True, 11], "y": [3, 5]},
                            "private_inputs": {}, "public_outputs": {"z": [4, 6]}})
        with self.assertRaisesRegex(ValueError, "noncanonical structural M31 input"):
            evaluate_assignment(certificate, bad_bool)


if __name__ == "__main__":
    unittest.main()
