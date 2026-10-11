"""Adversarial checks for the versioned public-record boundary."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import (binding_digest, decode_public_statement,
                            decode_typed_public_statement, encode_typed_public_statement,
                            flat_assignment_from_typed, statement_from_assignment,
                            encode_public_statement, make_binding, validate_binding)
from abi.record_v2 import AbiError
from language.syntax import RecordType, TupleType
from s31_stdlib import Type


class RecordBindingV2Tests(unittest.TestCase):
    def setUp(self) -> None:
        field = Type("m31", 1)
        self.request = RecordType("Request", (("first", field), ("second", field)))
        self.response = RecordType("Response", (("sum", field),
                                                 ("copy", TupleType((field, field)))))
        self.relation = {
            "version": 1, "name": "binding_probe",
            "inputs": [
                {"name": "a", "kind": "m31", "length": 1, "visibility": "public"},
                {"name": "b", "kind": "m31", "length": 1, "visibility": "public"},
                {"name": "secret", "kind": "m31", "length": 1, "visibility": "private"},
            ],
            "nodes": [{"name": "sum", "op": "add", "lhs": "a", "rhs": "secret"}],
            "assertions": [], "public_outputs": ["sum", "b"],
        }
        self.binding = make_binding(self.relation, [
            ("request", self.request, "public", ["a", "b"]),
            ("witness", field, "private", ["secret"]),
        ], ("result", self.response, ["sum", "b", "b"]))

    def test_nested_paths_aliases_and_zero_extra_proof_words(self) -> None:
        validate_binding(self.relation, self.binding)
        leaves = self.binding["result"]["leaves"]
        self.assertEqual([leaf["wire"] for leaf in leaves], ["sum", "b", "b"])
        self.assertEqual([leaf["path"] for leaf in leaves], [
            [{"root": "result"}, {"field": "sum"}],
            [{"root": "result"}, {"field": "copy"}, {"tuple": 0}],
            [{"root": "result"}, {"field": "copy"}, {"tuple": 1}],
        ])
        self.assertEqual(self.relation["public_outputs"], ["sum", "b"])
        self.assertEqual(len(self.relation["nodes"]), 1)

    def test_digest_binds_nominal_names_field_order_and_wire_aliases(self) -> None:
        baseline = binding_digest(self.relation, self.binding)
        changed_type = RecordType("OtherResponse", self.response.fields)
        changed = make_binding(self.relation, [
            ("request", self.request, "public", ["a", "b"]),
            ("witness", Type("m31", 1), "private", ["secret"]),
        ], ("result", changed_type, ["sum", "b", "b"]))
        self.assertNotEqual(baseline, binding_digest(self.relation, changed))
        swapped = copy.deepcopy(self.binding)
        swapped["result"]["type"]["fields"][0], swapped["result"]["type"]["fields"][1] = (
            swapped["result"]["type"]["fields"][1], swapped["result"]["type"]["fields"][0])
        with self.assertRaisesRegex(AbiError, "path or shape"):
            binding_digest(self.relation, swapped)

    def test_changed_visibility_wire_shape_or_relation_output_order_reject(self) -> None:
        variants = []
        visibility = copy.deepcopy(self.binding)
        visibility["inputs"][1]["visibility"] = "public"
        variants.append(visibility)
        unknown = copy.deepcopy(self.binding)
        unknown["result"]["leaves"][0]["wire"] = "absent"
        variants.append(unknown)
        wrong_shape = copy.deepcopy(self.binding)
        wrong_shape["result"]["leaves"][0]["length"] = 2
        variants.append(wrong_shape)
        wrong_order = copy.deepcopy(self.binding)
        wrong_order["result"]["leaves"][0]["wire"] = "b"
        wrong_order["result"]["leaves"][1]["wire"] = "sum"
        variants.append(wrong_order)
        for variant in variants:
            with self.subTest(variant=variant), self.assertRaises(AbiError):
                validate_binding(self.relation, variant)

    def test_missing_duplicate_reordered_or_extra_paths_reject(self) -> None:
        variants = []
        missing = copy.deepcopy(self.binding)
        missing["result"]["leaves"].pop()
        variants.append(missing)
        duplicated = copy.deepcopy(self.binding)
        duplicated["result"]["leaves"][1]["path"] = duplicated["result"]["leaves"][0]["path"]
        variants.append(duplicated)
        reordered = copy.deepcopy(self.binding)
        reordered["result"]["leaves"].reverse()
        variants.append(reordered)
        extra = copy.deepcopy(self.binding)
        extra["result"]["leaves"].append(copy.deepcopy(extra["result"]["leaves"][0]))
        variants.append(extra)
        for variant in variants:
            with self.subTest(variant=variant), self.assertRaises(AbiError):
                validate_binding(self.relation, variant)

    def test_result_root_matches_native_reserved_name(self) -> None:
        renamed = copy.deepcopy(self.binding)
        renamed["result"]["name"] = "claim"
        for leaf in renamed["result"]["leaves"]:
            leaf["path"][0] = {"root": "claim"}
        with self.assertRaisesRegex(AbiError, "output root must be result"):
            validate_binding(self.relation, renamed)

    def test_top_level_tuple_root_matches_native_profile(self) -> None:
        tupled = copy.deepcopy(self.binding)
        tupled["result"]["type"] = {"tuple": [copy.deepcopy(tupled["result"]["type"])]}
        for leaf in tupled["result"]["leaves"]:
            leaf["path"].insert(1, {"tuple": 0})
        with self.assertRaisesRegex(AbiError, "top-level ABI root"):
            validate_binding(self.relation, tupled)

    def test_input_coverage_and_alias_constraints(self) -> None:
        wrong_input = copy.deepcopy(self.binding)
        wrong_input["inputs"][0]["leaves"][1]["wire"] = "a"
        with self.assertRaisesRegex(AbiError, "exactly"):
            validate_binding(self.relation, wrong_input)
        wrong_output = copy.deepcopy(self.binding)
        wrong_output["result"]["leaves"][2]["wire"] = "sum"
        validate_binding(self.relation, wrong_output)
        self.assertNotEqual(binding_digest(self.relation, wrong_output),
                            binding_digest(self.relation, self.binding))

    def test_non_m31_leaf_rejected_until_native_range_checks_exist(self) -> None:
        for typ in (Type("u16", 1), Type("bit", 1), Type("int_u8", 1)):
            with self.subTest(typ=typ), self.assertRaisesRegex(AbiError, "only supports"):
                make_binding(self.relation, [
                    ("request", self.request, "public", ["a", "b"]),
                    ("witness", Type("m31", 1), "private", ["secret"]),
                ], ("result", typ, ["sum"]))

    def test_public_word_budget_counts_distinct_output_wires(self) -> None:
        source = copy.deepcopy(self.relation)
        source["inputs"][0]["length"] = 7
        source["public_outputs"] = ["a"]
        source["nodes"] = []
        # 7 + 1 + 7 = 15 words; the underlying relation validator rejects it.
        with self.assertRaises(AbiError):
            make_binding(source, [
                ("array", Type("m31", 7), "public", ["a"]),
                ("other", Type("m31", 1), "public", ["b"]),
                ("witness", Type("m31", 1), "private", ["secret"]),
            ], ("result", Type("m31", 7), ["a"]))

    def test_canonical_statement_projects_aliases_to_existing_proof_words(self) -> None:
        encoded = encode_public_statement(self.relation, self.binding,
                                          [[3], [5], [10], [5], [5]])
        self.assertEqual(decode_public_statement(self.relation, self.binding, encoded),
                         [3, 5, 10, 5, 0, 0, 0, 0])
        self.assertEqual(encoded, encode_public_statement(self.relation, self.binding,
                                                          [[3], [5], [10], [5], [5]]))

    def test_statement_rejects_disagreeing_alias_wrong_digest_and_bad_words(self) -> None:
        for words in ([[3], [5], [10], [5], [6]],
                      [[3], [5], [10], [2**31 - 1], [5]],
                      [[True], [5], [10], [5], [5]]):
            with self.subTest(words=words), self.assertRaises(AbiError):
                encode_public_statement(self.relation, self.binding, words)
        encoded = encode_public_statement(self.relation, self.binding,
                                          [[3], [5], [10], [5], [5]])
        statement = json.loads(encoded)
        statement["abi_sha256"] = "0" * 64
        with self.assertRaisesRegex(AbiError, "digest"):
            decode_public_statement(self.relation, self.binding,
                                    (json.dumps(statement, sort_keys=True,
                                                separators=(",", ":")) + "\n").encode())

    def test_statement_rejects_path_swap_bool_tuple_index_and_duplicate_json_key(self) -> None:
        encoded = encode_public_statement(self.relation, self.binding,
                                          [[3], [5], [10], [5], [5]])
        statement = json.loads(encoded)
        statement["leaves"][3]["path"], statement["leaves"][4]["path"] = (
            statement["leaves"][4]["path"], statement["leaves"][3]["path"])
        with self.assertRaisesRegex(AbiError, "path"):
            decode_public_statement(self.relation, self.binding,
                                    (json.dumps(statement, sort_keys=True,
                                                separators=(",", ":")) + "\n").encode())
        statement = json.loads(encoded)
        statement["leaves"][4]["path"][-1] = {"tuple": True}
        with self.assertRaisesRegex(AbiError, "path"):
            decode_public_statement(self.relation, self.binding,
                                    (json.dumps(statement, sort_keys=True,
                                                separators=(",", ":")) + "\n").encode())
        with self.assertRaisesRegex(AbiError, "duplicate"):
            decode_public_statement(self.relation, self.binding,
                                    encoded.replace(b'"version":2',
                                                    b'"version":2,"version":2'))
        with self.assertRaisesRegex(AbiError, "noncanonical"):
            decode_public_statement(self.relation, self.binding, encoded[:-1])

    def test_typed_record_assignment_lowers_to_exact_native_wires(self) -> None:
        source = {**self.relation, "version": 2, "public_abi": self.binding}
        typed = {"version": 2,
                 "public_inputs": {"request": {"first": [3], "second": [5]}},
                 "private_inputs": {"witness": [7]},
                 "result": {"sum": [10], "copy": [[5], [5]]}}
        encoded = json.dumps(typed).encode()
        flat = flat_assignment_from_typed(source, encoded)
        self.assertEqual(flat, {"public_inputs": {"a": [3], "b": [5]},
                                "private_inputs": {"secret": [7]},
                                "public_outputs": {"sum": [10], "b": [5]}})
        statement = statement_from_assignment(source, flat)
        self.assertEqual(decode_public_statement(self.relation, self.binding, statement),
                         [3, 5, 10, 5, 0, 0, 0, 0])
        wrong_alias = copy.deepcopy(typed)
        wrong_alias["result"]["copy"][1] = [6]
        missing_field = copy.deepcopy(typed)
        del missing_field["public_inputs"]["request"]["second"]
        private_as_public = copy.deepcopy(typed)
        private_as_public["public_inputs"]["witness"] = [7]
        noncanonical = copy.deepcopy(typed)
        noncanonical["private_inputs"]["witness"] = [2**31 - 1]
        for variant in (wrong_alias, missing_field, private_as_public, noncanonical):
            with self.subTest(variant=variant), self.assertRaises(AbiError):
                flat_assignment_from_typed(source, json.dumps(variant).encode())
        with self.assertRaisesRegex(AbiError, "duplicate"):
            flat_assignment_from_typed(source,
                encoded.replace(b'"version": 2', b'"version": 2, "version": 2'))

    def test_typed_public_claim_round_trips_exact_statement_bytes(self) -> None:
        source = {**self.relation, "version": 2, "public_abi": self.binding}
        statement = encode_public_statement(self.relation, self.binding,
                                            [[3], [5], [10], [5], [5]])
        claim = decode_typed_public_statement(source, statement)
        self.assertEqual(claim, {
            "version": 2, "abi_sha256": binding_digest(self.relation, self.binding),
            "public_inputs": {"request": {"first": [3], "second": [5]}},
            "result": {"sum": [10], "copy": [[5], [5]]},
        })
        self.assertNotIn("witness", claim["public_inputs"])
        self.assertEqual(encode_typed_public_statement(source, claim), statement)

    def test_typed_public_claim_rejects_private_root_alias_and_bad_shape(self) -> None:
        source = {**self.relation, "version": 2, "public_abi": self.binding}
        statement = encode_public_statement(self.relation, self.binding,
                                            [[3], [5], [10], [5], [5]])
        claim = decode_typed_public_statement(source, statement)
        variants = []
        private = copy.deepcopy(claim)
        private["public_inputs"]["witness"] = [7]
        variants.append(private)
        alias = copy.deepcopy(claim)
        alias["result"]["copy"][1] = [6]
        variants.append(alias)
        wrong_digest = copy.deepcopy(claim)
        wrong_digest["abi_sha256"] = "0" * 64
        variants.append(wrong_digest)
        wrong_tuple = copy.deepcopy(claim)
        wrong_tuple["result"]["copy"] = [[5]]
        variants.append(wrong_tuple)
        bad_word = copy.deepcopy(claim)
        bad_word["public_inputs"]["request"]["first"] = [2**31 - 1]
        variants.append(bad_word)
        for variant in variants:
            with self.subTest(variant=variant), self.assertRaises(AbiError):
                encode_typed_public_statement(source, variant)
        with self.assertRaisesRegex(AbiError, "noncanonical"):
            decode_typed_public_statement(source, statement[:-1])
        with self.assertRaisesRegex(AbiError, "digest"):
            decode_typed_public_statement(
                source, statement.replace(claim["abi_sha256"].encode(), b"0" * 64))


if __name__ == "__main__":
    unittest.main()
