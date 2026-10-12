"""Adversarial bounded source-to-public-statement projection differential."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/acceptance/record_abi"))

from abi.binding_v2 import decode_public_statement  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from package.record_source_fragment import parse_record_source_fragment  # noqa: E402
from independent_statement_fragment_v2 import (  # noqa: E402
    CAPABILITY, InvalidRecordStatementFragment, check_record_source_statement,
)
from text_frontend import compile_text  # noqa: E402

SOURCE = b"""struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def relation_binding(source: bytes) -> tuple[dict, dict]:
    checked = parse_record_source_fragment(source)
    compiled, _ = compile_text(source.decode())
    if checked != compiled:
        raise AssertionError("independent source parser differs from production compiler")
    relation = {**checked, "version": 1}
    binding = relation.pop("public_abi")
    return relation, binding


def statement_for(binding: dict, values: dict[str, int]) -> dict:
    declared = [leaf for root in binding["inputs"] if root["visibility"] == "public"
                for leaf in root["leaves"]] + binding["result"]["leaves"]
    from independent_statement_fragment_v2 import ABI_DOMAIN  # noqa: PLC0415
    import hashlib  # noqa: PLC0415
    digest = hashlib.sha256(ABI_DOMAIN + canonical(binding)).hexdigest()
    return {"version": 2, "abi_sha256": digest,
            "leaves": [{"path": leaf["path"], "words": [values[leaf["wire"]]]}
                       for leaf in declared]}


class RecordStatementFragmentTests(unittest.TestCase):
    def test_handwritten_statement_and_valid_changed_claims(self) -> None:
        relation, binding = relation_binding(SOURCE)
        claim = statement_for(binding, {"_s31_abi_input_0": 2,
                                        "_s31_abi_input_1": 3, "q": 17})
        honest = canonical(claim)
        report = check_record_source_statement(SOURCE, honest)
        self.assertEqual(report["capability"], CAPABILITY)
        self.assertEqual(report["proof_words"], [2, 3, 17, 3, 0, 0, 0, 0])
        self.assertEqual(decode_public_statement(relation, binding, honest),
                         report["proof_words"])
        for index, word, expected in ((0, 9, [9, 3, 17, 3, 0, 0, 0, 0]),
                                      (2, 18, [2, 3, 18, 3, 0, 0, 0, 0])):
            with self.subTest(changed_leaf=index):
                changed = copy.deepcopy(claim)
                changed["leaves"][index]["words"] = [word]
                encoded = canonical(changed)
                self.assertEqual(check_record_source_statement(SOURCE, encoded)["proof_words"],
                                 expected)
                self.assertEqual(decode_public_statement(relation, binding, encoded), expected)

    def test_bounded_layout_and_alias_corpus(self) -> None:
        accepted = 0
        for fields in range(1, 5):
            for visibilities in (("public",), ("public", "private"),
                                 ("private", "public"), ("public", "public")):
                if fields * visibilities.count("public") + 1 > 8:
                    continue
                for arithmetic in (False, True):
                    names = [f"f{index}" for index in range(fields)]
                    roots = ("x", "y")[:len(visibilities)]
                    inputs = ", ".join(f"{vis} {root}: Rec"
                                       for vis, root in zip(visibilities, roots))
                    left, right = f"{roots[0]}.f0", f"{roots[-1]}.f0"
                    prelude = f"let t = {left} + {right};\n    " if arithmetic else ""
                    constructor = ", ".join(
                        f"{name}: {'t' if arithmetic and index == 0 else left}"
                        for index, name in enumerate(names))
                    source = (f"struct Rec {{ {', '.join(f'{name}: [m31; 1]' for name in names)} }}\n"
                              f"circuit run({inputs}) -> public Rec {{\n"
                              f"    {prelude}Rec {{ {constructor} }}\n}}\n").encode()
                    relation, binding = relation_binding(source)
                    declared = [leaf for root in binding["inputs"]
                                if root["visibility"] == "public" for leaf in root["leaves"]]
                    declared += binding["result"]["leaves"]
                    values = {leaf["wire"]: index + 11 for index, leaf in enumerate(declared)}
                    statement = canonical(statement_for(binding, values))
                    independent = check_record_source_statement(source, statement)["proof_words"]
                    self.assertEqual(independent,
                                     decode_public_statement(relation, binding, statement))
                    accepted += 1
        self.assertEqual(accepted, 30)

    def test_malformed_bytes_and_source_rebinding_fail_closed(self) -> None:
        relation, binding = relation_binding(SOURCE)
        honest = statement_for(binding, {"_s31_abi_input_0": 2,
                                         "_s31_abi_input_1": 3, "q": 17})
        variants: dict[str, bytes] = {}

        def edit(label: str, path: tuple[str | int, ...], value: object) -> None:
            changed = copy.deepcopy(honest)
            node = changed
            for part in path[:-1]:
                node = node[part]
            node[path[-1]] = value
            variants[label] = canonical(changed)

        edit("bool_version", ("version",), True)
        edit("float_version", ("version",), 2.0)
        edit("wrong_digest", ("abi_sha256",), "0" * 64)
        edit("numeric_digest", ("abi_sha256",), 5)
        edit("wrong_root", ("leaves", 0, "path", 0, "root"), "y")
        edit("wrong_field", ("leaves", 2, "path", 1, "field"), "right")
        edit("split_alias", ("leaves", 3, "words"), [4])
        for label, word in (("negative_word", -1), ("modulus_word", 2**31 - 1),
                            ("bool_word", True), ("float_word", 2.0),
                            ("string_word", "2")):
            edit(label, ("leaves", 0, "words", 0), word)
        edit("short_words", ("leaves", 0, "words"), [])
        edit("long_words", ("leaves", 0, "words"), [2, 2])
        edit("wrong_path_shape", ("leaves", 0, "path"), [{"root": "x"}, "left"])
        changed = copy.deepcopy(honest)
        changed["leaves"].pop()
        variants["missing_leaf"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"].append(copy.deepcopy(changed["leaves"][0]))
        variants["extra_leaf"] = canonical(changed)
        encoded = canonical(honest)
        variants.update({
            "missing_newline": encoded[:-1],
            "extra_newline": encoded + b"\n",
            "leading_space": b" " + encoded,
            "duplicate_version": encoded.replace(b'"version":2', b'"version":2,"version":2'),
            "nan_word": encoded.replace(b'"words":[2]', b'"words":[NaN]', 1),
            "escaped_path": encoded.replace(b'"root":"x"', b'"root":"\\u0078"', 1),
            "too_large": encoded + b" " * (1_000_001 - len(encoded)),
        })
        for label, malformed in variants.items():
            with self.subTest(mutation=label):
                self.assertNotEqual(malformed, encoded)
                with self.assertRaises(InvalidRecordStatementFragment):
                    check_record_source_statement(SOURCE, malformed)
                with self.assertRaises(AbiError):
                    decode_public_statement(relation, binding, malformed)
        changed_source = SOURCE.replace(b"left: [m31; 1], right: [m31; 1]",
                                        b"right: [m31; 1], left: [m31; 1]")
        with self.assertRaisesRegex(InvalidRecordStatementFragment, "ABI digest"):
            check_record_source_statement(changed_source, encoded)


if __name__ == "__main__":
    unittest.main()
