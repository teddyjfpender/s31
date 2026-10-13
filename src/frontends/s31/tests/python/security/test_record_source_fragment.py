"""Independent bounded v2 record source/ABI checks and re-sealed forgeries."""

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

from package.context import abi  # noqa: E402
from package.record_source_fragment import (  # noqa: E402
    CAPABILITY, UnsupportedRecordSourceFragment, check_package_record_source_relation,
    RESERVED_RECORD_TYPES, check_record_source_relation, expected_public_abi,
    parse_record_source_fragment,
)
from package.correspondence import (  # noqa: E402
    MAX_RELATION_NAME_CHARS, PLAIN_BUILTIN_NAMES, SOURCE_KEYWORDS,
)
from text_frontend import compile_text  # noqa: E402

SOURCE = """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""
PATTERN_SOURCE = """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let Pair { right: saved, left } = x;
    let Pair { right: secret } = y;
    let p = left .* secret;
    let q = p + saved;
    Pair { right: saved, left: q }
}
"""


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class RecordSourceFragmentTests(unittest.TestCase):
    def test_lean_byte_parser_identifier_inventory_matches_checker(self) -> None:
        lean = (S31.parents[2] / "formal/s31/S31/Gadgets/Records/SourceBytesV2.lean").read_text()

        def inventory(definition: str) -> set[str]:
            match = re.search(
                rf"private def {definition} .*?\(\[(.*?)\]\.map token\) name",
                lean, re.S,
            )
            self.assertIsNotNone(match, definition)
            return set(ast.literal_eval("[" + match.group(1) + "]"))

        self.assertEqual(inventory("reservedName"),
                         SOURCE_KEYWORDS | PLAIN_BUILTIN_NAMES)
        self.assertEqual(inventory("reservedRecordType"), RESERVED_RECORD_TYPES)
        self.assertIn(f"name.length ≤ {MAX_RELATION_NAME_CHARS}", lean)

        for length, accepted in ((128, True), (129, False)):
            field = "a" * length
            source = (f"struct Pair {{ {field}: [m31; 1] }} "
                      f"circuit copy(public x: Pair) -> public Pair {{ "
                      f"Pair {{ {field}: x.{field} }} }}")
            with self.subTest(length=length):
                if accepted:
                    self.assertEqual(parse_record_source_fragment(source.encode()),
                                     compile_text(source)[0])
                else:
                    with self.assertRaises(UnsupportedRecordSourceFragment):
                        parse_record_source_fragment(source.encode())
                    with self.assertRaises(Exception):
                        compile_text(source)

    def test_honest_source_matches_compiler_and_abi(self) -> None:
        variants = [
            SOURCE,
            PATTERN_SOURCE,
            """// no arithmetic: record fields are aliases
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit echo(public x: Pair) -> public Pair {
    Pair { left: x.left, right: x.right }
}""",
            """struct Pair { right: [m31; 1], left: [m31; 1] }
circuit order(public x: Pair) -> public Pair {
    let sum = x.left + x.right;
    Pair { left: sum, right: sum }
}""",
            """struct Quad { a: [m31; 1], b: [m31; 1], c: [m31; 1], d: [m31; 1] }
circuit edge(public x: Quad) -> public Quad {
    let p = x.a .* x.b;
    let q = p + x.c;
    Quad { a: q, b: x.b, c: x.c, d: x.d }
}""",
        ]
        for source in variants:
            with self.subTest(circuit=source.split("circuit ")[1].split("(")[0]):
                relation, _ = compile_text(source)
                independent = parse_record_source_fragment(source.encode())
                self.assertEqual(independent, relation)
                self.assertEqual(expected_public_abi(independent), abi(relation, "direct-gate"))
                self.assertEqual(check_record_source_relation(source.encode(), encoded(relation))["capability"],
                                 CAPABILITY)
        relation = parse_record_source_fragment(SOURCE.encode())
        self.assertEqual(expected_public_abi(relation)["boundary_sha256"],
                         "7f753c6d58f189e17c3e57211a408dd23d196c0d818137e28dd114f32362f8d7")

    def test_flat_pattern_erases_to_exact_handwritten_relation(self) -> None:
        handwritten = """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""
        expected, _ = compile_text(handwritten)
        actual, _ = compile_text(PATTERN_SOURCE)
        self.assertEqual(actual, expected)
        self.assertEqual(parse_record_source_fragment(PATTERN_SOURCE.encode()), expected)
        self.assertEqual(expected_public_abi(actual), expected_public_abi(expected))

    def test_pattern_scope_nominal_type_and_eager_rhs_boundary(self) -> None:
        variants = (
            PATTERN_SOURCE.replace("Pair { right: saved, left }", "Pair { right: saved, right: left }"),
            PATTERN_SOURCE.replace("Pair { right: saved, left }", "Pair { right: saved, left: saved }"),
            PATTERN_SOURCE.replace("Pair { right: saved, left }", "Pair { unknown: saved }"),
            PATTERN_SOURCE.replace("Pair { right: saved, left }", "Pair {}"),
            PATTERN_SOURCE.replace("Pair { right: saved, left }", "Other { right: saved, left }"),
            PATTERN_SOURCE.replace("= x;", "= Pair { left: x.left, right: x.right };", 1),
            PATTERN_SOURCE.replace("= x;", "= future;", 1),
            PATTERN_SOURCE.replace("let Pair { right: secret } = y;", "let Pair { right: saved } = y;"),
            PATTERN_SOURCE.replace("let Pair { right: secret } = y;", "let Pair { right: p } = y;"),
        )
        for source in variants:
            with self.subTest(source=source):
                with self.assertRaises(UnsupportedRecordSourceFragment):
                    parse_record_source_fragment(source.encode())
        repeated = "\n".join(f"let Pair {{ left: alias_{index} }} = x;"
                             for index in range(17))
        bounded = PATTERN_SOURCE.replace("    let Pair { right: saved, left } = x;", repeated)
        with self.assertRaisesRegex(UnsupportedRecordSourceFragment, "too many record pattern bindings"):
            parse_record_source_fragment(bounded.encode())

    def test_resealed_relation_and_abi_forgery_rejected(self) -> None:
        relation = parse_record_source_fragment(SOURCE.encode())
        honest_abi = expected_public_abi(relation)
        with tempfile.TemporaryDirectory() as root:
            package = Path(root)
            source_bytes = SOURCE.encode()
            (package / "source.s31").write_bytes(source_bytes)

            def reseal(changed: dict, sidecar: dict) -> None:
                relation_bytes, abi_bytes = encoded(changed), encoded(sidecar)
                (package / "source.s31.json").write_bytes(relation_bytes)
                (package / "public-abi.json").write_bytes(abi_bytes)
                manifest = {
                    "schema": "s31-package-v1", "name": changed["name"],
                    "lowering": "direct-gate", "text_frontend_version": 1,
                    "source_text_sha256": digest(source_bytes),
                    "program_sha256": digest(relation_bytes),
                    "artifacts": {"source.s31": digest(source_bytes),
                                  "source.s31.json": digest(relation_bytes),
                                  "public-abi.json": digest(abi_bytes)},
                }
                (package / "manifest.json").write_bytes(encoded(manifest))

            reseal(relation, honest_abi)
            self.assertEqual(check_package_record_source_relation(package)["capability"], CAPABILITY)
            variants: dict[str, dict] = {}
            changed = copy.deepcopy(relation)
            changed["nodes"][0]["op"] = "add"
            variants["changed_op"] = changed
            changed = copy.deepcopy(relation)
            changed["nodes"][0]["rhs"] = "_s31_abi_input_2"
            variants["changed_private_operand"] = changed
            changed = copy.deepcopy(relation)
            changed["inputs"][0]["visibility"] = "private"
            variants["changed_visibility"] = changed
            changed = copy.deepcopy(relation)
            changed["inputs"][0], changed["inputs"][1] = changed["inputs"][1], changed["inputs"][0]
            variants["swapped_input_order"] = changed
            changed = copy.deepcopy(relation)
            changed["public_abi"]["result"]["leaves"][0]["path"][1]["field"] = "right"
            variants["changed_result_path"] = changed
            changed = copy.deepcopy(relation)
            changed["public_abi"]["inputs"][1]["leaves"][0]["wire"] = "_s31_abi_input_3"
            variants["changed_input_wire"] = changed
            changed = copy.deepcopy(relation)
            changed["public_abi"]["result"]["type"]["fields"].reverse()
            variants["changed_field_order"] = changed
            changed = copy.deepcopy(relation)
            changed["public_abi"]["result"]["type"]["record"] = "Other"
            variants["changed_nominal_type"] = changed
            changed = copy.deepcopy(relation)
            changed["public_abi"]["result"]["leaves"][1]["wire"] = "q"
            variants["changed_alias"] = changed
            changed = copy.deepcopy(relation)
            changed["public_outputs"].reverse()
            variants["changed_output_order"] = changed
            changed = copy.deepcopy(relation)
            changed["unknown"] = 0
            variants["unknown_relation_field"] = changed
            for label, changed in variants.items():
                with self.subTest(forgery=label):
                    reseal(changed, expected_public_abi(changed))
                    with self.assertRaisesRegex(ValueError, "relation differs"):
                        check_package_record_source_relation(package)

            for label, mutate in (
                ("digest", lambda obj: obj.update(boundary_sha256="0" * 64)),
                ("encoding", lambda obj: obj.update(encoding="different")),
                ("path", lambda obj: obj["boundary"]["result"]["leaves"][0]
                 ["path"][1].update(field="right")),
                ("numeric_type", lambda obj: obj["boundary"]["result"]["leaves"][0]
                 .update(length=1.0)),
            ):
                with self.subTest(abi_forgery=label):
                    changed_abi = copy.deepcopy(honest_abi)
                    mutate(changed_abi)
                    reseal(relation, changed_abi)
                    with self.assertRaisesRegex(ValueError, "ABI artifact differs"):
                        check_package_record_source_relation(package)

            reseal(relation, honest_abi)
            manifest_path = package / "manifest.json"
            manifest = json.loads(manifest_path.read_bytes())
            manifest["artifacts"]["public-abi.json"] = "0" * 64
            manifest_path.write_bytes(encoded(manifest))
            with self.assertRaisesRegex(ValueError, "artifact hash differs"):
                check_package_record_source_relation(package)

            for misleading_version in (True, 1.0):
                with self.subTest(manifest_version=misleading_version):
                    reseal(relation, honest_abi)
                    manifest = json.loads(manifest_path.read_bytes())
                    manifest["text_frontend_version"] = misleading_version
                    manifest_path.write_bytes(encoded(manifest))
                    with self.assertRaises(ValueError):
                        check_package_record_source_relation(package)

            reseal(relation, honest_abi)
            duplicate = (package / "public-abi.json").read_bytes().replace(
                b'"schema": "s31-public-abi-v2"\n',
                b'"schema": "s31-public-abi-v2", "schema": "s31-public-abi-v2"\n')
            (package / "public-abi.json").write_bytes(duplicate)
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                check_package_record_source_relation(package)

    def test_json_shape_and_duplicate_keys_rejected(self) -> None:
        relation = parse_record_source_fragment(SOURCE.encode())
        for label, path, value in (
            ("version_bool", ("version",), True),
            ("version_float", ("version",), 2.0),
            ("length_bool", ("inputs", 0, "length"), True),
            ("length_float", ("inputs", 0, "length"), 1.0),
        ):
            with self.subTest(label=label):
                changed = copy.deepcopy(relation)
                target = changed
                for part in path[:-1]:
                    target = target[part]
                target[path[-1]] = value
                with self.assertRaisesRegex(ValueError, "relation differs"):
                    check_record_source_relation(SOURCE.encode(), encoded(changed))
        duplicate = encoded(relation).replace(b'"version": 2\n', b'"version": 2, "version": 2\n')
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            check_record_source_relation(SOURCE.encode(), duplicate)
        noncanonical = json.dumps(relation, separators=(",", ":")).encode()
        with self.assertRaisesRegex(ValueError, "noncanonical JSON"):
            check_record_source_relation(SOURCE.encode(), noncanonical)

    def test_unsupported_syntax_fails_closed(self) -> None:
        variants = {
            "duplicate_field": SOURCE.replace("right: [m31; 1]", "left: [m31; 1]", 1),
            "missing_field": SOURCE.replace("right: x.right, ", ""),
            "duplicate_constructor_field": SOURCE.replace("right: x.right", "left: x.right"),
            "future_wire": SOURCE.replace("let p = x.left .* y.right", "let p = q .* y.right"),
            "unknown_field": SOURCE.replace("x.left .*", "x.other .*"),
            "unsupported_operator": SOURCE.replace("x.left .* y.right", "x.left - y.right"),
            "trailing_tokens": SOURCE + "let extra = q + q;",
            "shadow_generated_wire": SOURCE.replace("let p", "let _s31_abi_input_0"),
            "unsupported_width": SOURCE.replace("left: [m31; 1]", "left: [m31; 2]", 1),
            "oversized_source": SOURCE + " " * 20_000,
            "nine_public_words": """struct Triple { a: [m31; 1], b: [m31; 1], c: [m31; 1] }
circuit too_wide(public x: Triple, public y: Triple) -> public Triple {
    Triple { a: x.a, b: y.b, c: x.c }
}""",
        }
        for label, source in variants.items():
            with self.subTest(label=label), self.assertRaises(UnsupportedRecordSourceFragment):
                parse_record_source_fragment(source.encode())

    def test_production_rejected_declaration_names_fail_closed(self) -> None:
        source = """struct Pair { left: [m31; 1] }
circuit run(public x: Pair) -> public Pair { Pair { left: x.left } }
"""
        variants = {
            "enum_field": source.replace("left", "enum"),
            "match_input": source.replace(" x:", " match:").replace("x.left", "match.left"),
            "lowercase_record": source.replace("Pair", "pair"),
            "built_in_type_record": source.replace("Pair", "UInt256"),
            "record_circuit_collision": source.replace("circuit run", "circuit Pair"),
        }
        for label, candidate in variants.items():
            with self.subTest(label=label):
                with self.assertRaises(Exception):
                    compile_text(candidate)
                with self.assertRaises(UnsupportedRecordSourceFragment):
                    parse_record_source_fragment(candidate.encode())


if __name__ == "__main__":
    unittest.main()
