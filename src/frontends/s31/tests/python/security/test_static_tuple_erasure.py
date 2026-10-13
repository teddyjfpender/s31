"""Exact source-byte product erasure against the production S31 compiler."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.source_relation_fragment import (  # noqa: E402
    LEAN_EFFECTS_PROFILE, UnsupportedSourceRelationFragment,
    check_source_relation_certificate, make_source_relation_certificate,
    parse_source_fragment,
)
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def source(body: str) -> str:
    return ("circuit tuple_case(public x: [m31; 2], private y: [m31; 2]) "
            "-> public [m31; 2] { " + body + " }")


class StaticTupleErasureTests(unittest.TestCase):
    def test_static_products_have_the_same_complete_relation_as_compiler(self) -> None:
        for body in (
            "let p = (x, y); let out = p.0 + p.1; out",
            "let p = (x, y); let q = p; let out = q.1 - p.0; out",
            "let p = (x, y, x, y); let out = p.2 .* p.3; out",
            "let first = x + y; let p = (first, x); "
            "assert_eq(p.0, first); let out = p.1 + y; out",
            "let p = (x, y); let dead = p.1 .* x; p.0",
        ):
            with self.subTest(body=body):
                text = source(body)
                actual, _ = compile_text(text)
                self.assertEqual(parse_source_fragment(text.encode()), actual)
                certificate = make_source_relation_certificate(text.encode(), canonical(actual))
                self.assertEqual(certificate["lean_semantic_profile"], LEAN_EFFECTS_PROFILE)
                self.assertEqual(certificate["unmodeled_features"], [])
                self.assertEqual(check_source_relation_certificate(
                    text.encode(), canonical(actual), canonical(certificate)), certificate)

    def test_product_changes_never_inherit_a_resealed_certificate(self) -> None:
        text = source("let p = (x, y); let out = p.0 + p.1; out")
        relation, _ = compile_text(text)
        certificate = make_source_relation_certificate(text.encode(), canonical(relation))
        for changed in (
            text.replace("(x, y)", "(y, x)"),
            text.replace("p.0 + p.1", "p.1 + p.0"),
            text.replace("p.0 + p.1", "p.0 + p.0"),
        ):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                check_source_relation_certificate(changed.encode(), canonical(relation),
                                                  canonical(certificate))
        forged = copy.deepcopy(relation)
        forged["nodes"][0]["lhs"] = "y"
        with self.assertRaisesRegex(ValueError, "relation differs"):
            make_source_relation_certificate(text.encode(), canonical(forged))

    def test_out_of_scope_and_invalid_projection_fail_closed(self) -> None:
        for body in (
            "let p = (x, y); let out = p.2 + x; out",
            "let p = (x, y); let out = p.01 + x; out",
            "let out = p.0 + x; let p = (x, y); out",
            "let p = (x, y); let out = p + x; out",
            "let p = (x, y); let out = x.0 + y; out",
            "let p = (x, y); let out = p.0 + y; p",
            "let p = (x, y); let out = (p.0 + y); out",
            "let p = (x, y); let q = (p); let out = q.0 + y; out",
            "let p = ((x), y); let out = p.0 + y; out",
            "let p = (x, splat<2>(1_m31)); let out = x + y; out",
            "let p = (x, y, x, y, x); let out = x + y; out",
        ):
            with self.subTest(body=body), self.assertRaises(UnsupportedSourceRelationFragment):
                parse_source_fragment(source(body).encode())


if __name__ == "__main__":
    unittest.main()
