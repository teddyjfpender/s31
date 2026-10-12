"""Deterministic source-vs-fieldwise corpus for nested product selection."""

from __future__ import annotations

import hashlib
import json
import random
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import flat_assignment_from_typed
from oracle import OracleError, evaluate_relation
from s31_stdlib import P
from text_frontend import compile_text


SEED = 0x531C0DE
CASES = 48
EXPECTED_CORPUS_SHA256 = "bc8a695422145e103f8293315f30f4f9456837ba3097a0af2a6df353512d750b"
TERMS = (
    ("x", lambda x, y: x),
    ("y", lambda x, y: y),
    ("x + x", lambda x, y: 2 * x % P),
    ("y + y", lambda x, y: 2 * y % P),
    ("x + y", lambda x, y: (x + y) % P),
    ("x .* x", lambda x, y: x * x % P),
    ("y .* y", lambda x, y: y * y % P),
    ("x .* y", lambda x, y: x * y % P),
)


def program(terms: tuple[int, ...], *, fieldwise: bool) -> str:
    chosen = [TERMS[index][0] for index in terms]
    common = """struct Pair { first: [m31; 1], nested: ([m31; 1], [m31; 1]) }
circuit generated(private x: [m31; 1], private y: [m31; 1]) -> public Pair {
    let b = is_zero(x);
    let a = Pair { first: A0, nested: (A1, A2) };
    let c = Pair { first: C0, nested: (C1, C2) };
"""
    for marker, value in zip(("A0", "A1", "A2", "C0", "C1", "C2"), chosen):
        common = common.replace(marker, value)
    if not fieldwise:
        return common + "    if b then a else c\n}\n"
    return common + """    Pair {
        first: if b then a.first else c.first,
        nested: (if b then a.nested.0 else c.nested.0,
                 if b then a.nested.1 else c.nested.1),
    }
}
"""


class GeneratedProductControlTests(unittest.TestCase):
    def test_nested_record_selection_against_fieldwise_and_integer_model(self) -> None:
        rng = random.Random(SEED)
        cases = [tuple(rng.randrange(len(TERMS)) for _ in range(6))
                 for _ in range(CASES)]
        sources = [(program(case, fieldwise=False), program(case, fieldwise=True))
                   for case in cases]
        corpus = "".join(source + "\0" + manual + "\n" for source, manual in sources)
        self.assertEqual(hashlib.sha256(corpus.encode()).hexdigest(), EXPECTED_CORPUS_SHA256)
        for index, (case, (source, manual)) in enumerate(zip(cases, sources)):
            with self.subTest(index=index):
                product, _ = compile_text(source)
                fieldwise, _ = compile_text(manual)
                self.assertEqual(product, fieldwise)
                semantic = {**product, "version": 1}
                semantic.pop("public_abi")
                for x, y in ((0, 7), (3, 7), (P - 1, 2)):
                    selected = case[:3] if x == 0 else case[3:]
                    values = [TERMS[term][1](x, y) for term in selected]
                    typed = {
                        "version": 2, "public_inputs": {},
                        "private_inputs": {"x": [x], "y": [y]},
                        "result": {"first": [values[0]],
                                   "nested": [[values[1]], [values[2]]]},
                    }
                    flat = flat_assignment_from_typed(product, json.dumps(typed).encode())
                    self.assertEqual(evaluate_relation(semantic, flat), flat["public_outputs"])
                    forged = json.loads(json.dumps(flat))
                    wire = product["public_outputs"][0]
                    forged["public_outputs"][wire][0] = (values[0] + 1) % P
                    with self.assertRaises(OracleError):
                        evaluate_relation(semantic, forged)


if __name__ == "__main__":
    unittest.main()
