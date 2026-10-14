"""Bounded statement and installed pin-route mutation controls."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts.compiler.control_public_statement_audit import (
    ABI, P, ROUTE_SCOPE, SOURCE_ROUTE, public_words, source_route_guard,
)

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "src/frontends/s31/tests/python/security/fixtures/control_air"


def statement(x: object = 0, result: object = None) -> bytes:
    if result is None:
        result = [1, 2, 3, 4]
    return json.dumps({"public_inputs": {"x": [x]},
                       "public_outputs": {"result": result}}).encode()


class ControlPublicStatementAuditTests(unittest.TestCase):
    def test_canonical_public_word_order_and_padding(self) -> None:
        self.assertEqual(public_words(statement(P - 1, [0, 1, 2, P - 1]), ABI),
                         [P - 1, 0, 1, 2, P - 1, 0, 0, 0])

    def test_changed_sealed_abi_is_rejected(self) -> None:
        altered = copy.deepcopy(ABI)
        altered["public_outputs"][0]["length"] = 3
        with self.assertRaisesRegex(ValueError, "sealed ABI"):
            public_words(statement(), altered)

    def test_private_unknown_duplicate_and_noncanonical_fields_rejected(self) -> None:
        cases = [
            statement(P),
            statement(True),
            statement(result=[1, 2, 3]),
            statement(result=[1, 2, 3, -1]),
            statement(result=[1, 2, 3, P]),
            b'{"public_inputs":{"x":[0],"x":[1]},"public_outputs":{"result":[1,2,3,4]}}',
            b'{"public_inputs":{"x":[0]},"public_outputs":{"result":[1,2,3,4]},"private_inputs":{}}',
            b'{"public_inputs":{"x":[0]},"public_outputs":{"result":[1,2,3,4],"extra":[]}}',
        ]
        for case in cases:
            with self.subTest(case=case[:80]):
                with self.assertRaises(ValueError):
                    public_words(case, ABI)

    def test_native_source_route_guard_rejects_each_missing_edge(self) -> None:
        self.assertEqual(set(source_route_guard()), set(SOURCE_ROUTE))
        sources = {path: (ROOT / path).read_text() for path in SOURCE_ROUTE}
        for path, markers in SOURCE_ROUTE.items():
            for marker in markers:
                with self.subTest(path=path, marker=marker):
                    altered = dict(sources)
                    start = altered[path].index(ROUTE_SCOPE[path][0])
                    before, within = altered[path][:start], altered[path][start:]
                    altered[path] = before + within.replace(marker, "/* altered */", 1)
                    with self.assertRaisesRegex(ValueError, "route changed"):
                        source_route_guard(sources=altered)

    def test_pin_order_mutation_rejected_by_source_bound_topology(self) -> None:
        from package.control_air_correspondence import check_control_air
        topology = json.loads((FIXTURE / "gate-topology.json").read_text())
        topology["output"][2], topology["output"][3] = (
            topology["output"][3], topology["output"][2])
        with self.assertRaisesRegex(ValueError, "public output ABI"):
            check_control_air(FIXTURE, topology)


if __name__ == "__main__":
    unittest.main()
