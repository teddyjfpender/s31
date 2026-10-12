"""Handwritten early-return alias DAG used by the general Lean witness note."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import canonical_ir_bytes, parse_source
from package.direct_gate_schedule import exact_direct_gate_schedule
from text_frontend import compile_text


ALIAS = """circuit early_alias(public x: [m31; 4]) -> public [m31; 4] {
  let base = (x);
  let a = ((base) .* (base));
  let saved = (a);
  let b = base + saved;
  let c = ((saved) .* (b));
  let returned = saved;
  returned
}"""

DIRECT = """circuit early_alias(public x: [m31; 4]) -> public [m31; 4] {
  let a = x .* x;
  let b = x + a;
  let c = a .* b;
  a
}"""


class AliasEarlyReturnProjectedTests(unittest.TestCase):
    def test_alias_early_return_has_same_producer_rows_as_direct(self) -> None:
        alias_relation, alias_syntax = parse_source(ALIAS.encode())
        direct_relation, direct_syntax = parse_source(DIRECT.encode())
        production_relation, source_map = compile_text(ALIAS)
        self.assertEqual(alias_relation, production_relation)
        self.assertEqual(alias_relation, direct_relation)
        self.assertEqual(
            (json.dumps(alias_relation, indent=2, sort_keys=True) + "\n").encode(),
            (json.dumps(direct_relation, indent=2, sort_keys=True) + "\n").encode())
        self.assertEqual(canonical_ir_bytes(alias_syntax),
                         canonical_ir_bytes(direct_syntax))
        self.assertEqual(alias_syntax["output"], 1)
        self.assertEqual([step["op"] for step in alias_syntax["instructions"]],
                         ["mul", "add", "mul"])
        self.assertEqual(set(source_map), {"a", "b", "c"})

        gates, _, rows, source_gates = exact_direct_gate_schedule(alias_syntax)
        self.assertEqual(rows, 512)
        self.assertEqual(len(gates["add"]), 474)
        self.assertEqual(len(gates["pointwise_mul"]), 10)
        self.assertEqual(sum(len(gates[kind]) for kind in ("add", "sub", "mul")),
                         502)
        self.assertEqual([step["out"] for step in source_gates], [23, 24, 25])
        self.assertEqual(gates["add"][3]["out"], 24)
        self.assertEqual([gate["out"] for gate in gates["pointwise_mul"][:2]],
                         [23, 25])
        # The final eager arithmetic producer is locally constrained but no
        # gate or public mask reads its value after it is produced.
        self.assertEqual(sum(gate[port] == 25 for group in gates.values()
                             for gate in group for port in ("in0", "in1")), 0)

    def test_retargeted_alias_changes_selected_certificate_and_ir(self) -> None:
        original, original_syntax = parse_source(ALIAS.encode())
        retargeted = ALIAS.replace("let returned = saved;", "let returned = c;")
        changed, changed_syntax = parse_source(retargeted.encode())
        produced, _ = compile_text(retargeted)
        self.assertEqual(changed, produced)
        self.assertNotEqual(changed, original)
        self.assertEqual(changed_syntax["output"], 3)
        self.assertNotEqual(canonical_ir_bytes(changed_syntax),
                            canonical_ir_bytes(original_syntax))


if __name__ == "__main__":
    unittest.main()
