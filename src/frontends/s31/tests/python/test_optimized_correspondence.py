"""Opt-in direct-gate source-to-canonical checks for reversed and shared gates."""

from __future__ import annotations

import copy
import itertools
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import (UnsupportedFragment, canonical_ir_bytes,
                                    canonical, digest, gate_schedule, parse_source,
                                    parse_source_optimized)
from package.direct_gate_schedule import exact_direct_gate_schedule
from text_frontend import compile_text


SOURCE = ("circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { "
          "let a = x + x; let b = x .* x; let c = a + b; "
          "let d = b + a; d }")
CANONICAL_DIGEST = "2088c1bad15f2ba5b52f0214e9d3d66744b9c84aa6218aa336d8b337157e7132"
COMPONENTS = ("eq", "m31_to_u32", "triple_xor", "blake_g")


def native_shape_report(names: list[str], ids: list[int]) -> dict:
    rows = []
    for name, canonical_id in zip(names, ids, strict=True):
        start = 0 if canonical_id == 0 else 5 + canonical_id
        row = {"name": name, "canonical_id": canonical_id,
               "qm31_start": start,
               "qm31_end": 6 if canonical_id == 0 else start + 1}
        for component in COMPONENTS:
            row[f"{component}_start"] = 0
            row[f"{component}_end"] = 0
        rows.append(row)
    return {"source_map": rows}


class OptimizedCorrespondenceTests(unittest.TestCase):
    def test_opt_in_checks_production_relation_ir_and_compact_gate_count(self) -> None:
        with self.assertRaises(UnsupportedFragment):
            parse_source(SOURCE.encode())
        relation, syntax = parse_source_optimized(SOURCE.encode())
        produced, _ = compile_text(SOURCE)
        self.assertEqual(relation, produced)
        self.assertEqual(syntax["source_names"], ["x", "a", "b", "c", "d"])
        self.assertEqual(syntax["source_to_canonical"], [0, 1, 2, 3, 3])
        self.assertEqual([node["op"] for node in syntax["instructions"]],
                         ["add", "mul", "add"])
        self.assertEqual(syntax["instructions"][2]["lhs"], 1)
        self.assertEqual(syntax["instructions"][2]["rhs"], 2)
        self.assertEqual(syntax["output_name"], "d")
        self.assertEqual(syntax["output"], 3)
        self.assertEqual(digest(canonical_ir_bytes(syntax)), CANONICAL_DIGEST)
        gates, _, _, source_gates = exact_direct_gate_schedule(syntax)
        self.assertEqual(len(source_gates), 3)
        self.assertEqual(len(gates["pointwise_mul"]), 9)  # 1 source mul + 4 masks + 4 inputs

    def test_resealed_wrong_source_map_and_reused_span_are_rejected(self) -> None:
        _, syntax = parse_source_optimized(SOURCE.encode())
        report = native_shape_report(syntax["source_names"],
                                     syntax["source_to_canonical"])
        schedule = gate_schedule(syntax, report)
        self.assertEqual([row["id"] for row in schedule], [0, 1, 2, 3])
        self.assertEqual([row["qm31_start"] for row in schedule], [0, 6, 7, 8])
        self.assertEqual(schedule[-1]["name"], "c")

        for field, value in (("canonical_id", 2), ("qm31_start", 9),
                             ("qm31_end", 10), ("name", "c")):
            changed = copy.deepcopy(report)
            changed["source_map"][-1][field] = value
            # Even a freshly sealed outer report digest cannot make a false
            # source-to-canonical mapping or span pass the source-derived check.
            resealed = {"cost_report_sha256": digest(canonical(changed))}
            self.assertEqual(resealed["cost_report_sha256"], digest(canonical(changed)))
            self.assertNotEqual(resealed["cost_report_sha256"], digest(canonical(report)))
            with self.subTest(field=field), self.assertRaises(ValueError):
                gate_schedule(syntax, changed)

    def test_cse_uses_canonical_operands_after_earlier_sharing(self) -> None:
        source = ("circuit sharing(public x: [m31; 4]) -> public [m31; 4] { "
                  "let a = x + x; let b = x + x; let c = b .* a; "
                  "let d = a .* b; d }")
        relation, syntax = parse_source_optimized(source.encode())
        self.assertEqual(relation, compile_text(source)[0])
        self.assertEqual(syntax["source_to_canonical"], [0, 1, 1, 2, 2])
        self.assertEqual([(step["op"], step["lhs"], step["rhs"])
                          for step in syntax["instructions"]],
                         [("add", 0, 0), ("mul", 1, 1)])
        report = native_shape_report(syntax["source_names"],
                                     syntax["source_to_canonical"])
        self.assertEqual(len(gate_schedule(syntax, report)), 3)

    def test_all_three_step_add_mul_dags_match_source_semantics(self) -> None:
        names = ("x", "a", "b", "c")
        choices = [[(op, left, right) for op in ("+", ".*")
                    for left in range(index + 1)
                    for right in range(index + 1)] for index in range(3)]
        checked = 0
        for steps in itertools.product(*choices):
            body = " ".join(
                f"let {names[index + 1]} = {names[left]} {op} {names[right]};"
                for index, (op, left, right) in enumerate(steps))
            for output in range(1, 4):
                source = ("circuit scan(public x: [m31; 4]) -> public [m31; 4] "
                          f"{{ {body} {names[output]} }}")
                relation, syntax = parse_source_optimized(source.encode())
                self.assertEqual(relation, compile_text(source)[0])
                self.assertEqual(len(syntax["source_to_canonical"]), 4)
                for input_value in (0, 5, 2**31 - 2):
                    raw = [input_value]
                    for op, left, right in steps:
                        value = (raw[left] + raw[right] if op == "+"
                                 else raw[left] * raw[right]) % (2**31 - 1)
                        raw.append(value)
                    compact = [input_value]
                    for step in syntax["instructions"]:
                        left, right = compact[step["lhs"]], compact[step["rhs"]]
                        compact.append((left + right if step["op"] == "add"
                                        else left * right) % (2**31 - 1))
                    self.assertEqual(compact[syntax["output"]], raw[output])
                checked += 1
        self.assertEqual(checked, 864)


if __name__ == "__main__":
    unittest.main()
