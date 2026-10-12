"""Exhaustive small lexical-let schedules against two independent lowerings."""

from __future__ import annotations

import itertools
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import parse_source  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def sources(operators: tuple[str, ...], *, helper: bool, wrapped: bool) -> tuple[str, str]:
    previous = f"local{len(operators) - 1}"
    expression = f"{previous} + {previous}"
    manual: list[str] = []
    for index in reversed(range(len(operators))):
        operand = "x" if index == 0 else f"local{index - 1}"
        bound = ("step(x)" if helper and index == 0 else
                 f"{operand} {operators[index]} {operand}")
        expression = f"let local{index} = {bound} in {expression}"
    for index, operator in enumerate(operators):
        operand = "x" if index == 0 else f"_s31_{index - 1}"
        manual.append(f"  let _s31_{index} = {operand} {operator} {operand};")
    if wrapped:
        expression = f"({expression})"
    prefix = (f"fn step(v: [m31; 4]) -> [m31; 4] {{ v {operators[0]} v }}\n"
              if helper else "")
    header = "circuit generated(public x: [m31; 4]) -> public [m31; 4] {\n"
    functional = prefix + header + f"  let result = {expression};\n  result\n}}\n"
    direct = (header + "\n".join(manual) + "\n" +
              f"  let result = _s31_{len(operators) - 1} + _s31_{len(operators) - 1};\n"
              "  result\n}\n")
    return functional, direct


class LexicalCorpusTests(unittest.TestCase):
    def test_all_small_operation_chains_have_exact_zero_cost(self) -> None:
        cases = 0
        for count in range(1, 5):
            for operators in itertools.product(("+", ".*"), repeat=count):
                helper = count % 2 == 0
                wrapped = operators[-1] == "+"
                functional, direct = sources(operators, helper=helper, wrapped=wrapped)
                with self.subTest(operators=operators):
                    checked = parse_source(functional.encode())
                    self.assertEqual(checked, parse_source(direct.encode()))
                    self.assertEqual(checked[0], compile_text(functional)[0])
                    self.assertEqual(len(checked[0]["nodes"]), count + 1)
                cases += 1
        self.assertEqual(cases, 30)


if __name__ == "__main__":
    unittest.main()
