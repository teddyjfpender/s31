"""Named pure helpers must erase to the same certified direct-gate program."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.context import TEXT_FRONTEND_SOURCES  # noqa: E402
from package.correspondence import (UnsupportedFragment, canonical_ir_bytes,
                                    parse_source)  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def program(count: int, *, helper: bool) -> str:
    prefix = "fn square(v: [m31; 4]) -> [m31; 4] { v .* v }\n" if helper else ""
    lines = ["circuit powers(public x: [m31; 4]) -> public [m31; 4] {"]
    previous = "x"
    for index in range(count):
        name = f"step{index}"
        right = f"square({previous})" if helper else f"{previous} .* {previous}"
        lines.append(f"  let {name} = {right};")
        previous = name
    lines.extend([f"  {previous}", "}"])
    return prefix + "\n".join(lines) + "\n"


class StaticHelperReleaseTests(unittest.TestCase):
    def test_helper_erases_at_one_four_and_sixteen_gates(self) -> None:
        for count in (1, 4, 16):
            with self.subTest(count=count):
                direct = program(count, helper=False)
                functional = program(count, helper=True)
                direct_relation, direct_syntax = parse_source(direct.encode())
                functional_relation, functional_syntax = parse_source(functional.encode())
                self.assertEqual(direct_relation, functional_relation)
                self.assertEqual(direct_syntax, functional_syntax)
                self.assertEqual(canonical_ir_bytes(direct_syntax),
                                 canonical_ir_bytes(functional_syntax))
                self.assertEqual(compile_text(direct)[0], direct_relation)
                self.assertEqual(compile_text(functional)[0], functional_relation)
                self.assertEqual(len(functional_relation["nodes"]), count)

    def test_two_parameter_helper_and_aliases(self) -> None:
        source = """fn add(a: [m31; 4], b: [m31; 4]) -> [m31; 4] { a + b }
circuit add_square(public x: [m31; 4]) -> public [m31; 4] {
    let square = x .* x;
    let saved = square;
    let result = add((x), (saved));
    result
}
"""
        checked, syntax = parse_source(source.encode())
        production, _ = compile_text(source)
        self.assertEqual(checked, production)
        self.assertEqual([node["op"] for node in checked["nodes"]], ["mul", "add"])
        self.assertEqual(syntax["output"], 2)

    def test_rejected_helper_forms_fail_closed(self) -> None:
        source = program(1, helper=True)
        malformed = [
            source.replace("v .* v", "v + missing"),
            source.replace("v .* v", "v .* v + v"),
            source.replace("v .* v", "std::math::inv(v)"),
            source.replace("[m31; 4]) ->", "[m31; 5]) ->", 1),
            source.replace("fn square(v:", "fn square(square:"),
            source.replace("square(x)", "square((x)"),
            source.replace("square(x)", "square(x, x)"),
            source.replace("square(x)", "square(missing)"),
            source.replace("let step0 = square(x);", "let step0 = x .* x;"),
            source.replace("circuit powers", "circuit square"),
            source.replace("let step0", "let square"),
            source + "fn other(v: [m31; 4]) -> [m31; 4] { v + v }",
        ]
        for changed in malformed:
            with self.subTest(source=changed[:95]), self.assertRaises(UnsupportedFragment):
                parse_source(changed.encode())

    def test_uncertified_operand_reversal_and_new_module_binding(self) -> None:
        source = """fn add(a: [m31; 4], b: [m31; 4]) -> [m31; 4] { b + a }
circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let first = x .* x;
  let result = add(x, first);
  result
}
"""
        with self.assertRaisesRegex(UnsupportedFragment, "canonical order"):
            parse_source(source.encode())
        optimized, _ = parse_source(source.encode(), optimized=True)
        self.assertEqual(optimized, compile_text(source)[0])
        self.assertIn(S31 / "python/package/source_fragments/static_helper.py",
                      TEXT_FRONTEND_SOURCES)


if __name__ == "__main__":
    unittest.main()
