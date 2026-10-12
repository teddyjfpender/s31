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

    def test_straight_line_helper_body_and_repeated_calls(self) -> None:
        source = """fn twice_square(v: [m31; 4]) -> [m31; 4] {
  let square = v .* v;
  square + square
}
circuit repeated(public x: [m31; 4]) -> public [m31; 4] {
  let first = twice_square(x);
  let result = twice_square(first);
  result
}
"""
        direct = """circuit repeated(public x: [m31; 4]) -> public [m31; 4] {
  let _s31_i1_0 = x .* x;
  let first = _s31_i1_0 + _s31_i1_0;
  let _s31_i2_0 = first .* first;
  let result = _s31_i2_0 + _s31_i2_0;
  result
}
"""
        checked, syntax = parse_source(source.encode())
        direct_checked, direct_syntax = parse_source(direct.encode())
        self.assertEqual(checked, direct_checked)
        self.assertEqual(syntax, direct_syntax)
        self.assertEqual(compile_text(source)[0], checked)
        self.assertEqual(len(checked["nodes"]), 4)

    def test_returned_local_and_three_gate_body(self) -> None:
        source = """fn poly(v: [m31; 4]) -> [m31; 4] {
  let square = v .* v;
  let fourth = square .* square;
  v + fourth
}
circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let result = poly(x);
  result
}
"""
        checked, _ = parse_source(source.encode())
        self.assertEqual(checked, compile_text(source)[0])
        self.assertEqual(len(checked["nodes"]), 3)

        returned = source.replace("v + fourth", "fourth")
        checked_returned, _ = parse_source(returned.encode())
        self.assertEqual(checked_returned, compile_text(returned)[0])
        self.assertEqual(len(checked_returned["nodes"]), 2)

    def test_helper_locals_are_bounded_and_hygienic(self) -> None:
        source = """fn polynomial(v: [m31; 4]) -> [m31; 4] {
  let square = v .* v;
  square + square
}
circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let result = polynomial(x);
  result
}
"""
        malformed = [
            source.replace("let square =", "let v ="),
            source.replace("square + square", "missing + square"),
            source.replace("square + square", "v + v + square"),
            source.replace("square + square", "v"),
            source.replace("let square = v .* v;", "let square = square .* v;"),
            source.replace("let result =", "let _s31_i1_0 ="),
            source.replace("let square = v .* v;", "let square = v .* v; let square = v .* v;"),
        ]
        for changed in malformed:
            with self.subTest(source=changed[:100]), self.assertRaises(UnsupportedFragment):
                parse_source(changed.encode())

    def test_sixteen_gate_body_is_the_exact_limit(self) -> None:
        def source(count: int) -> str:
            previous = "v"
            steps = []
            for index in range(count):
                current = f"power{index}"
                steps.append(f"  let {current} = {previous} .* {previous};")
                previous = current
            return ("fn power(v: [m31; 4]) -> [m31; 4] {\n" +
                    "\n".join(steps) + f"\n  {previous}\n}}\n" +
                    "circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n" +
                    "  let result = power(x);\n  result\n}\n")

        accepted = source(16)
        checked, _ = parse_source(accepted.encode())
        self.assertEqual(checked, compile_text(accepted)[0])
        self.assertEqual(len(checked["nodes"]), 16)
        with self.assertRaisesRegex(UnsupportedFragment, "exceeds 16"):
            parse_source(source(17).encode())

    def test_acyclic_function_composition_erases_to_direct_gates(self) -> None:
        source = """fn square(v: [m31; 4]) -> [m31; 4] { v .* v }
fn twice(v: [m31; 4]) -> [m31; 4] {
  let squared = square(v);
  squared + squared
}
fn add_original(v: [m31; 4]) -> [m31; 4] {
  let doubled = twice(v);
  v + doubled
}
circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let result = add_original(x);
  result
}
"""
        direct = """circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let _s31_i2_0 = x .* x;
  let _s31_i1_0 = _s31_i2_0 + _s31_i2_0;
  let result = x + _s31_i1_0;
  result
}
"""
        checked, syntax = parse_source(source.encode())
        direct_checked, direct_syntax = parse_source(direct.encode())
        self.assertEqual(checked, compile_text(source)[0])
        self.assertEqual((checked, syntax), (direct_checked, direct_syntax))
        self.assertEqual(len(checked["nodes"]), 3)

    def test_composition_rejects_forward_calls_and_unused_declarations(self) -> None:
        source = """fn square(v: [m31; 4]) -> [m31; 4] { v .* v }
fn twice(v: [m31; 4]) -> [m31; 4] { square(v) }
circuit calc(public x: [m31; 4]) -> public [m31; 4] {
  let result = twice(x);
  result
}
"""
        self.assertEqual(parse_source(source.encode())[0], compile_text(source)[0])
        with self.assertRaisesRegex(UnsupportedFragment, "earlier declaration"):
            parse_source(source.replace("fn square", "fn missing", 1).encode())
        with self.assertRaisesRegex(UnsupportedFragment, "unused static helper"):
            parse_source(source.replace("twice(x)", "square(x)").encode())
        with self.assertRaises(UnsupportedFragment):
            parse_source(source.replace("square(v) }", "twice(v) }").encode())

    def test_eight_function_chain_is_the_declaration_limit(self) -> None:
        def source(count: int) -> str:
            functions = ["fn f0(v: [m31; 4]) -> [m31; 4] { v + v }"]
            functions.extend(
                f"fn f{index}(v: [m31; 4]) -> [m31; 4] {{ f{index - 1}(v) }}"
                for index in range(1, count))
            return ("\n".join(functions) + "\n" +
                    "circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n" +
                    f"  let result = f{count - 1}(x);\n  result\n}}\n")

        accepted = source(8)
        checked, _ = parse_source(accepted.encode())
        self.assertEqual(checked, compile_text(accepted)[0])
        self.assertEqual(len(checked["nodes"]), 1)
        with self.assertRaisesRegex(UnsupportedFragment, "more than eight"):
            parse_source(source(9).encode())

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
