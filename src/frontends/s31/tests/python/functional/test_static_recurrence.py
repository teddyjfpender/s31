"""Static function values must retain the dedicated recurrence relation."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


P = (1 << 31) - 1
STEP = "fn step(v: [m31; 4]) -> [m31; 4] { v .* v + splat<4>(7_m31) }\n"
RUN = ("fn run(f: Fn([m31; 4]) -> [m31; 4], x: [m31; 4]) -> [m31; 4] "
       "{ iterate<16>(f, x) }\n")
HEADER = "circuit p(public x: [m31; 4]) -> public [m31; 4] { let result = "


class StaticRecurrenceTests(unittest.TestCase):
    def test_named_and_captured_steps_match_direct_chip_relation(self) -> None:
        direct, _ = compile_text(STEP + HEADER + "iterate<16>(step, x); result }")
        sources = (
            STEP + RUN + HEADER + "run(step, x); result }",
            STEP + HEADER + "iterate<16>(let f = step in f, x); result }",
            STEP + "fn choose() -> Fn([m31; 4]) -> [m31; 4] { step }\n" +
            HEADER + "iterate<16>(choose(), x); result }",
            HEADER + "iterate<16>(fun(v: [m31; 4]) -> [m31; 4] => "
                     "v .* v + splat<4>(7_m31), x); result }",
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
            "let bias = splat<4>(7_m31); "
            "let f = fun(v: [m31; 4]) -> [m31; 4] => v .* v + bias; "
            "let result = iterate<16>(f, x); result }",
        )
        self.assertEqual(direct["nodes"], [{
            "name": "result", "op": "repeat", "lhs": "x", "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 7}],
        }])
        words = [0, 1, 2, P - 1]
        expected = words[:]
        for _ in range(16):
            expected = [(value * value + 7) % P for value in expected]
        for source in sources:
            with self.subTest(source=source):
                relation, _ = compile_text(source)
                self.assertEqual(relation, direct)
                assignment = {"public_inputs": {"x": words}, "private_inputs": {},
                              "public_outputs": {"result": expected[:]}}
                self.assertEqual(evaluate_relation(relation, assignment),
                                 assignment["public_outputs"])
                assignment["public_outputs"]["result"][0] = (expected[0] + 1) % P
                with self.assertRaises(OracleError):
                    evaluate_relation(relation, assignment)

    def test_local_step_shadows_global_function(self) -> None:
        source = (STEP + "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
                  "let step = fun(v: [m31; 4]) -> [m31; 4] => v .* v; "
                  "iterate<16>(step, x) }")
        relation, _ = compile_text(source)
        self.assertEqual(relation["nodes"][0]["body"], [{"op": "square"}])

    def test_mix4_step_flows_through_higher_order_helpers(self) -> None:
        mix = "fn mix(v: [m31; 4]) -> [m31; 4] { std::math::mix4(v) }\n"
        relay = ("fn relay(f: Fn([m31; 4]) -> [m31; 4], x: [m31; 4]) "
                 "-> [m31; 4] { run(f, x) }\n")
        choose = "fn choose() -> Fn([m31; 4]) -> [m31; 4] { mix }\n"
        identity = ("fn identity(f: Fn([m31; 4]) -> [m31; 4]) "
                    "-> Fn([m31; 4]) -> [m31; 4] { f }\n")
        factory = ("fn make() -> Fn([m31; 4]) -> [m31; 4] { "
                   "fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v) }\n")
        sources = (
            mix + RUN + relay +
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { relay(mix, x) }",
            mix + choose +
            "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ iterate<16>(choose(), x) }",
            mix + identity +
            "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ iterate<16>(identity(mix), x) }",
            mix + identity +
            "fn choose() -> Fn([m31; 4]) -> [m31; 4] { identity(mix) }\n"
            "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ iterate<16>(choose(), x) }",
            factory +
            "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ iterate<16>(make(), x) }",
            factory + RUN +
            "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ run(make(), x) }",
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
            "let f = fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v); "
            "iterate<16>(f, x) }",
            RUN + "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
            "let f = fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v); "
            "let alias = f; run(alias, x) }",
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
            "let f = fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v) in "
            "iterate<16>(f, x) }",
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
            "iterate<16>(fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v), x) }",
        )
        direct, _ = compile_text(
            mix + "circuit p(public x: [m31; 4]) -> public [m31; 4] "
            "{ iterate<16>(mix, x) }")
        for source in sources:
            with self.subTest(source=source):
                relation, _ = compile_text(source)
                self.assertEqual(relation, direct)
                self.assertEqual(relation["nodes"], [{
                    "name": "_s31_0", "op": "repeat", "lhs": "x", "rounds": 16,
                    "body": [{"op": "mix4"}],
                }])

    def test_nonconstant_capture_and_unsupported_step_are_rejected(self) -> None:
        sources = (
            ("circuit p(public x: [m31; 4]) -> public [m31; 4] { "
             "let f = fun(v: [m31; 4]) -> [m31; 4] => v .* v + x; "
             "iterate<16>(f, x) }", "iterate step must use"),
            ("circuit p(public x: [m31; 4]) -> public [m31; 4] { "
             "iterate<16>(fun(v: [m31; 4]) -> [m31; 4] => std::math::inv(v), x) }",
             "iterate step must use"),
        )
        for source, message in sources:
            with self.subTest(source=source), self.assertRaisesRegex(SourceError, message):
                compile_text(source)

    def test_partial_step_expression_is_rejected_in_inactive_branch(self) -> None:
        source = (STEP + "circuit p(public b: bit, private x: [m31; 4]) "
                  "-> public [m31; 4] { if b then "
                  "iterate<16>(let unused = std::math::inv(x) in step, x) else x }")
        with self.assertRaisesRegex(
            SourceError, "if branch may fail when inactive: std::math::inv"
        ):
            compile_text(source)
        through_helper = (
            "fn bad(v: [m31; 4]) -> [m31; 4] { std::math::inv(v) } "
            + RUN +
            "circuit p(public b: bit, private x: [m31; 4]) -> public [m31; 4] "
            "{ if b then run(bad, x) else x }")
        with self.assertRaisesRegex(
            SourceError, "if branch may fail when inactive: std::math::inv"
        ):
            compile_text(through_helper)
        factory = (
            "fn make() -> Fn([m31; 4]) -> [m31; 4] { "
            "fun(v: [m31; 4]) -> [m31; 4] => std::math::inv(v) } "
            "circuit p(public b: bit, private x: [m31; 4]) -> public [m31; 4] "
            "{ if b then iterate<16>(make(), x) else x }")
        with self.assertRaisesRegex(
            SourceError, "if branch may fail when inactive: std::math::inv"
        ):
            compile_text(factory)

    def test_mix4_cannot_escape_the_step_context(self) -> None:
        source = (
            "fn make() -> Fn([m31; 4]) -> [m31; 4] { "
            "fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v) } "
            "circuit p(public x: [m31; 4]) -> public [m31; 4] { make()(x) }")
        with self.assertRaisesRegex(SourceError, "std::math::mix4 requires"):
            compile_text(source)


if __name__ == "__main__":
    unittest.main()
