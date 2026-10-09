"""Higher-order source forms must erase to the first-order circuit relation."""

import json
import sys
import unittest
from pathlib import Path

S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

from oracle import evaluate_relation
from text_frontend import SourceError, compile_file, compile_text
from s31 import TEXT_FRONTEND_SOURCES


class FunctionalCoreTests(unittest.TestCase):
    @staticmethod
    def operation_graph(relation: dict) -> tuple[list[dict], list[str]]:
        """Ignore descriptive names while retaining every operation and edge."""
        names = {item["name"]: f"input{index}" for index, item in enumerate(relation["inputs"])}
        nodes = []
        for index, node in enumerate(relation["nodes"]):
            nodes.append({key: names[value] if key in {"lhs", "rhs", "selector"} else value
                          for key, value in node.items() if key != "name"})
            names[node["name"]] = f"node{index}"
        return nodes, [names[name] for name in relation["public_outputs"]]

    def test_every_language_module_enters_compiler_identity(self) -> None:
        modules = set((S31_SOURCE_ROOT / "python/language").glob("*.py"))
        self.assertTrue(modules)
        self.assertLessEqual(modules, set(TEXT_FRONTEND_SOURCES))

    def test_higher_order_application_has_only_the_two_manual_multiplications(self) -> None:
        path = S31_SOURCE_ROOT / "examples/arithmetic/functional_square4.s31"
        relation, _ = compile_file(path)
        manual, _ = compile_text("""circuit functional_square4(public x: [m31; 4]) -> public [m31; 4] {
            let once = x .* x;
            let result = once .* once;
            result
        }""")
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "mul"])
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         [node["op"] for node in manual["nodes"]])
        self.assertEqual(len(relation["inputs"]), len(manual["inputs"]))
        assignment = json.loads(path.with_suffix(".valid.json").read_text())
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_lexical_capture_survives_shadowing_without_a_closure_witness(self) -> None:
        relation, _ = compile_text("""fn make_adder(capture: [m31; 1])
            -> Fn([m31; 1]) -> [m31; 1] {
            fun(v: [m31; 1]) -> [m31; 1] => v + capture
        }
        circuit closure(public x: [m31; 1]) -> public [m31; 1] {
            let add_x = make_adder(x);
            let x = splat<1>(7_m31) in add_x(x)
        }""")
        self.assertEqual(relation["nodes"],
                         [{"name": "_s31_0", "op": "add_const", "lhs": "x", "constant": 7}])
        assignment = {"public_inputs": {"x": [5]}, "private_inputs": {},
                      "public_outputs": {"_s31_0": [12]}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_function_values_cannot_cross_circuit_boundary(self) -> None:
        examples = (
            ("circuit bad(public f: Fn([m31; 1]) -> [m31; 1]) -> public [m31; 1] { splat<1>(0_m31) }",
             "circuit inputs must be first-order"),
            ("circuit bad() -> public Fn([m31; 1]) -> [m31; 1] { fun(x: [m31; 1]) -> [m31; 1] => x }",
             "circuit output must be a first-order"),
            ("circuit bad(public x: [m31; 1]) -> public [m31; 1] { let f = fun(y: [m31; 2]) -> [m31; 2] => y; f(x) }",
             "function value argument 1 expects"),
            ("circuit bad(public x: [m31; 1]) -> public [m31; 1] { let f = fun(y: [m31; 1]) -> [m31; 2] => y; f(x) }",
             "function value result does not match"),
        )
        for source, message in examples:
            with self.subTest(message=message), self.assertRaisesRegex(SourceError, message):
                compile_text(source)

    def test_lexical_binding_shadows_a_top_level_function(self) -> None:
        source = """fn square(x: [m31; 1]) -> [m31; 1] { x .* x }
        circuit shadow(public x: [m31; 1]) -> public [m31; 1] {
            let square = x in square(x)
        }"""
        with self.assertRaisesRegex(SourceError, "cannot call non-function value square"):
            compile_text(source)

    def test_expression_let_preserves_iterate_chip_shape(self) -> None:
        source = """fn step(v: [m31; 4]) -> [m31; 4] {
            let squared = v .* v in squared + splat<4>(7_m31)
        }
        circuit repeated(public x: [m31; 4]) -> public [m31; 4] {
            iterate<16>(step, x)
        }"""
        relation, _ = compile_text(source)
        self.assertEqual(relation["nodes"], [{
            "name": "_s31_0", "op": "repeat", "lhs": "x", "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 7}],
        }])

    def test_static_beta_reduction_preserves_operation_graph(self) -> None:
        expressions = (
            "a + b", "a .* b", "std::math::sub(a, b)",
            "std::math::square(a) + b", "std::math::pow<3>(a) + b",
            "std::math::sum([a, b, a])",
        )
        for body in expressions:
            with self.subTest(body=body):
                functional, _ = compile_text(f"""
                    fn apply(f: Fn([m31; 2], [m31; 2]) -> [m31; 2],
                             x: [m31; 2], y: [m31; 2]) -> [m31; 2] {{ f(x, y) }}
                    circuit p(public x: [m31; 2], public y: [m31; 2])
                        -> public [m31; 2] {{
                        let f = fun(a: [m31; 2], b: [m31; 2]) -> [m31; 2] => {body};
                        apply(f, x, y)
                    }}""")
                manual, _ = compile_text(f"""circuit p(public x: [m31; 2],
                    public y: [m31; 2]) -> public [m31; 2] {{
                    let a = x;
                    let b = y;
                    {body}
                }}""")
                self.assertEqual(self.operation_graph(functional), self.operation_graph(manual))

    def test_formal_captured_square_example_matches_text_lowering(self) -> None:
        functional, _ = compile_text("""circuit captured(public x: [m31; 1]) -> public [m31; 1] {
            let saved = x in
            let f = fun(y: [m31; 1]) -> [m31; 1] => y .* y + saved in
            f(saved)
        }""")
        manual, _ = compile_text("""circuit captured(public x: [m31; 1]) -> public [m31; 1] {
            x .* x + x
        }""")
        self.assertEqual(self.operation_graph(functional), self.operation_graph(manual))
        self.assertEqual([node["op"] for node in functional["nodes"]], ["mul", "add"])


if __name__ == "__main__":
    unittest.main()
