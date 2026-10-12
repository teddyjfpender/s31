"""Differential audit of real functional source and exact relation bytes."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
CHECKER = FORMAL / ".lake/build/bin/s31-source-function-check"
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.correspondence import PLAIN_BUILTIN_NAMES, SOURCE_KEYWORDS  # noqa: E402
from package.source_relation_fragment import parse_source_fragment  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode()


def canonical_ir(relation: dict) -> bytes:
    """Independent one-gate Zig LegacyNode layout, including null fields."""
    fields = ("tag", "kind", "length", "lhs", "rhs", "constant", "rounds",
              "body", "input_name", "visibility")

    def node(**values: object) -> dict:
        return {field: values.get(field) for field in fields}

    inputs = relation["inputs"]
    names = {item["name"]: index for index, item in enumerate(inputs)}
    gate = relation["nodes"][0]
    lhs, rhs = names[gate["lhs"]], names[gate["rhs"]]
    if gate["op"] in {"add", "mul"}:
        lhs, rhs = sorted((lhs, rhs))
    nodes = [node(tag="input", kind="m31", length=item["length"],
                  input_name=item["name"], visibility=item["visibility"])
             for item in inputs]
    nodes.append(node(tag=gate["op"], kind="m31", length=inputs[0]["length"],
                      lhs=lhs, rhs=rhs))
    ir = {"version": 1, "nodes": nodes, "assertions": [],
          "public_outputs": [{"name": relation["public_outputs"][0], "id": 2}]}
    return json.dumps(ir, separators=(",", ":"), ensure_ascii=True).encode()


def source_for(length: int, operator: str, *, reverse_body: bool = False,
               reverse_call: bool = False) -> str:
    left, right = ("y", "x") if reverse_body else ("x", "y")
    first, second = ("b", "a") if reverse_call else ("a", "b")
    return (f"fn combine(x: [m31; {length}], y: [m31; {length}]) "
            f"-> [m31; {length}] {{ {left} {operator} {right} }}\n"
            f"circuit calc(private a: [m31; {length}], private b: [m31; {length}]) "
            f"-> public [m31; {length}] {{ let out = combine({first}, {second}); out }}\n")


def invoke(source: bytes, relation: bytes,
           canonical_bytes: bytes | None = None) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "source.s31"
        relation_path = Path(directory) / "source.s31.json"
        source_path.write_bytes(source)
        relation_path.write_bytes(relation)
        args = [str(CHECKER), str(source_path), str(relation_path)]
        if canonical_bytes is not None:
            canonical_path = Path(directory) / "canonical-ir.json"
            canonical_path.write_bytes(canonical_bytes)
            args.append(str(canonical_path))
        return subprocess.run(args,
                              capture_output=True, text=True, check=False)


class SourceFunctionCheckTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not CHECKER.is_file():
            raise RuntimeError("build first: cd formal/s31 && lake build s31-source-function-check")

    def test_all_lanes_operations_and_noncommutative_orders(self) -> None:
        for length in range(1, 9):
            for operator, named_op in (("+", "add"), ("-", "sub"), (".*", "mul")):
                for reverse_body, reverse_call in ((False, False), (True, False),
                                                    (False, True), (True, True)):
                    with self.subTest(length=length, operator=operator,
                                      reverse_body=reverse_body, reverse_call=reverse_call):
                        source = source_for(length, operator, reverse_body=reverse_body,
                                            reverse_call=reverse_call)
                        relation, _ = compile_text(source)
                        self.assertEqual(relation, parse_source_fragment(source.encode()))
                        result = invoke(source.encode(), canonical(relation),
                                        canonical_ir(relation))
                        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                        summary = json.loads(result.stdout)
                        self.assertEqual(summary["operation"], named_op)
                        self.assertEqual(summary["length"], length)
                        self.assertEqual(summary["packed_rows"], (length + 3) // 4)
                        self.assertTrue(summary["canonical_ir_checked"])
                        self.assertEqual(relation["nodes"][0]["lhs"],
                                         "b" if reverse_body != reverse_call else "a")
                        self.assertEqual(relation["nodes"][0]["rhs"],
                                         "a" if reverse_body != reverse_call else "b")

    def test_mutated_source_relation_and_serialization_fail(self) -> None:
        source = source_for(5, "-")
        relation, _ = compile_text(source)
        good = canonical(relation)
        self.assertEqual(invoke(source.encode(), good).returncode, 0)
        good_ir = canonical_ir(relation)
        self.assertEqual(invoke(source.encode(), good, good_ir).returncode, 0)
        for changed_ir in (good_ir + b" ",
                           good_ir.replace(b'"tag":"sub"', b'"tag":"add"'),
                           good_ir.replace(b'"lhs":0', b'"lhs":1'),
                           good_ir.replace(b'"id":2', b'"id":1')):
            with self.subTest(canonical=changed_ir[-65:]):
                result = invoke(source.encode(), good, changed_ir)
                self.assertEqual(result.returncode, 1, result.stderr + result.stdout)

        mutations = []
        for field, value in (("op", "add"), ("lhs", "b"), ("rhs", "a"),
                             ("name", "forged")):
            changed = copy.deepcopy(relation)
            changed["nodes"][0][field] = value
            mutations.append((source.encode(), canonical(changed)))
        changed = copy.deepcopy(relation)
        changed["inputs"][1]["length"] = 4
        mutations.append((source.encode(), canonical(changed)))
        mutations.extend([
            (source.replace("x - y", "y - x").encode(), good),
            (source.replace("combine(a, b)", "combine(b, a)").encode(), good),
            (source.replace("[m31; 5] { x - y }", "[m31; 4] { x - y }").encode(), good),
            (source.encode(), good + b" "),
            (source.encode(), good.replace(b'"op": "sub"', b'"op":"sub"')),
            (source.encode() + b" trailing", good),
            (source.encode() + b" // \xff", good),
        ])
        for changed_source, changed_relation in mutations:
            with self.subTest(source=changed_source[-45:], relation=changed_relation[-60:]):
                result = invoke(changed_source, changed_relation)
                self.assertEqual(result.returncode, 1, result.stderr + result.stdout)
                self.assertFalse(json.loads(result.stdout)["accepted"])

    def test_reserved_names_and_helper_shadowing_fail(self) -> None:
        source = source_for(5, "-")
        relation, _ = compile_text(source)
        for name in sorted(PLAIN_BUILTIN_NAMES | SOURCE_KEYWORDS):
            changed_source = source.replace("circuit calc(", f"circuit {name}(", 1)
            changed_relation = {**relation, "name": name}
            with self.subTest(name=name):
                result = invoke(changed_source.encode(), canonical(changed_relation))
                self.assertEqual(result.returncode, 1, result.stderr + result.stdout)
        shadow = source.replace("fn combine(x:", "fn combine(combine:")
        self.assertEqual(invoke(shadow.encode(), canonical(relation)).returncode, 1)
        long_name = "a" * 129
        long_source = source.replace("circuit calc(", f"circuit {long_name}(", 1)
        self.assertEqual(invoke(long_source.encode(), canonical(relation)).returncode, 1)


if __name__ == "__main__":
    unittest.main()
