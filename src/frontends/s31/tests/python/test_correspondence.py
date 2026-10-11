"""Bounded independent parser and ambiguous-input rejection controls."""

from __future__ import annotations

import sys
import copy
import hashlib
import struct
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31.parents[2] / "scripts"))

from package.correspondence import (DIRECT_COLUMN_IDS, M31_MODULUS,
                                    UnsupportedFragment, _check_constant_island,
                                    _qm_mul, check_gate_topology, parse_source,
                                    read_canonical_json)
from package.direct_gate_schedule import constant_and_padding, exact_direct_gate_schedule
from text_frontend import compile_text
from export_s31_direct_gate_bridge import render_bridge


class CorrespondenceParserTests(unittest.TestCase):
    def test_lean_export_rejects_topology_changed_after_admission(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory)
            source = b"bounded source fixture"
            relation = b"bounded normalized fixture"
            original_topology = b'{"n_vars":512}'
            (package / "source.s31").write_bytes(source)
            (package / "source.s31.json").write_bytes(relation)
            topology_path = package / "gate-topology.json"
            topology_path.write_bytes(original_topology)
            checked = {
                "source_sha256": hashlib.sha256(source).hexdigest(),
                "relation_sha256": hashlib.sha256(relation).hexdigest(),
                "gate_topology_sha256": hashlib.sha256(original_topology).hexdigest(),
            }

            def admitted_then_changed(_: Path) -> dict:
                topology_path.write_bytes(b'{"n_vars":511}')
                return checked

            with patch("export_s31_direct_gate_bridge.check_package",
                       side_effect=admitted_then_changed):
                with self.assertRaisesRegex(ValueError, "checked topology digest"):
                    render_bridge(package)

    def test_add_mul_and_shared_let_match_production_relation(self) -> None:
        cases = (
            "let result = x + x; result",
            "let square = x .* x; let result = square .* square; result",
            "let a = x + x; let b = x .* a; let result = a + b; result",
        )
        for body in cases:
            source = ("circuit arithmetic(public x: [m31; 4]) -> public "
                      f"[m31; 4] {{ {body} }}")
            with self.subTest(body=body):
                independent, syntax = parse_source(source.encode())
                produced, _ = compile_text(source)
                self.assertEqual(independent, produced)
                self.assertEqual(len(syntax["instructions"]), len(produced["nodes"]))

    def test_rejects_forward_duplicate_and_unsupported_syntax(self) -> None:
        cases = (
            "let result = later .* x; let later = x .* x; result",
            "let result = x .* x; let result = result + x; result",
            "let result = (x .* x); result",
            "let result = std::math::pow<2>(x); result",
            "let unused = x .* x; x",
            "let a = x + x; let b = a .* x; b",
            "let a = x + x; let b = x + x; b",
        )
        for body in cases:
            source = ("circuit arithmetic(public x: [m31; 4]) -> public "
                      f"[m31; 4] {{ {body} }}")
            with self.subTest(body=body), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())

    def test_bounded_source_bytes_and_tokens(self) -> None:
        source = ("circuit square(public x: [m31; 4]) -> public [m31; 4] "
                  "{ let y = x .* x; y }")
        with self.assertRaisesRegex(UnsupportedFragment, "byte limit"):
            parse_source((source + "\n//" + "a" * 16_384).encode())
        with self.assertRaisesRegex(UnsupportedFragment, "token limit"):
            parse_source((source + " x" * 257).encode())

    def test_duplicate_keys_and_noncanonical_json_reject(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ambiguous.json"
            for data in ('{"op":"mul","op":"add"}\n',
                         '{"op": NaN}\n', '{ "op": "mul" }\n'):
                with self.subTest(data=data):
                    path.write_text(data)
                    with self.assertRaises(ValueError):
                        read_canonical_json(path)

    def test_value_free_gate_replay_and_resealed_wrong_selector(self) -> None:
        source = ("circuit square(public x: [m31; 4]) -> public [m31; 4] "
                  "{ let y = x .* x; y }")
        _, syntax = parse_source(source.encode())
        topo = {
            "schema": "s31-direct-gate-topology-v1", "program_sha256": "a" * 64,
            "n_vars": 46, "output": [2, *range(3, 11)],
            "add": [
                {"in0": 11, "in1": 19, "out": 22},
                {"in0": 22, "in1": 20, "out": 23},
                {"in0": 23, "in1": 21, "out": 24},
                *({"in0": wire, "in1": 0, "out": index}
                  for index, wire in enumerate((11, 12, 13, 14, 26, 30, 31, 32), 3)),
                *({"in0": 1, "in1": 1, "out": wire} for wire in range(36, 42)),
            ],
            "sub": [],
            "mul": [
                *({"in0": 15 + lane, "in1": 11 + lane, "out": 18 + lane}
                  for lane in range(1, 4)),
                *({"in0": 26 + lane, "in1": 32 + lane, "out": 29 + lane}
                  for lane in range(1, 4)),
            ],
            "pointwise_mul": [
                {"in0": 24, "in1": 24, "out": 25},
                *({"in0": 25, "in1": (1 if lane == 0 else 15 + lane), "out": 26 + lane}
                  for lane in range(4)),
                *({"in0": wire, "in1": 1, "out": wire} for wire in range(11, 15)),
            ],
            "permutation_ends": [], "permutation_inputs": [],
            "permutation_outputs": [], "first_permutation_row": 32,
        }
        produced = {gate["out"] for kind in ("add", "sub", "mul", "pointwise_mul")
                    for gate in topo[kind]}
        for missing in sorted(set(range(topo["n_vars"])) - produced):
            topo["add"].append({"in0": 0, "in1": 0, "out": missing})
        current_rows = sum(len(topo[kind]) for kind in ("add", "sub", "mul", "pointwise_mul"))
        while current_rows < 64:
            topo["add"].append({"in0": 1, "in1": 1, "out": topo["n_vars"]})
            topo["n_vars"] += 1
            current_rows += 1
        topo["first_permutation_row"] = current_rows

        def reseal(value: dict) -> dict:
            uses = [0] * value["n_vars"]
            for kind in ("add", "sub", "mul", "pointwise_mul"):
                for gate in value[kind]:
                    uses[gate["in0"]] += 1
                    uses[gate["in1"]] += 1
            for address in value["output"]:
                uses[address] += 1
            rows = []
            for index, kind in enumerate(("add", "sub", "mul", "pointwise_mul")):
                for gate in value[kind]:
                    rows.append([*(int(i == index) for i in range(4)),
                                 gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]])
            value["columns"] = [{"id": name, "values": [row[index] for row in rows]}
                                for index, name in enumerate(DIRECT_COLUMN_IDS)]
            return {"preprocessed_columns": [{
                "id": column["id"], "commitment_index": index, "rows": len(rows),
                "log_size": len(rows).bit_length() - 1,
                "values_sha256": hashlib.sha256(b"".join(
                    struct.pack("<I", word) for word in column["values"])).hexdigest(),
            } for index, column in enumerate(value["columns"])]}

        component = reseal(topo)
        report = {"padded": {"qm31_ops": 64}, "trace_log_size": 6}

        def checked(value: dict, declaration: dict) -> list[dict]:
            # This synthetic fixture covers selector/ABI replay. Native
            # acceptance checks the exact fixed constant and padding plan.
            source_adds = sum(node["op"] == "add" for node in syntax["instructions"])
            synthetic = ({"add": value["add"][3 + source_adds + 8:],
                          "sub": value["sub"], "mul": value["mul"][6:]},
                         value["n_vars"], report["padded"]["qm31_ops"])
            synthetic_exact = ({kind: value[kind] for kind in
                                ("add", "sub", "mul", "pointwise_mul")},
                               value["n_vars"], report["padded"]["qm31_ops"],
                               [{"id": 1, "op": "mul", **value["pointwise_mul"][0]}])
            with (patch("package.correspondence._check_constant_island"),
                  patch("package.correspondence.constant_and_padding", return_value=synthetic),
                  patch("package.correspondence.exact_direct_gate_schedule",
                        return_value=synthetic_exact)):
                return check_gate_topology(syntax, value, declaration, report, "a" * 64)

        self.assertEqual(checked(topo, component)[0]["op"], "mul")
        plus_source = ("circuit sum(public x: [m31; 4]) -> public [m31; 4] "
                       "{ let y = x + x; y }")
        _, plus_syntax = parse_source(plus_source.encode())
        plus = copy.deepcopy(topo)
        plus["add"].insert(3, plus["pointwise_mul"].pop(0))
        plus["program_sha256"] = "b" * 64
        plus_component = reseal(plus)
        plus_synthetic = ({"add": plus["add"][12:], "sub": plus["sub"],
                           "mul": plus["mul"][6:]}, plus["n_vars"], 64)
        plus_exact = ({kind: plus[kind] for kind in
                       ("add", "sub", "mul", "pointwise_mul")},
                      plus["n_vars"], 64,
                      [{"id": 1, "op": "add", **plus["add"][3]}])
        with (patch("package.correspondence._check_constant_island"),
              patch("package.correspondence.constant_and_padding", return_value=plus_synthetic),
              patch("package.correspondence.exact_direct_gate_schedule",
                    return_value=plus_exact)):
            self.assertEqual(check_gate_topology(plus_syntax, plus, plus_component,
                                                 report, "b" * 64)[0]["op"], "add")
        forged = copy.deepcopy(topo)
        forged["pointwise_mul"].pop(0)
        forged["add"].insert(3, {"in0": 24, "in1": 24, "out": 25})
        forged["pointwise_mul"].append(forged["add"].pop())
        # The forged compiler can reseal every column digest. It still cannot
        # make an add gate satisfy the independent source operation check.
        forged["first_permutation_row"] = 64
        forged_component = reseal(forged)
        with self.assertRaisesRegex(ValueError, "unexpected pointwise gates|source gate selector or operands"):
            checked(forged, forged_component)
        wrong_operand = copy.deepcopy(topo)
        wrong_operand["pointwise_mul"][0]["in1"] = 11
        wrong_operand_component = reseal(wrong_operand)
        with self.assertRaisesRegex(ValueError, "source gate selector or operands"):
            checked(wrong_operand, wrong_operand_component)
        hidden_gate = copy.deepcopy(topo)
        hidden_gate["add"][-1]["in0"] = 25
        hidden_component = reseal(hidden_gate)
        with self.assertRaisesRegex(ValueError, "extra native gate depends on source"):
            checked(hidden_gate, hidden_component)

    def test_independent_constant_and_padding_schedule(self) -> None:
        for n_nodes in (1, 2, 16):
            with self.subTest(n_nodes=n_nodes):
                gates, n_vars, rows = constant_and_padding(n_nodes)
                self.assertEqual((n_vars, rows), (512, 512))
                self.assertEqual(len(gates["sub"]), 1)
                self.assertEqual(len(gates["mul"]), 21)
                self.assertEqual(len(gates["add"]), 465 - n_nodes)
                self.assertEqual(gates["add"][-1]["in0"], 1)
                self.assertEqual(gates["add"][-1]["in1"], 1)
                syntax = {"instructions": [
                    {"id": index, "op": "mul" if index % 2 else "add",
                     "lhs": 0, "rhs": index - 1}
                    for index in range(1, n_nodes + 1)], "output": n_nodes}
                full, total_vars, total_rows, source = exact_direct_gate_schedule(syntax)
                self.assertEqual((total_vars, total_rows), (512, 512))
                self.assertEqual(full["add"][0], {"in0": 11, "in1": 17, "out": 18})
                self.assertEqual(full["mul"][0], {"in0": 15, "in1": 12, "out": 17})
                self.assertEqual(source[0]["out"], 23)
                self.assertEqual(source[-1]["out"], 22 + n_nodes)
                self.assertEqual(full["pointwise_mul"][-4:], [
                    {"in0": address, "in1": 1, "out": address}
                    for address in range(11, 15)])

    def test_independent_qm31_constant_derivation(self) -> None:
        i = (0, 1, 0, 0)
        minus_i = (0, M31_MODULUS - 1, 0, 0)
        self.assertEqual(_qm_mul(i, minus_i), (1, 0, 0, 0))
        self.assertEqual(_qm_mul((0, 0, 1, 0), (0, 0, 1, 0)), (2, 1, 0, 0))
        inv_five = pow(5, M31_MODULUS - 2, M31_MODULUS)
        self.assertEqual(_qm_mul((0, 0, 1, 0),
                                 (0, 0, 2 * inv_five % M31_MODULUS,
                                  -inv_five % M31_MODULUS)), (1, 0, 0, 0))
        self.assertEqual(_qm_mul((0, 0, 0, 1),
                                 (0, 0, -inv_five % M31_MODULUS,
                                  -2 * inv_five % M31_MODULUS)), (1, 0, 0, 0))
        _check_constant_island([{"in0": 1, "in1": 1, "out": 3}], [], [], [], [])
        _check_constant_island([], [], [], [1], [])
        with self.assertRaisesRegex(ValueError, "basis"):
            _check_constant_island([], [], [], [2], [])
        with self.assertRaisesRegex(ValueError, "contradictory"):
            _check_constant_island([{"in0": 1, "in1": 1, "out": 1}], [], [], [], [])
        with self.assertRaisesRegex(ValueError, "underived"):
            _check_constant_island([{"in0": 3, "in1": 1, "out": 4}], [], [], [], [])


if __name__ == "__main__":
    unittest.main()
