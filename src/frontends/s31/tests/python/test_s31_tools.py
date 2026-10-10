"""Checks that agent-facing measurements distinguish proving from PoW time."""

import sys
import json
from pathlib import Path
S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

import unittest
from tempfile import TemporaryDirectory
from pathlib import Path
from unittest.mock import patch

import s31


class ProverLogTests(unittest.TestCase):
    def test_library_lock_and_compiler_identity_cover_implementations(self) -> None:
        lock = s31.standard_library_lock(True)
        expected = {
            "s31_stdlib.py", "s31_mathlib.py",
            "library/__init__.py", "library/stdlib.py", "library/math.py",
            "library/addition_chains.py",
        }
        discovered = {
            f"library/{path.relative_to(S31_SOURCE_ROOT / 'python/library').as_posix()}"
            for path in (S31_SOURCE_ROOT / "python/library").rglob("*.py")
        }
        self.assertEqual(discovered, expected - {"s31_stdlib.py", "s31_mathlib.py"})
        self.assertEqual(set(s31.LIBRARY_SOURCE_FILES), expected)
        self.assertEqual(set(lock["sources"]), expected)
        self.assertEqual(lock["version"], 1)
        for name in expected:
            path = S31_SOURCE_ROOT / "python" / name
            self.assertEqual(lock["sources"][name], s31.file_hash(path))
            self.assertIn(path, s31.TEXT_FRONTEND_SOURCES)

        package_files = set((S31_SOURCE_ROOT / "python/package").glob("*.py"))
        self.assertEqual({path.name for path in package_files},
                     {"__init__.py", "context.py", "build.py", "verify.py", "trust.py",
                         "correspondence.py", "direct_gate_schedule.py",
                         "manifest_digest.py"})
        self.assertTrue(package_files.issubset(s31.TEXT_FRONTEND_SOURCES))
        runtime_files = set((S31_SOURCE_ROOT / "python/runtime").glob("*.py"))
        self.assertEqual({path.name for path in runtime_files},
                         {"__init__.py", "trials.py", "folds.py", "cost_model.py"})
        self.assertTrue(runtime_files.issubset(s31.TEXT_FRONTEND_SOURCES))
        cli_files = set((S31_SOURCE_ROOT / "python/cli").glob("*.py"))
        self.assertEqual({path.name for path in cli_files},
                         {"__init__.py", "parser.py", "commands.py"})
        self.assertTrue(cli_files.issubset(s31.TEXT_FRONTEND_SOURCES))

    def test_pins_the_runtime_stage_format(self) -> None:
        log = (
            "S31 demo: proof=123 bytes, witness=0.000200s, setup=0.000500s, "
            "prove=0.040000s, total through verification=0.050000s\n"
            "S31 demo proof: interaction_pow=0.003000s fri_pow=0.032000s\n"
        )
        stages = s31.prover_stages(log)
        self.assertIsNotNone(stages)
        non_pow = stages.pop("prove_excluding_pow_seconds")
        self.assertAlmostEqual(non_pow, 0.005)
        self.assertAlmostEqual(stages.pop("runtime_other_seconds"), 0.0093)
        self.assertEqual(stages, {
            "witness_seconds": 0.0002,
            "setup_seconds": 0.0005,
            "prove_seconds": 0.04,
            "interaction_pow_seconds": 0.003,
            "fri_pow_seconds": 0.032,
            "total_through_verification_seconds": 0.05,
        })

    def test_missing_pow_timers_do_not_imply_zero_pow(self) -> None:
        log = "witness=0.001s, setup=0.002s, prove=0.030s"
        stages = s31.prover_stages(log)
        self.assertIsNotNone(stages)
        self.assertNotIn("prove_excluding_pow_seconds", stages)
        self.assertIsNone(s31.prover_stages("proof accepted"))

    def test_inconsistent_pow_timers_fail_closed(self) -> None:
        with self.assertRaisesRegex(ValueError, "PoW stages exceed"):
            s31.prover_stages("witness=0.001s, setup=0.002s, prove=0.010s\n"
                              "interaction_pow=0.010000s fri_pow=0.010000s")

    def test_distinct_assignment_detection_ignores_json_formatting(self) -> None:
        with TemporaryDirectory() as directory:
            first = Path(directory) / "first.json"
            second = Path(directory) / "second.json"
            changed = Path(directory) / "changed.json"
            first.write_text('{"public_inputs":{"x":[1]},"public_outputs":{"y":[2]}}')
            second.write_text('{"public_outputs": {"y": [2]}, "public_inputs": {"x": [1]}}\n')
            changed.write_text('{"public_inputs":{"x":[1]},"public_outputs":{"y":[3]}}')
            self.assertEqual(s31.assignment_digest(first), s31.assignment_digest(second))
            self.assertNotEqual(s31.assignment_digest(first), s31.assignment_digest(changed))

    def test_inspection_wrappers_verify_then_report_source_equations(self) -> None:
        with TemporaryDirectory() as directory:
            package = Path(directory)
            relation = {
                "name": "square", "inputs": [{"name": "x", "kind": "m31", "length": 1,
                                               "visibility": "public"}],
                "nodes": [{"name": "result", "op": "mul", "lhs": "x", "rhs": "x"}],
                "assertions": [], "public_outputs": ["result"],
            }
            source_map = {"name": "result", "canonical_id": 1}
            for component in ("qm31", "m31_to_u32", "eq", "triple_xor", "blake_g"):
                source_map[f"{component}_start"] = 0
                source_map[f"{component}_end"] = 1 if component == "qm31" else 0
            cost = {
                "name": "square", "profile": "direct-m31-v4", "chip": None,
                "raw": {"qm31_ops": 1}, "padded": {"qm31_ops": 16},
                "preprocessed_cells": 128, "preprocessed_columns": 8,
                "canonical_ir_sha256": "0" * 64, "source_map": [source_map],
            }
            (package / "source.s31.json").write_text(json.dumps(relation))
            (package / "cost-report.json").write_text(json.dumps(cost))
            with patch.object(s31, "verify_package", return_value={}) as verifier:
                explained = s31.explain(package)
                equations = s31.equations(package)
            self.assertEqual(verifier.call_count, 2)
            self.assertEqual(explained["nodes"][0]["gate_rows"]["qm31"], 1)
            self.assertEqual(equations["nodes"][0]["field_equations"],
                             ["result[j] - x[j] * x[j] = 0"])


if __name__ == "__main__":
    unittest.main()
