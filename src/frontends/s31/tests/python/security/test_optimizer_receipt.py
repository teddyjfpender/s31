"""Versioned package binding for the native pure-field optimizer audit."""

import json
import sys
import tempfile
import unittest
from pathlib import Path

PYTHON_ROOT = Path(__file__).resolve().parents[3] / "python"
sys.path.insert(0, str(PYTHON_ROOT))

from package.optimizer_receipt import (ARTIFACT, SCHEMA, LEGACY_SCHEMA,
                                       eligible, validate, verify_artifact)


class OptimizerReceiptTests(unittest.TestCase):
    def setUp(self):
        self.source = {
            "version": 1, "name": "optimizer_test", "inputs": [
                {"name": "x", "kind": "m31", "length": 1, "visibility": "private"}],
            "nodes": [{"name": "y", "op": "add_const", "lhs": "x", "constant": 3}],
            "assertions": [], "public_outputs": ["y"],
        }
        self.program = "a" * 64
        self.ir = "b" * 64
        self.receipt = {
            "schema": SCHEMA, "program_sha256": self.program,
            "canonical_ir_sha256": self.ir, "source_nodes": 1,
            "canonical_nodes": 2, "aliases": 0,
        }

    def test_fragment_and_identity(self):
        self.assertTrue(eligible(self.source))
        validate(self.receipt, self.source, self.program, self.ir)
        for changed in (
            {**self.receipt, "canonical_ir_sha256": "c" * 64},
            {**self.receipt, "program_sha256": "c" * 64},
            {**self.receipt, "aliases": 1},
            {**self.receipt, "extra": 0},
        ):
            with self.subTest(changed=changed):
                with self.assertRaises(ValueError):
                    validate(changed, self.source, self.program, self.ir)
        self.assertFalse(eligible({**self.source, "version": 2}))
        self.assertTrue(eligible({**self.source, "nodes": [
            {"name": "y", "op": "inv", "lhs": "x"}]}))
        self.assertTrue(eligible({**self.source, "nodes": [
            {"name": "y", "op": "is_zero", "lhs": "x"}]}))
        self.assertTrue(eligible({**self.source, "nodes": [
            {"name": "y", "op": "select", "lhs": "x", "rhs": "x",
             "selector": "x"}]}))
        self.assertFalse(eligible({**self.source, "nodes": [
            {"name": "y", "op": "hash_blake2s", "lhs": "x"}]}))
        validate({**self.receipt, "schema": LEGACY_SCHEMA}, self.source,
                 self.program, self.ir)
        with self.assertRaises(ValueError):
            validate({**self.receipt, "schema": LEGACY_SCHEMA},
                     {**self.source, "nodes": [{"name": "y", "op": "inv", "lhs": "x"}]},
                     self.program, self.ir)

    def test_manifest_requires_declared_artifact_and_key_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ARTIFACT).write_text(json.dumps(self.receipt))
            manifest = {
                "optimizer_correspondence_schema": SCHEMA,
                "program_sha256": self.program, "canonical_ir_sha256": self.ir,
                "artifacts": {ARTIFACT: "unused in this local validator"},
                "lowering": "direct-gate",
            }
            key = {"canonical_ir_sha256": self.ir}
            self.assertTrue(verify_artifact(root, manifest, key, self.source))
            with self.assertRaises(ValueError):
                verify_artifact(root, {**manifest, "artifacts": {}}, key, self.source)
            with self.assertRaises(ValueError):
                verify_artifact(root, manifest, {"canonical_ir_sha256": "c" * 64}, self.source)
            with self.assertRaises(ValueError):
                verify_artifact(root, {**manifest, "lowering": "sha-joint"}, key, self.source)
            with self.assertRaises(ValueError):
                verify_artifact(root, {**manifest,
                                       "optimizer_correspondence_schema": LEGACY_SCHEMA},
                                key, self.source)


if __name__ == "__main__":
    unittest.main()
