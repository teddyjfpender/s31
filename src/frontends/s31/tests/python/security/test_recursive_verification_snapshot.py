"""Recursive proof admission must execute the checked verifier bytes.

The package directory is adversarial input. Validation followed by execution
from that same mutable directory admits a replacement binary after the check.
Each public recursive verification command must instead execute a private
snapshot that was checked as one unit.
"""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from cli.commands import dispatch  # noqa: E402
from cli.parser import make_parser  # noqa: E402


class RecursiveVerificationSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-recursive-snapshot-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name) / "package"
        (self.package / "bin").mkdir(parents=True)
        self.binary = self.package / "bin/s31-example-native-verifier"
        self.binary.write_bytes(b"sealed verifier")
        self.proof = Path(temporary.name) / "proof.bin"
        self.statement = Path(str(self.proof) + ".statement.json")

    def test_recursive_verification_uses_admitted_snapshot(self) -> None:
        cases = (
            ("verify-recursive", "gate", False),
            ("verify-recursive-next", "sparse-wide-gate", False),
            ("verify-fold", "gate", False),
            ("verify-state-fold", "gate", True),
        )
        for command, lowering, state_fold in cases:
            with self.subTest(command=command):
                self.binary.write_bytes(b"sealed verifier")
                self.proof.write_bytes(b"sealed proof")
                self.statement.write_bytes(b"sealed statement")
                arguments = make_parser().parse_args(
                    (command, str(self.package), str(self.proof)))
                manifest = {
                    "name": "example",
                    "lowering": lowering,
                    "artifacts": ({"state-fold-verification-key.json": "digest"}
                                  if state_fold else {}),
                }

                def admit(_snapshot: Path) -> dict:
                    self.proof.write_bytes(b"replacement proof during admission")
                    self.statement.write_bytes(b"replacement statement during admission")
                    return manifest

                def invoke(executable: str, native_command: str, proof: str,
                           statement: str, *flags: str) -> str:
                    selected = Path(executable)
                    self.assertNotEqual(selected, self.binary)
                    self.assertEqual(selected.read_bytes(), b"sealed verifier")
                    self.assertNotEqual(Path(proof), self.proof)
                    self.assertNotEqual(Path(statement), self.statement)
                    self.assertEqual(Path(proof).read_bytes(), b"sealed proof")
                    self.assertEqual(Path(statement).read_bytes(), b"sealed statement")
                    self.binary.write_bytes(b"replacement")
                    self.assertEqual(selected.read_bytes(), b"sealed verifier")
                    return "accepted\n"

                with patch("cli.commands.verify_package", return_value=manifest), \
                        patch("package.trust.verify_package", side_effect=admit), \
                        patch("cli.commands.invoke", side_effect=invoke), \
                        contextlib.redirect_stdout(io.StringIO()) as output:
                    dispatch(arguments)
                self.assertEqual(output.getvalue(), "accepted\n")

    def test_recursive_statement_limit_precedes_package_admission(self) -> None:
        self.proof.write_bytes(b"sealed proof")
        self.statement.write_bytes(b" " * 4097)
        args = make_parser().parse_args(
            ("verify-recursive", str(self.package), str(self.proof)))
        with patch("package.trust.verify_package") as admit, \
                patch("cli.commands.invoke") as native:
            with self.assertRaisesRegex(ValueError, "exceeds 4096 bytes"):
                dispatch(args)
        admit.assert_not_called()
        native.assert_not_called()

    def test_chain_audit_reports_exact_verified_checkpoint_bytes(self) -> None:
        self.proof.write_bytes(b"sealed proof")
        statement = Path(str(self.proof) + ".statement.json")
        original = {
            "schema": "s31-fixed-fold-statement-v3",
            "step": 0,
            "leaf_public_words": [1] * 8,
            "base_public_words": [2] * 8,
            "fold_preprocessed_root": "fixed root",
        }
        statement.write_text(json.dumps(original))
        args = make_parser().parse_args(
            ("audit-fold-chain", str(self.package), str(self.proof)))
        manifest = {"name": "example", "lowering": "gate", "artifacts": {}}

        def native(executable: str, command: str, proof: str, claim: str) -> str:
            self.assertEqual(command, "fold-verify")
            self.assertNotEqual(Path(executable), self.binary)
            self.assertEqual(Path(executable).read_bytes(), b"sealed verifier")
            self.assertNotEqual(Path(proof), self.proof)
            self.assertNotEqual(Path(claim), statement)
            self.assertEqual(Path(proof).read_bytes(), b"sealed proof")
            self.assertEqual(json.loads(Path(claim).read_text()), original)
            replacement_proof = self.proof.parent / "replacement-proof.bin"
            replacement_proof.write_bytes(b"replacement proof")
            replacement_proof.replace(self.proof)
            replacement_statement = self.proof.parent / "replacement-statement.json"
            replacement_statement.write_text(json.dumps({**original, "leaf_public_words": [9] * 8}))
            replacement_statement.replace(statement)
            self.binary.write_bytes(b"replacement verifier")
            self.assertEqual(Path(proof).read_bytes(), b"sealed proof")
            self.assertEqual(json.loads(Path(claim).read_text()), original)
            self.assertEqual(Path(executable).read_bytes(), b"sealed verifier")
            return "accepted\n"

        with patch("cli.commands.verify_package", return_value=manifest), \
                patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke", side_effect=native), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(args)
        result = json.loads(output.getvalue())
        self.assertEqual(result["proofs_verified"], 1)
        self.assertEqual(result["leaf_public_words"], [1] * 8)

    def test_chain_audit_rejects_mutation_of_captured_statement(self) -> None:
        self.proof.write_bytes(b"sealed proof")
        statement = Path(str(self.proof) + ".statement.json")
        statement.write_text(json.dumps({
            "schema": "s31-fixed-fold-statement-v3",
            "step": 0,
            "leaf_public_words": [1] * 8,
            "base_public_words": [2] * 8,
            "fold_preprocessed_root": "fixed root",
        }))
        args = make_parser().parse_args(
            ("audit-fold-chain", str(self.package), str(self.proof)))
        manifest = {"name": "example", "lowering": "gate", "artifacts": {}}

        def mutate_captured(_executable: str, _command: str,
                            _proof: str, captured_statement: str) -> str:
            Path(captured_statement).write_text("{}")
            return "accepted\n"

        with patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke", side_effect=mutate_captured):
            with self.assertRaisesRegex(ValueError, "proof input snapshot changed"):
                dispatch(args)

    def test_chain_audit_rejects_linked_checkpoint_inputs_before_native(self) -> None:
        self.proof.write_bytes(b"sealed proof")
        self.statement.write_text(json.dumps({
            "schema": "s31-fixed-fold-statement-v3", "step": 0,
            "leaf_public_words": [1] * 8, "base_public_words": [2] * 8,
            "fold_preprocessed_root": "fixed root",
        }))
        linked_proof = self.proof.parent / "linked-proof.bin"
        linked_proof.symlink_to(self.proof)
        linked_statement = Path(str(linked_proof) + ".statement.json")
        linked_statement.write_bytes(self.statement.read_bytes())
        manifest = {"name": "example", "lowering": "gate", "artifacts": {}}
        with patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke") as native:
            with self.assertRaisesRegex(ValueError, "linked"):
                dispatch(make_parser().parse_args(
                    ("audit-fold-chain", str(self.package), str(linked_proof))))
            native.assert_not_called()

        linked_proof.unlink()
        linked_proof.write_bytes(b"sealed proof")
        linked_statement.unlink()
        linked_statement.symlink_to(self.statement)
        with patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke") as native:
            with self.assertRaisesRegex(ValueError, "linked"):
                dispatch(make_parser().parse_args(
                    ("audit-fold-chain", str(self.package), str(linked_proof))))
            native.assert_not_called()

        linked_parent = self.proof.parent / "linked-parent"
        linked_parent.symlink_to(self.proof.parent, target_is_directory=True)
        with patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke") as native:
            with self.assertRaisesRegex(ValueError, "linked"):
                dispatch(make_parser().parse_args(
                    ("audit-fold-chain", str(self.package),
                     str(linked_parent / self.proof.name))))
            native.assert_not_called()

    def test_chain_audit_caps_statement_before_native_execution(self) -> None:
        self.proof.write_bytes(b"sealed proof")
        Path(str(self.proof) + ".statement.json").write_bytes(b" " * 4097)
        args = make_parser().parse_args(
            ("audit-fold-chain", str(self.package), str(self.proof)))
        manifest = {"name": "example", "lowering": "gate", "artifacts": {}}
        with patch("package.trust.verify_package", return_value=manifest), \
                patch("runtime.folds.invoke") as native:
            with self.assertRaisesRegex(ValueError, "proof input exceeds 4096 bytes"):
                dispatch(args)
        native.assert_not_called()


if __name__ == "__main__":
    unittest.main()
