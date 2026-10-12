"""Ordinary proof verification must execute the admitted package snapshot."""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from cli.commands import dispatch  # noqa: E402
from cli.parser import make_parser  # noqa: E402


class UnpinnedVerificationTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-unpinned-verify-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name) / "package"
        (self.package / "bin").mkdir(parents=True)
        (self.package / "verification-key.json").write_bytes(b"sealed key")
        (self.package / "bin/s31-example-native-verifier").write_bytes(b"sealed verifier")
        self.proof = Path(temporary.name) / "proof.bin"
        self.proof.write_bytes(b"sealed proof")
        Path(str(self.proof) + ".statement.json").write_bytes(b"sealed statement")
        self.args = make_parser().parse_args(("verify", str(self.package), str(self.proof)))

    def test_admission_failure_prevents_native_execution(self) -> None:
        with patch("package.trust.verify_package", side_effect=ValueError("bad certificate")), \
                patch("cli.commands.invoke") as invoke:
            with self.assertRaisesRegex(ValueError, "bad certificate"):
                dispatch(self.args)
        invoke.assert_not_called()

    def test_mutating_original_package_does_not_change_verifier_inputs(self) -> None:
        captured_snapshot: list[Path] = []

        def verify(executable: str, proof: str, statement: str, key: str) -> str:
            binary = Path(executable)
            snapshot = binary.parents[1]
            captured_snapshot.append(snapshot)
            self.assertNotEqual(snapshot, self.package.resolve())
            self.assertEqual(binary.read_bytes(), b"sealed verifier")
            self.assertEqual(Path(key).read_bytes(), b"sealed key")
            self.assertNotEqual(Path(proof), self.proof)
            self.assertEqual(Path(proof).read_bytes(), b"sealed proof")
            self.assertEqual(Path(statement).read_bytes(), b"sealed statement")
            (self.package / "bin/s31-example-native-verifier").write_bytes(b"replacement")
            (self.package / "verification-key.json").write_bytes(b"replacement")
            self.assertEqual(binary.read_bytes(), b"sealed verifier")
            self.assertEqual(Path(key).read_bytes(), b"sealed key")
            return "accepted\n"

        with patch("package.trust.verify_package", return_value={"name": "example"}) as admit, \
                patch("cli.commands.invoke", side_effect=verify) as invoke, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(self.args)
        admit.assert_called_once()
        self.assertEqual(admit.call_args.args[0], captured_snapshot[0])
        invoke.assert_called_once()
        self.assertFalse(captured_snapshot[0].exists())
        self.assertEqual(output.getvalue(), "accepted\n")

    def test_mutating_proof_during_package_admission_does_not_change_native_inputs(self) -> None:
        def admit(_snapshot: Path) -> dict:
            self.proof.write_bytes(b"replacement proof")
            Path(str(self.proof) + ".statement.json").write_bytes(b"replacement statement")
            return {"name": "example"}

        def verify(_executable: str, proof: str, statement: str, _key: str) -> str:
            self.assertEqual(Path(proof).read_bytes(), b"sealed proof")
            self.assertEqual(Path(statement).read_bytes(), b"sealed statement")
            return "accepted"

        with patch("package.trust.verify_package", side_effect=admit), \
                patch("cli.commands.invoke", side_effect=verify), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(self.args)
        self.assertEqual(output.getvalue(), "accepted")

    def test_native_mutation_cannot_print_success(self) -> None:
        def mutate(_executable: str, proof: str, _statement: str, _key: str) -> str:
            Path(proof).write_bytes(b"changed during native verification")
            return "accepted"

        with patch("package.trust.verify_package", return_value={"name": "example"}), \
                patch("cli.commands.invoke", side_effect=mutate), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            with self.assertRaisesRegex(ValueError, "snapshot changed"):
                dispatch(self.args)
        self.assertEqual(output.getvalue(), "")


if __name__ == "__main__":
    unittest.main()
