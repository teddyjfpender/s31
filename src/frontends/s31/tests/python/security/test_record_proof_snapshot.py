"""Proof inspection must display bytes from the same private verification snapshot."""

from __future__ import annotations

import io
import hashlib
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from cli.commands import dispatch
from cli.parser import make_parser
from abi.binding_v2 import encode_public_statement, make_binding
from language.syntax import RecordType
from package.trust import pinned_paths
from s31_stdlib import Type


class RecordProofSnapshotTests(unittest.TestCase):
    def test_caller_path_mutations_cannot_change_verified_readback(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-record-race-") as temporary:
            work = Path(temporary)
            package = work / "package"
            binary = package / "bin" / "s31-demo-native-verifier"
            binary.parent.mkdir(parents=True)
            original_relation = {"version": 2, "name": "original"}
            (package / "source.s31.json").write_text(json.dumps(original_relation))
            (package / "verification-key.json").write_bytes(b"original-key")
            binary.write_bytes(b"original-verifier")
            proof = work / "proof.bin"
            statement = Path(str(proof) + ".statement.json")
            proof.write_bytes(b"original-proof")
            statement.write_bytes(b"original-statement")
            captured_snapshot: list[Path] = []

            def check_snapshot(snapshot: Path) -> dict:
                self.assertNotEqual(snapshot, package)
                captured_snapshot.append(snapshot)
                # A caller can replace every input path after copying. The
                # checked package and the executable path must stay original.
                (package / "source.s31.json").write_text('{"version":1}')
                (package / "verification-key.json").write_bytes(b"changed-key")
                binary.write_bytes(b"changed-verifier")
                self.assertEqual(json.loads((snapshot / "source.s31.json").read_text()),
                                 original_relation)
                return {"name": "demo", "lowering": "direct-gate"}

            def native_verify(executable: str, copied_proof: str,
                              copied_statement: str, key: str) -> str:
                snapshot = captured_snapshot[0]
                self.assertEqual(Path(executable), snapshot / "bin/s31-demo-native-verifier")
                self.assertEqual(Path(executable).read_bytes(), b"original-verifier")
                self.assertEqual(Path(key).read_bytes(), b"original-key")
                self.assertEqual(Path(copied_proof).read_bytes(), b"original-proof")
                self.assertEqual(Path(copied_statement).read_bytes(), b"original-statement")
                self.assertNotEqual(Path(copied_proof), proof)
                self.assertNotEqual(Path(copied_statement), statement)
                proof.write_bytes(b"changed-proof")
                statement.write_bytes(b"changed-statement")
                return "verified"

            def decode(relation: dict, encoded: bytes) -> dict:
                self.assertEqual(relation, original_relation)
                self.assertEqual(encoded, b"original-statement")
                return {"version": 2, "public_inputs": {}, "result": [7]}

            args = make_parser().parse_args(
                ["inspect-record-proof", str(package), str(proof)])
            output = io.StringIO()
            with (mock.patch("package.trust.verify_package", side_effect=check_snapshot),
                  mock.patch("cli.commands.invoke", side_effect=native_verify),
                  mock.patch("cli.commands.decode_typed_public_statement", side_effect=decode),
                  redirect_stdout(output)):
                dispatch(args)
            report = json.loads(output.getvalue())
            self.assertTrue(report["proof_verified"])
            self.assertEqual(report["claim"]["result"], [7])
            self.assertEqual(report["program"], "demo")
            self.assertFalse(captured_snapshot[0].exists())

    def test_verifier_cannot_mutate_copied_inputs_before_readback(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-record-mutation-") as temporary:
            work = Path(temporary)
            package = work / "package"
            binary = package / "bin" / "s31-demo-native-verifier"
            binary.parent.mkdir(parents=True)
            (package / "source.s31.json").write_text('{"version":2,"name":"demo"}')
            (package / "verification-key.json").write_bytes(b"key")
            binary.write_bytes(b"verifier")
            proof = work / "proof.bin"
            statement = Path(str(proof) + ".statement.json")
            proof.write_bytes(b"proof")
            statement.write_bytes(b"statement")
            args = make_parser().parse_args(
                ["inspect-record-proof", str(package), str(proof)])

            for target in ("source", "key", "verifier", "proof", "statement"):
                with self.subTest(target=target):
                    def mutate(_executable: str, copied_proof: str,
                               copied_statement: str, copied_key: str) -> str:
                        paths = {
                            "source": Path(copied_key).parent / "source.s31.json",
                            "key": Path(copied_key),
                            "verifier": Path(_executable),
                            "proof": Path(copied_proof),
                            "statement": Path(copied_statement),
                        }
                        paths[target].write_bytes(b"changed")
                        return "verified"

                    output = io.StringIO()
                    with (mock.patch("package.trust.verify_package",
                                     return_value={"name": "demo", "lowering": "direct-gate"}),
                          mock.patch("cli.commands.invoke", side_effect=mutate),
                          mock.patch("cli.commands.decode_typed_public_statement") as decode,
                          redirect_stdout(output)):
                        with self.assertRaisesRegex(ValueError, "snapshot changed"):
                            dispatch(args)
                    decode.assert_not_called()
                    self.assertEqual(output.getvalue(), "")


class PinnedRecordProofTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="s31-pinned-record-")
        self.addCleanup(self.temporary.cleanup)
        work = Path(self.temporary.name)
        self.package = work / "package"
        (self.package / "bin").mkdir(parents=True)
        field = Type("m31", 1)
        relation = {
            "version": 1, "name": "unit",
            "inputs": [{"name": "x", "kind": "m31", "length": 1,
                        "visibility": "public"}],
            "nodes": [], "assertions": [], "public_outputs": ["x"],
        }
        binding = make_binding(
            relation, [("x", field, "public", ["x"])],
            ("result", RecordType("Echo", (("value", field),)), ["x"]),
        )
        source = {**relation, "version": 2, "public_abi": binding}
        (self.package / "manifest.json").write_text(json.dumps({"name": "unit"}))
        (self.package / "source.s31.json").write_text(json.dumps(source))
        (self.package / "verification-key.json").write_bytes(b"original-key")
        (self.package / "bin/s31-unit-prover").write_bytes(b"original-prover")
        (self.package / "bin/s31-unit-native-verifier").write_bytes(b"original-verifier")
        self.proof = work / "proof.bin"
        self.proof.write_bytes(b"original-proof")
        self.statement = Path(str(self.proof) + ".statement.json")
        self.statement.write_bytes(encode_public_statement(relation, binding, [[7], [7]]))
        self.pins = {kind: hashlib.sha256(path.read_bytes()).hexdigest()
                     for kind, path in pinned_paths(self.package).items()}
        self.manifest = {"name": "unit", "lowering": "direct-gate"}

    def args(self) -> object:
        command = ["inspect-record-proof-pinned", str(self.package), str(self.proof)]
        for kind in ("source", "key", "prover", "verifier", "text"):
            if kind in self.pins:
                command.extend((f"--{kind}-sha256", self.pins[kind]))
        return make_parser().parse_args(command)

    def test_correct_external_pins_verify_and_decode_named_claim(self) -> None:
        output = io.StringIO()

        def inspect(executable: str, proof: str, statement: str, key: str) -> str:
            self.assertNotEqual(Path(executable), self.package / "bin/s31-unit-native-verifier")
            self.assertEqual(Path(executable).read_bytes(), b"original-verifier")
            self.assertEqual(Path(key).read_bytes(), b"original-key")
            self.assertEqual(Path(proof).read_bytes(), b"original-proof")
            self.assertEqual(Path(statement).read_bytes(), self.statement.read_bytes())
            return "accepted"

        with (mock.patch("package.trust.verify_package", return_value=self.manifest) as validate,
              mock.patch("cli.commands.invoke", side_effect=inspect) as native,
              redirect_stdout(output)):
            dispatch(self.args())
        self.assertEqual(validate.call_count, 1)
        self.assertEqual(native.call_count, 1)
        report = json.loads(output.getvalue())
        self.assertTrue(report["proof_verified"])
        self.assertEqual(report["claim"]["public_inputs"], {"x": [7]})
        self.assertEqual(report["claim"]["result"], {"value": [7]})

    def test_wrong_pin_rejects_before_native_verification(self) -> None:
        args = self.args()
        args.verifier_sha256 = "0" * 64
        with (mock.patch("package.trust.verify_package") as validate,
              mock.patch("cli.commands.invoke") as native,
              self.assertRaisesRegex(ValueError, "pinned verifier digest mismatch")):
            dispatch(args)
        validate.assert_not_called()
        native.assert_not_called()

    def test_mutable_caller_paths_cannot_change_pinned_readback(self) -> None:
        original_statement = self.statement.read_bytes()
        output = io.StringIO()

        def mutate_caller(executable: str, proof: str, statement: str, key: str) -> str:
            self.assertEqual(Path(executable).read_bytes(), b"original-verifier")
            self.assertEqual(Path(key).read_bytes(), b"original-key")
            self.assertEqual(Path(proof).read_bytes(), b"original-proof")
            self.assertEqual(Path(statement).read_bytes(), original_statement)
            (self.package / "source.s31.json").write_bytes(b"changed-source")
            (self.package / "verification-key.json").write_bytes(b"changed-key")
            (self.package / "bin/s31-unit-prover").write_bytes(b"changed-prover")
            (self.package / "bin/s31-unit-native-verifier").write_bytes(b"changed-verifier")
            self.proof.write_bytes(b"changed-proof")
            self.statement.write_bytes(b"changed-statement")
            return "accepted"

        with (mock.patch("package.trust.verify_package", return_value=self.manifest),
              mock.patch("cli.commands.invoke", side_effect=mutate_caller),
              redirect_stdout(output)):
            dispatch(self.args())
        report = json.loads(output.getvalue())
        self.assertEqual(report["claim"]["result"], {"value": [7]})

    def test_mutated_copied_statement_rejects_after_native_return(self) -> None:
        output = io.StringIO()

        def mutate_snapshot(_executable: str, _proof: str, statement: str,
                            _key: str) -> str:
            Path(statement).write_bytes(b"changed-statement")
            return "accepted"

        with (mock.patch("package.trust.verify_package", return_value=self.manifest),
              mock.patch("cli.commands.invoke", side_effect=mutate_snapshot),
              redirect_stdout(output),
              self.assertRaisesRegex(ValueError, "snapshot changed")):
            dispatch(self.args())
        self.assertEqual(output.getvalue(), "")

    def test_text_package_requires_fifth_external_pin(self) -> None:
        (self.package / "source.s31").write_text("text source")
        with (mock.patch("package.trust.verify_package") as validate,
              mock.patch("cli.commands.invoke") as native,
              self.assertRaisesRegex(ValueError, "requires exactly")):
            dispatch(self.args())
        validate.assert_not_called()
        native.assert_not_called()


if __name__ == "__main__":
    unittest.main()
