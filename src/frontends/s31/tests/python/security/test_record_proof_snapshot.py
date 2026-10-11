"""Proof inspection must display bytes from the same private verification snapshot."""

from __future__ import annotations

import io
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

            for target in ("source", "key", "proof", "statement"):
                with self.subTest(target=target):
                    def mutate(_executable: str, copied_proof: str,
                               copied_statement: str, copied_key: str) -> str:
                        paths = {
                            "source": Path(copied_key).parent / "source.s31.json",
                            "key": Path(copied_key),
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


if __name__ == "__main__":
    unittest.main()
