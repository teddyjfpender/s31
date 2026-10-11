"""The release gate must pin five artifacts and use only its private copy."""

from __future__ import annotations

import contextlib
import hashlib
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
from package.release_admission import bounded_direct_gate_snapshot  # noqa: E402
from package.trust import pinned_paths  # noqa: E402


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ReleaseAdmissionBoundaryTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-release-boundary-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name) / "package"
        (self.package / "bin").mkdir(parents=True)
        self.manifest = {
            "name": "bounded", "lowering": "direct-gate",
            "text_frontend_version": 1, "source_text_sha256": "a" * 64,
            "artifacts": {
                "correspondence-certificate.json": "b" * 64,
                "gate-topology.json": "c" * 64,
            },
        }
        (self.package / "manifest.json").write_text(json.dumps(self.manifest))
        for name, data in (
            ("source.s31.json", b"original relation"),
            ("source.s31", b"original source"),
            ("verification-key.json", json.dumps({
                "schema": "s31-verification-key-direct-manifest-v2",
            }).encode()),
            ("bin/s31-bounded-prover", b"original prover"),
            ("bin/s31-bounded-native-verifier", b"original verifier"),
        ):
            (self.package / name).write_bytes(data)
        self.pins = {kind: digest(path)
                     for kind, path in pinned_paths(self.package).items()}
        self.assertEqual(set(self.pins), {"source", "key", "prover", "verifier", "text"})
        self.certificate = {"status": {
            "source_to_normalized": "source-to-normalized-checked",
            "native_gate_emission": "native-gate-topology-and-selectors-checked",
            "native_root_binding": "native-reported-fixed-root-matches-key",
            "admission": "python-package-only",
        }}

    def test_every_external_pin_is_required_before_certificate_or_native_preflight(self) -> None:
        for kind in self.pins:
            with self.subTest(missing=kind), \
                    patch("package.trust.verify_package") as validate, \
                    patch("package.release_admission.check_package") as certificate, \
                    patch("package.release_admission.invoke") as native:
                without = {name: value for name, value in self.pins.items()
                           if name != kind}
                with self.assertRaisesRegex(ValueError, "requires exactly these digests"):
                    with bounded_direct_gate_snapshot(self.package, without):
                        self.fail("missing external pin admitted")
                validate.assert_not_called()
                certificate.assert_not_called()
                native.assert_not_called()

    def test_every_changed_pinned_artifact_fails_before_certificate_or_native_preflight(self) -> None:
        for kind, path in pinned_paths(self.package).items():
            original = path.read_bytes()
            with self.subTest(changed=kind), \
                    patch("package.trust.verify_package") as validate, \
                    patch("package.release_admission.check_package") as certificate, \
                    patch("package.release_admission.invoke") as native:
                path.write_bytes(original + b" tampered")
                try:
                    with self.assertRaisesRegex(ValueError, f"pinned {kind} digest mismatch"):
                        with bounded_direct_gate_snapshot(self.package, self.pins):
                            self.fail("changed externally pinned bytes admitted")
                finally:
                    path.write_bytes(original)
                validate.assert_not_called()
                certificate.assert_not_called()
                native.assert_not_called()

    def test_original_mutation_after_admission_cannot_change_verified_package(self) -> None:
        proof = self.package / "proof.bin"
        statement = self.package / "proof.bin.statement.json"
        proof.write_bytes(b"proof")
        statement.write_bytes(b"statement")
        args = ["verify-release", str(self.package), str(proof)]
        for kind, value in self.pins.items():
            args.extend((f"--{kind}-sha256", value))
        expected = {kind: path.read_bytes()
                    for kind, path in pinned_paths(self.package).items()}

        def mutate_original(snapshot: Path) -> dict:
            self.assertNotEqual(snapshot, self.package)
            for path in pinned_paths(self.package).values():
                path.write_bytes(b"changed after snapshot")
            proof.write_bytes(b"changed proof during package admission")
            statement.write_bytes(b"changed statement during package admission")
            return self.certificate

        def check_key(executable: str, command: str, key: str) -> str:
            self.assertEqual(command, "check-key")
            self.assertEqual(Path(key).parent, Path(executable).parents[1])
            return "valid"

        def verify(executable: str, proof_arg: str, statement_arg: str,
                   key: str) -> str:
            snapshot = Path(key).parent
            self.assertEqual(Path(executable).parents[1], snapshot)
            for kind, path in pinned_paths(snapshot).items():
                self.assertEqual(path.read_bytes(), expected[kind])
            self.assertNotEqual(Path(proof_arg), proof)
            self.assertNotEqual(Path(statement_arg), statement)
            self.assertEqual(Path(proof_arg).read_bytes(), b"proof")
            self.assertEqual(Path(statement_arg).read_bytes(), b"statement")
            return "accepted"

        with patch("package.trust.verify_package", return_value=self.manifest), \
                patch("package.release_admission.check_package",
                      side_effect=mutate_original), \
                patch("package.release_admission.invoke", side_effect=check_key), \
                patch("cli.commands.invoke", side_effect=verify) as native, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(make_parser().parse_args(args))
        native.assert_called_once()
        self.assertEqual(output.getvalue(), "accepted")

    def test_native_mutation_of_captured_inputs_cannot_print_acceptance(self) -> None:
        proof = self.package / "proof.bin"
        statement = self.package / "proof.bin.statement.json"
        proof.write_bytes(b"proof")
        statement.write_bytes(b"statement")
        args = ["verify-release", str(self.package), str(proof)]
        for kind, value in self.pins.items():
            args.extend((f"--{kind}-sha256", value))

        def check_key(_executable: str, command: str, _key: str) -> str:
            self.assertEqual(command, "check-key")
            return "valid"

        for changed in ("proof", "statement"):
            def tamper(_executable: str, proof_arg: str, statement_arg: str,
                       _key: str) -> str:
                target = Path(proof_arg if changed == "proof" else statement_arg)
                target.write_bytes(b"native changed captured input")
                return "accepted"

            with self.subTest(changed=changed), \
                    patch("package.trust.verify_package", return_value=self.manifest), \
                    patch("package.release_admission.check_package",
                          return_value=self.certificate), \
                    patch("package.release_admission.invoke", side_effect=check_key), \
                    patch("cli.commands.invoke", side_effect=tamper), \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                with self.assertRaisesRegex(ValueError, "snapshot changed"):
                    dispatch(make_parser().parse_args(args))
            self.assertEqual(output.getvalue(), "")


if __name__ == "__main__":
    unittest.main()
