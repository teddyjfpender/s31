"""A strict release gate must not silently admit uncertified text packages."""

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

from package.release_admission import bounded_direct_gate_snapshot  # noqa: E402
from cli.commands import dispatch  # noqa: E402
from cli.parser import make_parser  # noqa: E402


class BoundedReleaseAdmissionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-release-admission-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name) / "original"
        self.snapshot = Path(temporary.name) / "snapshot"
        (self.snapshot / "bin").mkdir(parents=True)
        (self.snapshot / "verification-key.json").write_text(json.dumps({
            "schema": "s31-verification-key-direct-manifest-v2",
        }))
        self.pins = {kind: kind[0] * 64 for kind in
                     ("source", "key", "prover", "verifier", "text")}
        self.manifest = {
            "name": "example", "lowering": "direct-gate",
            "text_frontend_version": 1, "source_text_sha256": "a" * 64,
            "artifacts": {
                "correspondence-certificate.json": "b" * 64,
                "gate-topology.json": "c" * 64,
            },
        }
        self.certificate = {"status": {
            "source_to_normalized": "source-to-normalized-checked",
            "native_gate_emission": "native-gate-topology-and-selectors-checked",
            "native_root_binding": "native-reported-fixed-root-matches-key",
            "gate_lookup_air_pcs": "AIR/PCS-assumed",
            "admission": "python-package-only",
        }}

    @contextlib.contextmanager
    def admitted(self, package: Path, pins: dict[str, str]):
        self.assertEqual(package, self.package)
        self.assertEqual(pins, self.pins)
        yield self.snapshot, self.manifest

    def test_certified_v2_package_runs_native_preflight_on_snapshot(self) -> None:
        with patch("package.release_admission.admitted_snapshot", self.admitted), \
                patch("package.release_admission.check_package",
                      return_value=self.certificate) as check, \
                patch("package.release_admission.invoke", return_value="valid") as native:
            with bounded_direct_gate_snapshot(self.package, self.pins) as admitted:
                self.assertEqual(admitted, (self.snapshot, self.manifest, self.certificate))
        check.assert_called_once_with(self.snapshot)
        native.assert_called_once_with(
            str(self.snapshot / "bin/s31-example-native-verifier"),
            "check-key", str(self.snapshot / "verification-key.json"))

    def test_unsupported_text_never_reaches_native_verifier(self) -> None:
        self.manifest["artifacts"].pop("correspondence-certificate.json")
        with patch("package.release_admission.admitted_snapshot", self.admitted), \
                patch("package.release_admission.check_package") as check, \
                patch("package.release_admission.invoke") as native:
            with self.assertRaisesRegex(ValueError, "requires a correspondence certificate"):
                with bounded_direct_gate_snapshot(self.package, self.pins):
                    pass
        check.assert_not_called()
        native.assert_not_called()

    def test_noninteger_frontend_version_never_reaches_certificate(self) -> None:
        for version in (True, 1.0):
            with self.subTest(version=version):
                self.manifest["text_frontend_version"] = version
                with patch("package.release_admission.admitted_snapshot", self.admitted), \
                        patch("package.release_admission.check_package") as check, \
                        patch("package.release_admission.invoke") as native:
                    with self.assertRaisesRegex(ValueError, "direct-gate text package"):
                        with bounded_direct_gate_snapshot(self.package, self.pins):
                            pass
                check.assert_not_called()
                native.assert_not_called()

    def test_legacy_unrooted_certificate_is_rejected(self) -> None:
        self.certificate["status"]["native_root_binding"] = "preprocessed-root-binding-assumed"
        with patch("package.release_admission.admitted_snapshot", self.admitted), \
                patch("package.release_admission.check_package",
                      return_value=self.certificate), \
                patch("package.release_admission.invoke") as native:
            with self.assertRaisesRegex(ValueError, "requires a rooted correspondence certificate"):
                with bounded_direct_gate_snapshot(self.package, self.pins):
                    pass
        native.assert_not_called()

    def test_native_preflight_failure_prevents_admission(self) -> None:
        with patch("package.release_admission.admitted_snapshot", self.admitted), \
                patch("package.release_admission.check_package",
                      return_value=self.certificate), \
                patch("package.release_admission.invoke",
                      side_effect=RuntimeError("invalid sealed key")):
            with self.assertRaisesRegex(RuntimeError, "invalid sealed key"):
                with bounded_direct_gate_snapshot(self.package, self.pins):
                    self.fail("an invalid native key must not yield a release snapshot")

    def test_cli_verifies_from_strict_admitted_snapshot(self) -> None:
        proof = self.package / "proof.bin"
        proof.parent.mkdir()
        proof.write_bytes(b"proof")
        Path(str(proof) + ".statement.json").write_bytes(b"statement")
        argv = ["verify-release", str(self.package), str(proof)]
        for kind, value in self.pins.items():
            argv.extend((f"--{kind}-sha256", value))
        parsed = make_parser().parse_args(argv)

        @contextlib.contextmanager
        def strict(package: Path, pins: dict[str, str]):
            self.assertEqual(package, self.package.resolve())
            self.assertEqual(pins, self.pins)
            yield self.snapshot, self.manifest, self.certificate

        with patch("cli.commands.bounded_direct_gate_snapshot", strict), \
                patch("cli.commands.invoke", return_value="accepted") as native, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(parsed)
        self.assertEqual(output.getvalue(), "accepted")
        native.assert_called_once()
        executable, proof_arg, statement_arg, key = native.call_args.args
        self.assertEqual(executable, str(self.snapshot / "bin/s31-example-native-verifier"))
        self.assertNotEqual(proof_arg, str(proof))
        self.assertNotEqual(statement_arg, str(Path(str(proof) + ".statement.json")))
        self.assertEqual(key, str(self.snapshot / "verification-key.json"))


if __name__ == "__main__":
    unittest.main()
