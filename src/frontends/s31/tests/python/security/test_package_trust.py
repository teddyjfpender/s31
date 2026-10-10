"""External package pins must gate native verifier execution."""

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
from package.trust import admit_pinned_package, pinned_paths  # noqa: E402


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class PinnedPackageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="s31-pinned-test-")
        self.addCleanup(self.temporary.cleanup)
        self.package = Path(self.temporary.name) / "package"
        (self.package / "bin").mkdir(parents=True)
        (self.package / "manifest.json").write_text(json.dumps({"name": "unit"}))
        for path, contents in (
            ("source.s31.json", b"normalized relation"),
            ("verification-key.json", b"sealed key"),
            ("bin/s31-unit-prover", b"prover executable"),
            ("bin/s31-unit-native-verifier", b"verifier executable"),
        ):
            (self.package / path).write_bytes(contents)
        self.pins = {kind: digest(path)
                     for kind, path in pinned_paths(self.package).items()}

    def test_exact_external_pins_admit_then_validate_package(self) -> None:
        with patch("package.trust.verify_package", return_value={"name": "unit"}) as validate:
            actual, manifest = admit_pinned_package(self.package, self.pins)
        self.assertEqual(actual, self.pins)
        self.assertEqual(manifest, {"name": "unit"})
        validate.assert_called_once_with(self.package)

    def test_changed_verifier_rejected_before_package_validation(self) -> None:
        (self.package / "bin/s31-unit-native-verifier").write_bytes(b"forged verifier")
        with patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "pinned verifier digest mismatch"):
                admit_pinned_package(self.package, self.pins)
        validate.assert_not_called()

    def test_text_source_requires_its_own_pin_and_detects_mutation(self) -> None:
        text_path = self.package / "source.s31"
        text_path.write_text("fn main(x: M31) -> M31 = x\n")
        with patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "requires exactly"):
                admit_pinned_package(self.package, self.pins)
            validate.assert_not_called()
        self.pins["text"] = digest(text_path)
        with patch("package.trust.verify_package", return_value={"name": "unit"}):
            admit_pinned_package(self.package, self.pins)
        text_path.write_text("fn main(x: M31) -> M31 = x + 1\n")
        with self.assertRaisesRegex(ValueError, "pinned text digest mismatch"):
            admit_pinned_package(self.package, self.pins)

    def test_bin_directory_symlink_rejected_even_inside_package(self) -> None:
        (self.package / "bin").rename(self.package / "bin-real")
        (self.package / "bin").symlink_to("bin-real", target_is_directory=True)
        with patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "pinned prover is a symlink"):
                admit_pinned_package(self.package, self.pins)
            validate.assert_not_called()

    def test_manifest_symlink_rejected_before_reading_it(self) -> None:
        (self.package / "manifest.json").rename(self.package / "manifest-real.json")
        (self.package / "manifest.json").symlink_to("manifest-real.json")
        with patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "package manifest is a symlink"):
                admit_pinned_package(self.package, self.pins)
            validate.assert_not_called()

    def test_manifest_cannot_choose_an_executable_outside_its_namespace(self) -> None:
        (self.package / "manifest.json").write_text(json.dumps({"name": "../other"}))
        with patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "invalid package name"):
                admit_pinned_package(self.package, self.pins)
            validate.assert_not_called()

    def test_cli_rejects_bad_pin_before_invoking_native_verifier(self) -> None:
        proof = self.package / "proof.bin"
        args = ["verify-pinned", str(self.package), str(proof)]
        for kind, value in self.pins.items():
            args.extend((f"--{kind}-sha256", value))
        parsed = make_parser().parse_args(args)
        parsed.verifier_sha256 = "0" * 64
        with patch("package.trust.verify_package") as validate, \
                patch("cli.commands.invoke") as invoke:
            with self.assertRaisesRegex(ValueError, "pinned verifier digest mismatch"):
                dispatch(parsed)
            validate.assert_not_called()
            invoke.assert_not_called()

    def test_cli_admits_before_invoking_native_verifier(self) -> None:
        proof = self.package / "proof.bin"
        args = ["verify-pinned", str(self.package), str(proof)]
        for kind, value in self.pins.items():
            args.extend((f"--{kind}-sha256", value))
        parsed = make_parser().parse_args(args)
        with patch("package.trust.verify_package", return_value={"name": "unit"}) as validate, \
                patch("cli.commands.invoke", return_value="accepted") as invoke, \
                contextlib.redirect_stdout(io.StringIO()) as output:
            dispatch(parsed)
        validate.assert_called_once_with(self.package.resolve())
        package = self.package.resolve()
        invoke.assert_called_once_with(
            str(package / "bin/s31-unit-native-verifier"),
            str(proof.resolve()), str(Path(str(proof) + ".statement.json").resolve()),
            str(package / "verification-key.json"),
        )
        self.assertEqual(output.getvalue(), "accepted")


if __name__ == "__main__":
    unittest.main()
