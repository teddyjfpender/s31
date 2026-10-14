"""One text package accepted by both the Lean byte bridge and optimizer audit."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.build import build_text  # noqa: E402
from package.verify import verify_package  # noqa: E402
from package.optimizer_receipt import ARTIFACT, SCHEMA  # noqa: E402

SOURCE = b"""use std@1;
circuit optimizer_control(public x: [m31; 1], private a: [m31; 4],
                          private b: [m31; 4]) -> public [m31; 4] {
    let square = a .* a;
    let z = std::field::is_zero(x);
    let picked = std::field::select(z, square, b);
    let result = std::math::inv(picked);
    result
}
"""


class OptimizerControlJoinTests(unittest.TestCase):
    def test_one_sealed_text_package_crosses_both_checked_boundaries(self) -> None:
        checker = Path(os.environ.get(
            "S31_PURE_FIELD_LEAN_CHECKER",
            ROOT / "formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check"))
        if not checker.is_file():
            self.skipTest("build the Lean pure-field byte checker first")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.s31"
            source.write_bytes(SOURCE)
            package = build_text(source, root / "package", lowering="gate")
            manifest = verify_package(package)
            self.assertEqual(manifest["optimizer_correspondence_schema"], SCHEMA)
            for name in (ARTIFACT, "pure-field-derivation.json"):
                self.assertIn(name, manifest["artifacts"])
            checked = subprocess.run(
                [str(checker), str(package / "source.s31"),
                 str(package / "pure-field-derivation.json"),
                 str(package / "source.s31.json")],
                capture_output=True, text=True, check=False)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            self.assertIn("accepted: exact source", checked.stdout)

            # Refresh the package artifact hash so admission reaches the
            # receipt's independent source/IR identity checks.
            path = package / ARTIFACT
            original = path.read_bytes()
            receipt = json.loads(original)
            receipt["canonical_ir_sha256"] = "0" * 64
            path.write_text(json.dumps(receipt))
            manifest_path = package / "manifest.json"
            manifest["artifacts"][ARTIFACT] = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "optimizer receipt"):
                verify_package(package)


if __name__ == "__main__":
    unittest.main()
