"""Executable parity and mutation controls for Lean's pure-field byte bridge.

The Lean binary is built by the formal job. A Python-only test run skips when
that binary is absent; the explicit formal command builds it before this test.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.pure_field_derivation import make_certificate  # noqa: E402
from package.optimizer_receipt import eligible as optimizer_receipt_eligible  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


SCALAR = b"""use std@1;
// aliases are erased and comments are whitespace
circuit choose(public x: [m31; 1], public a: [m31; 1],
               public b: [m31; 1]) -> public [m31; 1] {
  let z = std::field::is_zero(x);
  let copy = z;
  let result = std::field::select(copy, a, b);
  result
}
"""

MIXED = b"""use std@1;
circuit mixed(public x: [m31; 1], private a: [m31; 4],
              private b: [m31; 4]) -> public [m31; 4] {
  let squared = a .* a;
  let z = std::field::is_zero(x);
  let chosen = select(z, squared, b);
  let result = std::math::inv(chosen);
  result
}
"""

EIGHT = b"""use std@1; circuit lanes(private x:[m31;8]) -> public [m31;8] {
  let y = std::math::inv(x); let z = y .* x; z
}
"""

PARENTHESIZED = b"""use std@1;
circuit parenthesized(public x:[m31;1], private a:[m31;4],
                       private b:[m31;4]) -> public [m31;4] {
  let diff = a - b;
  let copy = ((diff));
  let z = std::field::is_zero(x);
  let chosen = (select(z, copy, b));
  chosen
}
"""


class PureFieldLeanBytesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.checker = (ROOT / "formal/s31/.lake/build/bin/"
                       "s31-pure-field-derivation-bytes-check")
        if not cls.checker.is_file():
            raise unittest.SkipTest("build s31-pure-field-derivation-bytes-check first")

    def fixture(self, source: bytes) -> tuple[bytes, bytes, bytes]:
        relation, _ = compile_text(source.decode())
        relation_bytes = canonical(relation)
        certificate_bytes = canonical(make_certificate(source, relation_bytes))
        return source, certificate_bytes, relation_bytes

    def checked(self, source: bytes, cert: bytes, relation: bytes) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in
                     ("source.s31", "pure-field-derivation.json", "source.s31.json")]
            for path, data in zip(paths, (source, cert, relation)):
                path.write_bytes(data)
            return subprocess.run([str(self.checker), *map(str, paths)],
                                  capture_output=True, text=True, check=False)

    def test_compiler_emitted_scalar_mixed_and_eight_lane_artifacts(self) -> None:
        for source in (SCALAR, MIXED, EIGHT, PARENTHESIZED):
            with self.subTest(source=source[:40]):
                result = self.checked(*self.fixture(source))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("accepted: exact source", result.stdout)

    def test_long_straight_line_program(self) -> None:
        lets = ["let z = std::field::is_zero(x);",
                "let picked = select(z, a, b);"]
        prev = "picked"
        for index in range(26):
            new = f"v{index}"
            lets.append(f"let {new} = {prev} + a;")
            prev = new
        source = ("use std@1; circuit long(public x:[m31;1], public a:[m31;1], "
                  "public b:[m31;1]) -> public [m31;1] { " + " ".join(lets) +
                  " " + prev + " }").encode()
        result = self.checked(*self.fixture(source))
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_source_derivation_relation_and_json_mutations_reject(self) -> None:
        source, cert, relation = self.fixture(SCALAR)
        changed_certificate = json.loads(cert)
        changed_certificate["derivation"]["steps"][-1]["resolved_operands"][-1] = "x"
        wrong_index = json.loads(cert)
        wrong_index["derivation"]["steps"][-1]["node_index"] = 0
        wrong_shape = json.loads(cert)
        wrong_shape["derivation"]["steps"][-1]["result"]["length"] = 4
        wrong_rule = json.loads(cert)
        wrong_rule["derivation"]["steps"][-1]["rule"] = "sha256d"
        changed_relation = json.loads(relation)
        changed_relation["nodes"][-1]["rhs"] = "a"
        controls = (
            (source.replace(b"select(copy, a, b)", b"select(copy, a, a)"), cert, relation),
            (source, canonical(changed_certificate), relation),
            (source, canonical(wrong_index), relation),
            (source, canonical(wrong_shape), relation),
            (source, canonical(wrong_rule), relation),
            (source, cert, canonical(changed_relation)),
            (source, cert.replace(b'"schema":', b'"schema": "duplicate", "schema":', 1), relation),
            (source, cert.rstrip(), relation),
            (source + b"\n// \x80", cert, relation),
        )
        for candidate in controls:
            with self.subTest(candidate=candidate[0][-50:]):
                result = self.checked(*candidate)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("rejected:", result.stderr)

    def test_hash_contents_are_package_verifier_boundary(self) -> None:
        source, cert, relation = self.fixture(SCALAR)
        changed = json.loads(cert)
        changed["source_sha256"] = "0" * 64
        self.assertNotEqual(canonical(changed), cert)
        # Lean proves the source/derivation/relation semantics from supplied
        # bytes. The package verifier, not this Lean CLI, owns SHA-256 custody.
        result = self.checked(source, canonical(changed), relation)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_current_optimizer_receipt_has_no_overlap(self) -> None:
        for source in (SCALAR, MIXED, EIGHT, PARENTHESIZED):
            relation, _ = compile_text(source.decode())
            self.assertFalse(optimizer_receipt_eligible(relation))


if __name__ == "__main__":
    unittest.main()
