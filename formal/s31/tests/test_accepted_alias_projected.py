"""Early-return alias bytes exercise the general projected-witness premise."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[1]
CHECKER = FORMAL / ".lake/build/bin/s31-alias-relation-check"
sys.path.insert(0, str(FORMAL.parents[1] / "src/frontends/s31/python"))

from package.correspondence import canonical_ir_bytes, parse_source
from text_frontend import compile_text


SOURCE = """circuit early_alias(public x: [m31; 4]) -> public [m31; 4] {
  let base = (x);
  let a = ((base) .* (base));
  let saved = (a);
  let b = base + saved;
  let c = ((saved) .* (b));
  let returned = saved;
  returned
}"""


def audited(text: str, canonical_override: bytes | None = None) -> tuple[int, dict]:
    relation, syntax = parse_source(text.encode())
    produced, _ = compile_text(text)
    if relation != produced:
        raise AssertionError("independent source parser differs from production")
    with tempfile.TemporaryDirectory(prefix="s31-alias-early-return-") as directory:
        work = Path(directory)
        source_path = work / "source.s31"
        normalized_path = work / "normalized.s31.json"
        canonical_path = work / "canonical-ir.json"
        source_path.write_bytes(text.encode())
        normalized_path.write_bytes(
            (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode())
        canonical_path.write_bytes(
            canonical_override if canonical_override is not None
            else canonical_ir_bytes(syntax))
        result = subprocess.run(
            [str(CHECKER), str(source_path), str(normalized_path),
             str(canonical_path)], capture_output=True, text=True, check=False)
    return result.returncode, json.loads(result.stdout)


class AcceptedAliasProjectedTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not CHECKER.is_file():
            raise RuntimeError("build first: cd formal/s31 && lake build s31-alias-relation-check")

    def test_three_file_checker_keeps_dead_trailing_arithmetic(self) -> None:
        status, report = audited(SOURCE)
        self.assertEqual(status, 0, report)
        self.assertTrue(report["accepted"])
        self.assertEqual(report["output_wire"], 1)
        self.assertEqual(report["gates"], [
            {"id": 1, "lhs": 0, "rhs": 0, "op": "mul"},
            {"id": 2, "lhs": 0, "rhs": 1, "op": "add"},
            {"id": 3, "lhs": 1, "rhs": 2, "op": "mul"},
        ])

        retargeted = SOURCE.replace("let returned = saved;", "let returned = c;")
        changed_status, changed = audited(retargeted)
        self.assertEqual(changed_status, 0, changed)
        self.assertEqual(changed["gates"], report["gates"])
        self.assertEqual(changed["output_wire"], 3)

        # The same source and normalized bytes cannot be paired with an IR
        # selecting the later producer.
        _, changed_syntax = parse_source(retargeted.encode())
        wrong_status, wrong = audited(
            SOURCE, canonical_ir_bytes(changed_syntax))
        self.assertEqual(wrong_status, 1, wrong)
        self.assertFalse(wrong["accepted"])


if __name__ == "__main__":
    unittest.main()
