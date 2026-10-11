"""Fast executable smoke for the proved bounded source/relation checker."""

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
sys.path.insert(0, str(FORMAL.parents[1] / "src/frontends/s31/tests/python/generated"))

from text_frontend import compile_text  # noqa: E402
from package.correspondence import (PLAIN_BUILTIN_NAMES, canonical_ir_bytes,
                                    parse_source)  # noqa: E402
from test_direct_alias_correspondence_generated import corpus  # noqa: E402

SOURCE = (
    "circuit square4(public x: [m31; 4]) -> public [m31; 4] { "
    "let base = (x); let once = ((base) .* (base)); "
    "let saved = (once); let result = ((saved) .* (saved)); "
    "let returned = (result); (returned); }"
)

RELATION = {
    "assertions": [],
    "inputs": [{"kind": "m31", "length": 4, "name": "x", "visibility": "public"}],
    "name": "square4",
    "nodes": [
        {"lhs": "x", "name": "once", "op": "mul", "rhs": "x"},
        {"lhs": "once", "name": "result", "op": "mul", "rhs": "once"},
    ],
    "public_outputs": ["result"],
    "version": 1,
}


def invoke(source: bytes, relation: bytes, canonical: bytes | None = None) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "source.s31"
        relation_path = Path(directory) / "normalized.s31.json"
        source_path.write_bytes(source)
        relation_path.write_bytes(relation)
        args = [str(CHECKER), str(source_path), str(relation_path)]
        if canonical is not None:
            canonical_path = Path(directory) / "canonical-ir.json"
            canonical_path.write_bytes(canonical)
            args.append(str(canonical_path))
        return subprocess.run(
            args,
            capture_output=True,
            text=True,
            check=False,
        )


class AliasRelationCheckTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if not CHECKER.is_file():
            raise RuntimeError("build first: cd formal/s31 && lake build s31-alias-relation-check")

    def test_exact_bytes_and_rejections(self) -> None:
        normalized = (json.dumps(RELATION, indent=2, sort_keys=True) + "\n").encode()
        production_relation, _ = compile_text(SOURCE)
        self.assertEqual(production_relation, RELATION)
        accepted = invoke(SOURCE.encode(), normalized)
        self.assertEqual(accepted.returncode, 0, accepted.stderr + accepted.stdout)
        summary = json.loads(accepted.stdout)
        self.assertTrue(summary["accepted"])
        self.assertEqual(summary["gate_count"], 2)
        self.assertEqual(summary["output_wire"], 2)
        self.assertEqual(summary["gates"], [
            {"id": 1, "lhs": 0, "op": "mul", "rhs": 0},
            {"id": 2, "lhs": 1, "op": "mul", "rhs": 1},
        ])
        checked_relation, checked_syntax = parse_source(SOURCE.encode())
        self.assertEqual(checked_relation, RELATION)
        canonical = canonical_ir_bytes(checked_syntax)
        accepted_three_file = invoke(SOURCE.encode(), normalized, canonical)
        self.assertEqual(accepted_three_file.returncode, 0,
                         accepted_three_file.stderr + accepted_three_file.stdout)
        self.assertEqual(json.loads(accepted_three_file.stdout)["checker"],
                         "AliasCanonicalIrBytes.checkAliasCanonical")
        changed_canonical = invoke(SOURCE.encode(), normalized, canonical + b" ")
        self.assertEqual(changed_canonical.returncode, 1)
        self.assertFalse(json.loads(changed_canonical.stdout)["accepted"])

        changed = normalized.replace(b'"op": "mul"', b'"op": "add"', 1)
        rejected_relation = invoke(SOURCE.encode(), changed)
        self.assertEqual(rejected_relation.returncode, 1)
        self.assertFalse(json.loads(rejected_relation.stdout)["accepted"])

        malformed = SOURCE.replace("let base = (x);", "let base = (later);")
        rejected_source = invoke(malformed.encode(), normalized)
        self.assertEqual(rejected_source.returncode, 1)
        self.assertFalse(json.loads(rejected_source.stdout)["accepted"])

        for builtin in PLAIN_BUILTIN_NAMES:
            builtin_source = SOURCE.replace("circuit square4", f"circuit {builtin}", 1)
            builtin_relation = {**RELATION, "name": builtin}
            builtin_bytes = (json.dumps(builtin_relation, indent=2, sort_keys=True) + "\n").encode()
            with self.subTest(builtin=builtin):
                self.assertEqual(invoke(builtin_source.encode(), builtin_bytes).returncode, 1)

        long_name = "x" * 129
        long_source = SOURCE.replace("public x:", f"public {long_name}:", 1).replace("(x)", f"({long_name})")
        long_relation = json.loads(json.dumps(RELATION))
        long_relation["inputs"][0]["name"] = long_name
        long_relation["nodes"][0]["lhs"] = long_name
        long_relation["nodes"][0]["rhs"] = long_name
        long_bytes = (json.dumps(long_relation, indent=2, sort_keys=True) + "\n").encode()
        self.assertEqual(invoke(long_source.encode(), long_bytes).returncode, 1)

        long_producer = "p" * 129
        producer_source = SOURCE.replace("once", long_producer)
        producer_relation = json.loads(json.dumps(RELATION))
        producer_relation["nodes"][0]["name"] = long_producer
        producer_relation["nodes"][1]["lhs"] = long_producer
        producer_relation["nodes"][1]["rhs"] = long_producer
        producer_bytes = (json.dumps(producer_relation, indent=2, sort_keys=True) + "\n").encode()
        self.assertEqual(invoke(producer_source.encode(), producer_bytes).returncode, 1)

    def test_generated_512_one_through_sixteen_gate_sources(self) -> None:
        for case in corpus():
            source = case.source.encode()
            relation, syntax = parse_source(source)
            normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
            canonical = canonical_ir_bytes(syntax)
            with self.subTest(gates=case.gate_count):
                result = invoke(source, normalized, canonical)
                self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                admitted = json.loads(result.stdout)
                self.assertEqual(admitted["gate_count"], case.gate_count)
                self.assertEqual(admitted["output_wire"], syntax["output"])


if __name__ == "__main__":
    unittest.main()
