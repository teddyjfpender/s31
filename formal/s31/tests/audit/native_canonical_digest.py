#!/usr/bin/env python3
"""Join Lean's checked compact IR bytes to fresh native package identities."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

import s31  # noqa: E402
from package.source_relation_fragment import parse_source_fragment  # noqa: E402
from text_frontend import compile_text  # noqa: E402
from test_source_function_check import canonical, canonical_ir, invoke, source_for  # noqa: E402


def run() -> dict:
    cases = (("sub5", source_for(5, "-")),
             ("reversed_add5", source_for(5, "+", reverse_body=True)))
    results = []
    with tempfile.TemporaryDirectory(prefix="s31-source-function-canonical-") as directory:
        work = Path(directory)
        for label, source in cases:
            relation, _ = compile_text(source)
            if relation != parse_source_fragment(source.encode()):
                raise AssertionError(f"independent source parser disagrees: {label}")
            relation_bytes = canonical(relation)
            canonical_bytes = canonical_ir(relation)
            audit = invoke(source.encode(), relation_bytes, canonical_bytes)
            if audit.returncode != 0 or not json.loads(audit.stdout)["canonical_ir_checked"]:
                raise AssertionError(f"Lean source/relation/IR audit failed: {label}: {audit.stdout}")

            source_path = work / f"{label}.s31"
            source_path.write_text(source)
            package = s31.build(source_path, work / f"{label}-package", "direct-gate")
            cost = json.loads((package / "cost-report.json").read_text())
            key = json.loads((package / "verification-key.json").read_text())
            expected = hashlib.sha256(canonical_bytes).hexdigest()
            if cost["canonical_ir_sha256"] != expected or key["canonical_ir_sha256"] != expected:
                raise AssertionError(f"native canonical IR identity differs: {label}")
            results.append({"case": label, "length": 5,
                            "operation": relation["nodes"][0]["op"],
                            "source_operands": [relation["nodes"][0]["lhs"],
                                                relation["nodes"][0]["rhs"]],
                            "canonical_ir_sha256": expected,
                            "raw_qm31_rows": cost["raw"]["qm31_ops"]})
    return {"schema": "s31-source-function-canonical-native-v1", "cases": results,
            "lean_source_relation_ir_accepted": True,
            "native_canonical_digest_matched": True}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
