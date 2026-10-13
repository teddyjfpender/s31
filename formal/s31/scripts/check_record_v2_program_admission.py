#!/usr/bin/env python3
"""Focused static corpus plus optional real record proof and fixed-row mutations."""

from __future__ import annotations

import hashlib
import json
import copy
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.trust import pinned_paths  # noqa: E402
from scripts.release import record_v2_lean_release as release  # noqa: E402


def check_real(package: Path, proof: Path, statement: Path, checker: Path) -> None:
    pins = {name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in pinned_paths(package).items()}
    checker_digest = hashlib.sha256(checker.read_bytes()).hexdigest()
    if "native verification accepted" not in release.verify(
            package, proof, statement, pins, checker, checker_digest):
        raise AssertionError("real public record proof was not accepted")

    with tempfile.TemporaryDirectory(prefix="s31-record-admission-mutation-") as temp:
        altered = json.loads(statement.read_bytes())
        altered["leaves"][-1]["words"][0] += 1
        wrong_claim = Path(temp) / "wrong-claim.json"
        wrong_claim.write_text(json.dumps(altered, sort_keys=True,
                                          separators=(",", ":")) + "\n")
        try:
            release.verify(package, proof, wrong_claim, pins, checker, checker_digest)
        except ValueError as exc:
            if "source scalar evaluator rejected public claim" not in str(exc):
                raise
        else:
            raise AssertionError("wrong public result reached the native verifier")

    with release.admitted_snapshot(package, pins) as (snapshot, manifest):
        real_invoke = release.invoke
        real_schedule = release.exact_direct_gate_schedule

        def altered_schedule(*args: object) -> tuple:
            gates, variables, rows, source = real_schedule(*args)
            gates = copy.deepcopy(gates)
            gates["add"][0]["in0"] += 1
            return gates, variables, rows, source

        with patch.object(release, "exact_direct_gate_schedule", altered_schedule):
            try:
                release.check_fixed_rows(snapshot, manifest)
            except ValueError:
                pass
            else:
                raise AssertionError("altered source-derived fixed Gate row was accepted")

        def altered_root(*args: str) -> str:
            result = real_invoke(*args)
            if len(args) == 3 and args[1] == "inspect-fixed-root-from-columns":
                report = json.loads(result)
                report["fixed_root"] = "0" * 64
                return json.dumps(report)
            return result

        with patch.object(release, "invoke", altered_root):
            try:
                release.check_fixed_rows(snapshot, manifest)
            except ValueError:
                pass
            else:
                raise AssertionError("altered fixed Gate root was accepted")
    print("real record proof: accepted; wrong claim, fixed row and root: rejected")


def main(argv: list[str]) -> None:
    if len(argv) not in (1, 4):
        raise SystemExit("usage: CHECKER [PACKAGE PROOF STATEMENT]")
    checker = Path(argv[0]).resolve(strict=True)
    corpus = ROOT / "formal/s31/scripts/check_record_v2_source_correspondence.py"
    subprocess.run([sys.executable, str(corpus), str(checker)], check=True)
    if len(argv) == 4:
        check_real(*(Path(arg).resolve(strict=True) for arg in argv[1:]), checker)


if __name__ == "__main__":
    main(sys.argv[1:])
