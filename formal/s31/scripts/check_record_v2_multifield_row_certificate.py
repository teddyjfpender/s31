#!/usr/bin/env python3
"""Adversarial real-proof controls for the multi-field record row certificate."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
sys.path.insert(0, str(ROOT / "src/frontends/s31/tools/audit"))

from package.trust import pinned_paths  # noqa: E402
from scripts.release import record_v2_multifield_row_certificate as release  # noqa: E402
import record_source_cells as row_audit  # noqa: E402


def rejected(action, reason: str) -> None:
    try:
        action()
    except (OSError, ValueError, RuntimeError):
        return
    raise AssertionError(f"{reason} was accepted")


def main(args: list[str]) -> None:
    if len(args) != 4:
        raise SystemExit("usage: CHECKER PACKAGE PROOF STATEMENT")
    checker, package, proof, statement = (Path(arg).resolve(strict=True) for arg in args)
    pins = {name: hashlib.sha256(path.read_bytes()).hexdigest()
            for name, path in pinned_paths(package).items()}
    digest = hashlib.sha256(checker.read_bytes()).hexdigest()

    def certify(*, proof_path: Path = proof, statement_path: Path = statement,
                source_pins: dict[str, str] = pins) -> dict:
        return release.certify(package, proof_path, statement_path,
                               source_pins, checker, digest)

    accepted = certify()
    if (accepted["arithmetic_nodes"] != 2 or
            accepted["zero_row_aliases"] != 3 or
            accepted["public_leaves"] != 4 or
            [cell["physical_row"] for cell in accepted["source_cells"]] != [508, 0] or
            [cell["use_multiplicity"] for cell in accepted["source_cells"]] != [1, 1] or
            not accepted["native_verifier_accepted"]):
        raise AssertionError("real private two-field pattern certificate differs")

    with tempfile.TemporaryDirectory(prefix="s31-multifield-row-mutation-") as directory:
        work = Path(directory)
        baseline = json.loads(statement.read_bytes())
        wrong = copy.deepcopy(baseline)
        wrong["leaves"][2]["words"][0] += 1
        wrong_result = work / "wrong-result.json"
        wrong_result.write_text(json.dumps(wrong, separators=(",", ":")) + "\n")
        rejected(lambda: certify(statement_path=wrong_result), "wrong public result")

        wrong = copy.deepcopy(baseline)
        wrong["leaves"][3]["words"][0] += 1
        wrong_alias = work / "wrong-alias.json"
        wrong_alias.write_text(json.dumps(wrong, separators=(",", ":")) + "\n")
        rejected(lambda: certify(statement_path=wrong_alias), "contradictory public alias")

        damaged = bytearray(proof.read_bytes())
        damaged[len(damaged) // 2] ^= 1
        bad_proof = work / "wrong-proof.bin"
        bad_proof.write_bytes(damaged)
        rejected(lambda: certify(proof_path=bad_proof), "damaged native proof")

        wrong_pins = dict(pins)
        wrong_pins["text"] = "0" * 64
        rejected(lambda: certify(source_pins=wrong_pins), "wrong external source pin")
        wrong_pins = dict(pins)
        wrong_pins["key"] = "0" * 64
        rejected(lambda: certify(source_pins=wrong_pins), "wrong external key pin")

        static = work / "static"
        static.mkdir()
        for name in ("source.s31", "typed-structural-derivation.json",
                     "source.s31.json", "public-abi.json"):
            shutil.copyfile(package / name, static / name)
        tree_path = static / "typed-structural-derivation.json"
        original_tree = tree_path.read_bytes()
        tree = json.loads(original_tree)
        tree["program"]["steps"][0]["expr"]["field"] = "left"
        tree_path.write_text(json.dumps(tree, indent=2, sort_keys=True) + "\n")
        rejected(lambda: release._check_static(checker, static),
                 "resealed wrong pattern projection")
        tree_path.write_bytes(original_tree)
        source_path = static / "source.s31"
        source_path.write_bytes(source_path.read_bytes().replace(
            b"right: saved, left", b"left: saved, right: left", 1))
        rejected(lambda: release._check_static(checker, static),
                 "changed exact source with old typed relation")

        original_invoke = row_audit.invoke

        def altered_column(column: int):
            def invoke(*argv: str) -> str:
                result = original_invoke(*argv)
                if len(argv) == 2 and argv[1] == "inspect-topology":
                    topology = json.loads(result)
                    topology["columns"][column]["values"][508] += 1
                    return json.dumps(topology)
                return result
            return invoke

        for column, reason in ((6, "changed source output address"),
                               (7, "changed exact source use multiplicity")):
            with patch.object(row_audit, "invoke", altered_column(column)):
                rejected(certify, reason)

        def altered_root(*argv: str) -> str:
            result = original_invoke(*argv)
            if len(argv) == 3 and argv[1] == "inspect-fixed-root-from-columns":
                report = json.loads(result)
                report["fixed_root"] = "0" * 64
                return json.dumps(report)
            return result

        with patch.object(row_audit, "invoke", altered_root):
            rejected(certify, "changed native fixed root")

    print("private two-field pattern: native row certificate accepted; "
          "wrong claim, alias, proof, source/key pins, source/tree, row, "
          "multiplicity and root rejected")


if __name__ == "__main__":
    main(sys.argv[1:])
