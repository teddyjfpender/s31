#!/usr/bin/env python3
"""Public bit leaves: native range checks, proof binding, and flat AIR parity."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from abi.binding_v2 import flat_assignment_from_typed
from package.context import write_json
from text_frontend import compile_text


SOURCE = """struct Request { flag: bit, value: [m31; 1] }
struct Response { flag: bit, chosen: [m31; 1] }
circuit bits(public request: Request, private other: [m31; 1]) -> public Response {
    Response { flag: std::field::is_zero(other),
               chosen: select(request.flag, request.value, other) }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def reject(verifier: Path, proof: Path, statement: Path, key: Path,
           encoded: bytes, label: str, expected: str | None = None) -> None:
    statement.write_bytes(encoded)
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                            capture_output=True, text=True)
    if result.returncode != 1 or "error:" not in result.stderr or (
            expected is not None and f"error: {expected}" not in result.stderr):
        raise AssertionError(f"native verifier mishandled {label}: "
                             f"exit={result.returncode} {result.stderr}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-public-bit-v2-") as temporary:
        work = Path(temporary)
        source = work / "bits.s31"
        source.write_text(SOURCE)
        relation, _ = compile_text(SOURCE)
        if relation["version"] != 2 or [node["op"] for node in relation["nodes"]] != [
                "is_zero", "select"]:
            raise AssertionError("public bit record lowered to an unexpected graph")
        input_leaves = relation["public_abi"]["inputs"][0]["leaves"]
        output_leaves = relation["public_abi"]["result"]["leaves"]
        if ([leaf["kind"] for leaf in input_leaves] != ["bit", "m31"] or
                [leaf["kind"] for leaf in output_leaves] != ["bit", "m31"]):
            raise AssertionError("typed bit leaf tag was lost")
        manual = {**relation, "version": 1, "name": "bits_flat"}
        del manual["public_abi"]
        manual_path = work / "bits_flat.s31.json"
        manual_path.write_bytes(canonical(manual))

        package = s31.build(source, work / "record-package", "direct-gate")
        flat_package = s31.build(manual_path, work / "flat-package", "direct-gate")
        record_cost = json.loads((package / "cost-report.json").read_text())
        flat_cost = json.loads((flat_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if record_cost[field] != flat_cost[field]:
                raise AssertionError(f"record grouping changed {field}")

        verifier = package / "bin/s31-bits-native-verifier"
        key = package / "verification-key.json"
        checked = 0
        for flag, other, expected_flag, chosen in ((0, 0, 1, 7), (1, 5, 0, 5)):
            typed = {"version": 2,
                     "public_inputs": {"request": {"flag": [flag], "value": [7]}},
                     "private_inputs": {"other": [other]},
                     "result": {"flag": [expected_flag], "chosen": [chosen]}}
            typed_path = work / f"typed-{flag}.json"
            typed_path.write_bytes(canonical(typed))
            flat = flat_assignment_from_typed(relation, canonical(typed))
            flat_path = work / f"flat-{flag}.json"
            write_json(flat_path, flat)
            trial_dir = work / f"record-trial-{flag}"
            flat_trial_dir = work / f"flat-trial-{flag}"
            trial = s31.trial(package, typed_path, trial_dir)
            flat_trial = s31.trial(flat_package, flat_path, flat_trial_dir)
            if (not trial["native_verifier_accepted"] or
                    not trial["changed_public_statement_rejected"] or
                    not flat_trial["native_verifier_accepted"]):
                raise AssertionError("honest typed or flat bit proof did not verify")
            proof = trial_dir / "proof.bin"
            statement = json.loads((trial_dir / "statement.json").read_text())
            for at in (0, 2):
                for bad in (2, (1 << 31) - 2):
                    altered = copy.deepcopy(statement)
                    altered["leaves"][at]["words"][0] = bad
                    reject(verifier, proof, work / "mutated-statement.json", key,
                           canonical(altered), f"bit leaf {at} value {bad}",
                           "InvalidRecordStatement")
                    checked += 1
            flipped = copy.deepcopy(statement)
            flipped["leaves"][0]["words"][0] ^= 1
            reject(verifier, proof, work / "mutated-statement.json", key,
                   canonical(flipped), "valid changed public bit")
            checked += 1
            reject(verifier, proof, work / "mutated-statement.json", key,
                   canonical({"public_inputs": flat["public_inputs"],
                              "public_outputs": flat["public_outputs"]}),
                   "flat v1 statement replay")
            checked += 1

        print(json.dumps({"schema": "s31-record-public-bit-v2-acceptance",
                          "native_honest_proofs": 2, "flat_parity_proofs": 2,
                          "native_rejected_mutations": checked,
                          "zero_extra_grouping_rows": True,
                          "raw": record_cost["raw"],
                          "padded": record_cost["padded"]},
                         indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
