#!/usr/bin/env python3
"""Pinned public Pair ABI: native compiler digest, proof and alias controls."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
SOURCE = ROOT / "formal/s31/fixtures/record_pair_alias_v2.s31"
EXPECTED_ABI_SHA256 = "fb44caccd29cb52bedc6ef2cdf27c7f864b980f5d4ffe709032819b89447c71a"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from abi.binding_v2 import DOMAIN, decode_public_statement  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("ascii")


def main() -> None:
    source = SOURCE.read_bytes()
    relation, _ = compile_text(source.decode("utf-8"))
    descriptor = relation["public_abi"]
    abi_digest = hashlib.sha256(DOMAIN + canonical(descriptor)).hexdigest()
    if abi_digest != EXPECTED_ABI_SHA256:
        raise AssertionError("pinned Pair source emitted a different public ABI")
    if (relation["public_outputs"] != ["square"] or
            relation["nodes"] != [{"lhs": "x", "name": "square", "op": "mul", "rhs": "x"}]):
        raise AssertionError("pinned Pair source changed its one-wire arithmetic relation")

    with tempfile.TemporaryDirectory(prefix="s31-record-pair-refinement-") as directory:
        work = Path(directory)
        package = s31.build(SOURCE, work / "package", "direct-gate")
        native_relation = json.loads((package / "source.s31.json").read_bytes())
        key = json.loads((package / "verification-key.json").read_bytes())
        published_abi = json.loads((package / "public-abi.json").read_bytes())
        if (native_relation != relation or
                (package / "source.s31").read_bytes() != source or
                published_abi.get("boundary") != descriptor or
                published_abi.get("boundary_sha256") != abi_digest or
                key.get("public_abi_sha256") != abi_digest):
            raise AssertionError("native package source, ABI artifact or sealed key differs")
        prover = package / "bin/s31-pair-prover"
        inspected = subprocess.run([str(prover), "inspect"], capture_output=True, text=True, check=True)
        inspection = json.loads(inspected.stdout + inspected.stderr)
        if (inspection.get("public_abi_sha256") != abi_digest or
                inspection.get("program_sha256") != key.get("program_sha256") or
                inspection.get("canonical_ir_sha256") != key.get("canonical_ir_sha256")):
            raise AssertionError("fresh native inspect differs from sealed key")

        assignment = work / "assignment.json"
        assignment.write_bytes(canonical({
            "public_inputs": {"x": [7]}, "private_inputs": {},
            "public_outputs": {"square": [49]},
        }))
        trial = s31.trial(package, assignment, work / "trial")
        if trial["native_verifier_accepted"] is not True:
            raise AssertionError("honest Pair proof did not verify")
        honest = work / "trial/statement.json"
        statement = json.loads(honest.read_bytes())
        flat = {**relation, "version": 1}
        del flat["public_abi"]
        if decode_public_statement(flat, descriptor, honest.read_bytes()) != [7, 49, 0, 0, 0, 0, 0, 0]:
            raise AssertionError("Pair typed statement did not project to two proof words")
        verifier = package / "bin/s31-pair-native-verifier"
        proof = work / "trial/proof.bin"
        key_path = package / "verification-key.json"
        rejected = []
        for label in ("changed_first_alias", "changed_second_alias", "changed_field_path"):
            changed = copy.deepcopy(statement)
            if label == "changed_first_alias":
                changed["leaves"][1]["words"] = [50]
            elif label == "changed_second_alias":
                changed["leaves"][2]["words"] = [50]
            else:
                changed["leaves"][2]["path"][1]["field"] = "other"
            changed_path = work / f"{label}.json"
            changed_path.write_bytes(canonical(changed))
            outcome = subprocess.run(
                [str(verifier), str(proof), str(changed_path), str(key_path)],
                capture_output=True, text=True,
            )
            if outcome.returncode != 1 or "InvalidRecordStatement" not in outcome.stderr:
                raise AssertionError(f"native verifier did not reject {label}: {outcome.stderr}")
            rejected.append(label)
        print(json.dumps({
            "schema": "s31-record-pair-refinement-acceptance-v1",
            "native_proof_accepted": True,
            "abi_sha256": abi_digest,
            "public_words": [7, 49],
            "rejected_native_mutations": rejected,
            "raw_qm31_rows": inspection["raw"]["qm31_ops"],
            "padded_qm31_rows": inspection["padded"]["qm31_ops"],
            "proof_bytes": trial["proof_bytes"],
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
