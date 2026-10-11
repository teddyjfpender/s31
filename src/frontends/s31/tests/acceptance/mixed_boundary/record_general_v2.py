#!/usr/bin/env python3
"""Native public-record ABI v2 gate for the source-pinned mixed profile."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import binding_digest, encode_typed_public_statement
from text_frontend import compile_text
from registry_manifest_digest import digest as registry_manifest_digest

P = 2_147_483_647
SOURCE = (S31 / "examples/boundary/record_mixed1.s31").read_text()


def run(*args: str, accept: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, capture_output=True, text=True, check=False)
    if (result.returncode == 0) != accept:
        raise AssertionError(f"unexpected exit {result.returncode}: {args}\n{result.stderr}")
    return result


def family(count: int) -> dict:
    assert count in (1, 8)
    relation, _ = compile_text(SOURCE)
    if count == 1:
        return relation
    input_name = relation["inputs"][0]["name"]
    output_name = relation["public_outputs"][0]
    nodes = []
    for index in range(count):
        nodes.append({
            "name": f"r{index}", "op": "repeat",
            "lhs": input_name if index == 0 else f"r{index - 1}",
            "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 13 + index}],
        })
    nodes.append({"name": output_name, "op": "add", "lhs": "r7", "rhs": input_name})
    return {**relation, "name": "record_mixed_eight", "nodes": nodes}


def flat_relation(source: dict) -> dict:
    relation = {**source, "version": 1}
    relation.pop("public_abi")
    return relation


def exercise(work: Path, count: int) -> dict:
    source = family(count)
    source_path = work / f"record-{count}.s31.json"
    source_path.write_text(json.dumps(source, separators=(",", ":")))
    initial = [1, 2, 3, 4]
    result = initial[:]
    for index in range(count):
        for _ in range(16):
            result = [(word * word + 13 + index) % P for word in result]
    result = [(word + start) % P for word, start in zip(result, initial)]
    assignment = {
        "public_inputs": {source["inputs"][0]["name"]: initial},
        "private_inputs": {},
        "public_outputs": {source["public_outputs"][0]: result},
    }
    assignment_path = work / f"assignment-{count}.json"
    assignment_path.write_text(json.dumps(assignment, separators=(",", ":")))
    claim = {
        "version": 2,
        "abi_sha256": binding_digest(flat_relation(source), source["public_abi"]),
        "public_inputs": {"x": {"words": initial}},
        "result": {"words": result},
    }
    typed = encode_typed_public_statement(source, claim)
    typed_path = work / f"typed-{count}.json"
    typed_path.write_bytes(typed)
    prefix = work / f"build-{count}"
    run("zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=2",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
        "-Ds31-name=record", "-j1", "--prefix", str(prefix))
    if count == 1:
        mismatch = run("zig", "build", "--build-file", str(S31 / "build.zig"),
                       "install", "-Doptimize=ReleaseFast", "-Ds31-version=1",
                       "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
                       "-Ds31-name=record", "-j1", "--prefix", str(work / "wrong-version"),
                       accept=False)
        assert "-Ds31-version differs from embedded mixed source version" in mismatch.stderr
    bin_dir = prefix / "bin"
    prover = bin_dir / "s31-record-mixed-general-prover"
    verifier = bin_dir / "s31-record-mixed-general-native-verifier"
    manifest_bin = bin_dir / "s31-record-mixed-general-manifest"
    manifest = json.loads(run(str(manifest_bin)).stdout)
    assert manifest["schema"] == "s31-mixed-component-inspection-general-v3"
    assert manifest["source_sha256"] == hashlib.sha256(source_path.read_bytes()).hexdigest()
    assert manifest["registry_manifest_sha256"] == registry_manifest_digest(manifest)
    assert manifest["call_count"] == count and manifest["slot_count"] == 1 + 2 * count
    assert [slot["claimed_sum_index"] for slot in manifest["slots"]] == list(range(1 + 2 * count))
    assert [slot["registry_role"] for slot in manifest["slots"]] == [
        "circuit", *(role for _ in range(count) for role in ("chip", "bridge")),
    ]
    proof = work / f"proof-{count}.bin"
    statement = work / f"statement-{count}.json"
    run(str(prover), str(assignment_path), str(proof), str(statement), str(typed_path))
    assert statement.read_bytes() == typed
    run(str(verifier), str(proof), str(statement))
    proof_bytes = proof.read_bytes()
    assert proof_bytes.startswith(b"S31MIX07" + bytes((count, 1 + 2 * count, 3, 0)))
    assert proof_bytes[12:44].hex() == manifest["source_sha256"]
    assert proof_bytes[44:76].hex() == manifest["registry_manifest_sha256"]
    assert proof_bytes[76:108].hex() == manifest["circuit_identity_sha256"]

    for name, root, word_index in (("public_input", 0, 0), ("public_result", 1, 0)):
        changed = copy.deepcopy(json.loads(typed))
        changed["leaves"][root]["words"][word_index] = (
            changed["leaves"][root]["words"][word_index] + 1) % P
        altered = work / f"changed-{count}-{name}.json"
        altered.write_bytes(encode_typed_public_statement(source, {
            **claim,
            "public_inputs": {"x": {"words": changed["leaves"][0]["words"]}},
            "result": {"words": changed["leaves"][1]["words"]},
        }))
        rejected = run(str(verifier), str(proof), str(altered), accept=False)
        assert any(error in rejected.stderr for error in (
            "InvalidMixedPublicStatement", "InvalidMixedInteractionNonce",
            "InvalidMixedLookupSum", "VerificationFailed")), rejected.stderr

    malformed = json.loads(typed)
    malformed["leaves"][0]["path"][1]["field"] = "forged"
    changed_path = work / f"changed-{count}-path.json"
    changed_path.write_bytes((json.dumps(malformed, sort_keys=True, separators=(",", ":")) + "\n").encode())
    run(str(verifier), str(proof), str(changed_path), accept=False)
    duplicate = work / f"duplicate-{count}.json"
    duplicate.write_bytes(typed.replace(b'"version":2', b'"version":2,"version":2'))
    run(str(verifier), str(proof), str(duplicate), accept=False)

    wrong_assignment = copy.deepcopy(assignment)
    wrong_assignment["public_inputs"][source["inputs"][0]["name"]][0] += 1
    wrong = work / f"wrong-assignment-{count}.json"
    wrong.write_text(json.dumps(wrong_assignment))
    run(str(prover), str(wrong), str(work / "wrong.proof"),
        str(work / "wrong.statement"), str(typed_path), accept=False)
    return {"calls": count, "proof_bytes": proof.stat().st_size,
            "installed_file_bytes": sum(path.stat().st_size for path in prefix.rglob("*")
                                        if path.is_file()),
            "prover_binary_bytes": prover.stat().st_size,
            "verifier_binary_bytes": verifier.stat().st_size,
            "manifest_binary_bytes": manifest_bin.stat().st_size,
            "changed_public_input_rejected": True, "changed_public_result_rejected": True}


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-mixed-v2-") as directory:
        work = Path(directory)
        results = [exercise(work, count) for count in (1, 8)]
        print(json.dumps({"schema": "s31-record-mixed-general-v2-acceptance",
                          "profiles": results}, sort_keys=True))


if __name__ == "__main__":
    main()
