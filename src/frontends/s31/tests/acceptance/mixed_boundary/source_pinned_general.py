#!/usr/bin/env python3
"""Black-box source-pinned controls for the experimental 1..8 mixed proof."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

from registry_manifest_digest import digest as registry_manifest_digest

S31 = Path(__file__).resolve().parents[3]
MODULUS = 2_147_483_647
MAGIC = b"S31MIX07"
SUMS_OFFSET = len(MAGIC) + 4 + 32 * 3 + 8


def run(*args: str, accept: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, text=True, capture_output=True, check=False)
    if (result.returncode == 0) != accept:
        raise AssertionError(
            f"unexpected exit {result.returncode} for {args}:\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result


def family(count: int) -> tuple[dict, dict]:
    assert 1 <= count <= 8
    nodes = []
    for call_id in range(count):
        nodes.append({
            "name": f"r{call_id}", "op": "repeat",
            "lhs": "x" if call_id == 0 else f"r{call_id - 1}",
            "rounds": 16,
            "body": [{"op": "square"}, {"op": "add_const", "constant": 13 + call_id}],
        })
    nodes += [
        {"name": "sum", "op": "add", "lhs": f"r{count - 1}", "rhs": "x"},
        {"name": "product", "op": "mul", "lhs": f"r{count - 1}", "rhs": "x"},
    ]
    source = {
        "version": 1, "name": f"mixed_general_{count}",
        "inputs": [{"name": "x", "kind": "m31", "length": 4, "visibility": "private"}],
        "nodes": nodes, "assertions": [], "public_outputs": ["sum", "product"],
    }
    initial = [1, 2, 3, 4]
    result = initial.copy()
    for call_id in range(count):
        for _ in range(16):
            result = [(value * value + 13 + call_id) % MODULUS for value in result]
    assignment = {
        "public_inputs": {}, "private_inputs": {"x": initial},
        "public_outputs": {
            "sum": [(a + b) % MODULUS for a, b in zip(result, initial)],
            "product": [(a * b) % MODULUS for a, b in zip(result, initial)],
        },
    }
    return source, assignment


def check_source_call_mapping(source: dict, manifest: dict) -> None:
    """Independently project this chain's source calls into the native roster.

    This checks the public inspection report. The generated verifier remains
    responsible for binding it to compiler output, fixed rows and proof bytes.
    """
    calls = manifest["calls"]
    count = len(calls)
    nodes = source["nodes"]
    if (not 1 <= count <= 8 or manifest["call_count"] != count or
            len(nodes) != count + 2 or len(manifest["slots"]) != 1 + 2 * count or
            source["inputs"] != [{"name": "x", "kind": "m31", "length": 4,
                                   "visibility": "private"}] or
            source["public_outputs"] != ["sum", "product"]):
        raise AssertionError("source/manifest call shape differs")
    occupied: set[int] = set()
    previous_name = "x"
    previous_output: list[int] | None = None

    def check_slot(slot: dict, index: int, call_id: int | None,
                   role: str, key: str, registry_id: int) -> None:
        # source_kind is a diagnostic projection, not part of the registry
        # digest. Check it against the source-derived constructor explicitly.
        if (slot["source_kind"] != key or slot["registry_key"] != key or
                slot["registry_id"] != registry_id or
                slot["registry_version"] != 1 or
                slot["registry_role"] != role or slot["call_id"] != call_id or
                slot["proof_index"] != index or
                slot["claimed_sum_index"] != index):
            raise AssertionError("mixed source/registry/claim slot differs")

    circuit = manifest["slots"][0]
    check_slot(circuit, 0, None, "circuit", "bundled_circuit", 0)
    if circuit["relation_ids"] != [378353459]:
        raise AssertionError("mixed circuit Gate relation differs")
    for call_id, (node, call) in enumerate(zip(nodes[:count], calls)):
        expected = {"name": f"r{call_id}", "op": "repeat", "lhs": previous_name,
                    "rounds": 16,
                    "body": [{"op": "square"},
                             {"op": "add_const", "constant": 13 + call_id}]}
        if (node != expected or call["call_id"] != call_id or
                call["source_node_id"] != call_id + 1 or
                call["input_node_id"] != call_id or
                call["rounds"] != node["rounds"] or
                call["constant"] != node["body"][1]["constant"]):
            raise AssertionError("mixed call differs from source repeat")
        inputs, outputs = call["input"], call["output"]
        if (not isinstance(inputs, list) or not isinstance(outputs, list) or
                len(inputs) != 4 or len(outputs) != 4 or
                any(type(address) is not int or address < 0 for address in inputs + outputs) or
                len(set(inputs)) != 4 or len(set(outputs)) != 4 or
                set(outputs) & occupied or
                set(outputs) & set(inputs) or
                (previous_output is not None and inputs != previous_output)):
            raise AssertionError("mixed call endpoint chain differs")
        occupied.update(inputs)
        occupied.update(outputs)
        chip, bridge = manifest["slots"][1 + 2 * call_id:3 + 2 * call_id]
        constructor = "pair" if call_id < 2 else "many"
        check_slot(chip, 1 + 2 * call_id, call_id, "chip",
                   f"{constructor}_chip", 1 if call_id < 2 else 3)
        check_slot(bridge, 2 + 2 * call_id, call_id, "bridge",
                   f"{constructor}_bridge", 2 if call_id < 2 else 4)
        if (chip["relation_ids"] != [1395863811] or
                bridge["relation_ids"] != [378353459, 1395863811]):
            raise AssertionError("mixed call lookup relation or slot differs")
        previous_output = outputs
        previous_name = node["name"]
    if (nodes[count] != {"name": "sum", "op": "add", "lhs": previous_name,
                          "rhs": "x"} or
            nodes[count + 1] != {"name": "product", "op": "mul",
                                 "lhs": previous_name, "rhs": "x"}):
        raise AssertionError("mixed public output tail differs")


def check_source_call_mapping_mutations(source: dict, manifest: dict) -> int:
    """Require the independent projection to detect altered call metadata."""
    cases = []
    for key in ("call_id", "source_node_id", "input_node_id", "rounds", "constant"):
        changed = copy.deepcopy(manifest)
        changed["calls"][0][key] += 1
        cases.append((f"call-{key}", changed))
    for field in ("input", "output"):
        changed = copy.deepcopy(manifest)
        changed["calls"][0][field][0] += 1
        cases.append((f"endpoint-{field}", changed))
    for slot, key, value in ((1, "call_id", 7), (1, "relation_ids", [378353459]),
                             (2, "relation_ids", [1395863811]),
                             (0, "relation_ids", [1395863811])):
        changed = copy.deepcopy(manifest)
        changed["slots"][slot][key] = value
        cases.append((f"slot-{slot}-{key}", changed))
    for slot, key, value in ((1, "registry_key", "many_chip"),
                             (2, "registry_id", 4),
                             (1, "registry_version", 2),
                             (1, "proof_index", 2),
                             (2, "claimed_sum_index", 1)):
        changed = copy.deepcopy(manifest)
        changed["slots"][slot][key] = value
        cases.append((f"slot-{slot}-{key}", changed))
    for index, slot in enumerate(manifest["slots"]):
        changed = copy.deepcopy(manifest)
        changed["slots"][index]["source_kind"] = (
            "pair_chip" if index == 0 else
            slot["source_kind"].replace("_chip", "_bridge") if index % 2 else
            slot["source_kind"].replace("_bridge", "_chip"))
        cases.append((f"slot-{index}-source-kind", changed))
    # This retains a permutation of all claimed-sum indices; order still
    # matters because the claims belong to different AIR components.
    changed = copy.deepcopy(manifest)
    changed["slots"][1]["claimed_sum_index"] = 2
    changed["slots"][2]["claimed_sum_index"] = 1
    cases.append(("swapped-chip-bridge-claim-indices", changed))
    for label, changed in cases:
        try:
            check_source_call_mapping(source, changed)
        except AssertionError:
            continue
        raise AssertionError(f"mixed source/manifest mutation {label} escaped independent projection")
    return len(cases)


def static_mapping_checks() -> dict:
    """Exercise the projector and mutation controls without a native build."""
    mutation_counts: dict[int, int] = {}
    for count in (1, 3, 8):
        source, _ = family(count)
        calls = []
        slots = [{"source_kind": "bundled_circuit",
                  "registry_key": "bundled_circuit", "registry_id": 0,
                  "registry_version": 1, "registry_role": "circuit",
                  "call_id": None, "proof_index": 0,
                  "claimed_sum_index": 0, "relation_ids": [378353459]}]
        previous = [100, 101, 102, 103]
        for call_id in range(count):
            output = [104 + 4 * call_id + lane for lane in range(4)]
            calls.append({"call_id": call_id, "source_node_id": call_id + 1,
                          "input_node_id": call_id, "rounds": 16,
                          "constant": 13 + call_id,
                          "input": previous, "output": output})
            constructor = "pair" if call_id < 2 else "many"
            slots += [{"source_kind": f"{constructor}_chip",
                       "registry_key": f"{constructor}_chip",
                       "registry_id": 1 if call_id < 2 else 3,
                       "registry_version": 1, "registry_role": "chip",
                       "call_id": call_id, "proof_index": 1 + 2 * call_id,
                       "claimed_sum_index": 1 + 2 * call_id,
                       "relation_ids": [1395863811]},
                      {"source_kind": f"{constructor}_bridge",
                       "registry_key": f"{constructor}_bridge",
                       "registry_id": 2 if call_id < 2 else 4,
                       "registry_version": 1, "registry_role": "bridge",
                       "call_id": call_id, "proof_index": 2 + 2 * call_id,
                       "claimed_sum_index": 2 + 2 * call_id,
                       "relation_ids": [378353459, 1395863811]}]
            previous = output
        manifest = {"calls": calls, "call_count": count, "slots": slots}
        check_source_call_mapping(source, manifest)
        mutation_counts[count] = check_source_call_mapping_mutations(source, manifest)
        # A serializer-only fixture makes the important asymmetry explicit:
        # source_kind is an unhashed report field, whereas registry_key is
        # hashed. Neither synthetic digest is a native verifier key.
        digest_fixture = copy.deepcopy(manifest)
        digest_fixture.update({
            "registry_manifest_version": 1, "registry_version": 1,
            "source_sha256": "00" * 32, "canonical_ir_sha256": "00" * 32,
            "fixed_root": "00" * 32, "manifest_sha256": "00" * 32,
            "descriptor_sha256": "00" * 32, "slot_count": len(slots),
            "main_columns": 0, "interaction_columns": 0,
            "total_constraints": 0,
        })
        for slot in digest_fixture["slots"]:
            slot.update({
                "trace_log_size": 0, "evaluation_log_size": 0,
                "main_offset": 0, "main_columns": 0,
                "interaction_offset": 0, "interaction_columns": 0,
                "constraint_offset": 0, "n_constraints": 0,
                "preprocessed_indices": [], "air_source_sha256": "00" * 32,
                "program_binding_sha256": "00" * 32,
            })
        unchanged_digest = registry_manifest_digest(digest_fixture)
        changed = copy.deepcopy(digest_fixture)
        changed["slots"][1]["source_kind"] = "many_chip"
        if registry_manifest_digest(changed) != unchanged_digest:
            raise AssertionError("diagnostic source_kind unexpectedly entered digest")
        changed["slots"][1]["registry_key"] = "many_chip"
        if registry_manifest_digest(changed) == unchanged_digest:
            raise AssertionError("registry constructor key escaped digest")
        # This projector checks continuity and freshness, but source text
        # alone does not expose the compiler's absolute circuit addresses.
        # A coordinated fresh retarget remains possible in this *static*
        # model; the sealed native verifier re-inspects actual topology.
        retargeted = copy.deepcopy(manifest)
        retargeted["calls"][0]["input"][0] = 10_000
        retargeted["calls"][0]["output"][0] = 20_000
        if count > 1:
            retargeted["calls"][1]["input"][0] = 20_000
        check_source_call_mapping(source, retargeted)
        changed_source = copy.deepcopy(source)
        changed_source["nodes"][0]["body"][1]["constant"] += 1
        try:
            check_source_call_mapping(changed_source, manifest)
        except AssertionError:
            pass
        else:
            raise AssertionError("source-side chip constant mutation escaped")
    return {"schema": "s31-mixed-source-roster-mapping-static-v1",
            "counts": [1, 3, 8],
            "manifest_mutations_rejected_by_count": mutation_counts,
            "source_mutations_rejected_per_count": 1,
            "fresh_absolute_address_retarget_accepted_without_topology": True}


def build(source: Path, prefix: Path, *, accept: bool = True) -> tuple[Path, Path, Path]:
    run(
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source}",
        "-Ds31-name=general", "-j1", "--prefix", str(prefix), accept=accept,
    )
    root = prefix / "bin"
    return (
        root / "s31-general-mixed-general-prover",
        root / "s31-general-mixed-general-native-verifier",
        root / "s31-general-mixed-general-manifest",
    )


def verify_rejects(verifier: Path, proof: Path, statement: Path) -> None:
    result = subprocess.run((str(verifier), str(proof), str(statement)),
                            text=True, capture_output=True, check=False, timeout=30)
    if result.returncode == 0 or result.returncode < 0:
        raise AssertionError(
            f"native verifier accepted or crashed on changed proof or statement "
            f"(exit {result.returncode}): {proof}, {statement}"
        )


def exercise(work: Path, count: int) -> dict:
    source_value, assignment_value = family(count)
    source = work / f"general-{count}.s31.json"
    assignment = work / f"assignment-{count}.json"
    source.write_text(json.dumps(source_value, separators=(",", ":")))
    assignment.write_text(json.dumps(assignment_value, separators=(",", ":")))
    prover, verifier, manifest_bin = build(source, work / f"build-{count}")
    manifest = json.loads(run(str(manifest_bin)).stdout)
    assert manifest["schema"] == "s31-mixed-component-inspection-general-v3"
    assert manifest["source_sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert manifest["call_count"] == count and manifest["slot_count"] == 1 + 2 * count
    assert manifest["registry_manifest_sha256"] == registry_manifest_digest(manifest)
    relabeled = copy.deepcopy(manifest)
    relabeled["slots"][1]["source_kind"] = "many_chip"
    assert registry_manifest_digest(relabeled) == manifest["registry_manifest_sha256"]
    try:
        check_source_call_mapping(source_value, relabeled)
    except AssertionError:
        pass
    else:
        raise AssertionError("unhashed source-kind relabel escaped independent audit")
    assert [slot["claimed_sum_index"] for slot in manifest["slots"]] == list(range(1 + 2 * count))
    assert [slot["registry_role"] for slot in manifest["slots"]] == [
        "circuit", *(role for _ in range(count) for role in ("chip", "bridge")),
    ]
    assert [slot["registry_id"] for slot in manifest["slots"]] == [
        0, *(id for call in range(count) for id in ((1, 2) if call < 2 else (3, 4))),
    ]
    check_source_call_mapping(source_value, manifest)
    check_source_call_mapping_mutations(source_value, manifest)
    proof = work / f"proof-{count}.bin"
    statement = work / f"statement-{count}.json"
    run(str(prover), str(assignment), str(proof), str(statement))
    run(str(verifier), str(proof), str(statement))
    raw = proof.read_bytes()
    saved = json.loads(statement.read_text())
    assert raw[:len(MAGIC) + 4] == MAGIC + bytes((count, 1 + 2 * count, 3, 0))
    assert saved["schema"] == "s31-mixed-public-words-general-v3"
    assert saved["source_sha256"] == manifest["source_sha256"]
    assert saved["selected_manifest_sha256"] == manifest["manifest_sha256"]
    assert saved["registry_manifest_sha256"] == manifest["registry_manifest_sha256"]
    assert saved["circuit_identity_sha256"] == manifest["circuit_identity_sha256"]
    assert saved["public_words"] == [
        *assignment_value["public_outputs"]["sum"],
        *assignment_value["public_outputs"]["product"],
    ]
    for field, offset in (
        ("source_sha256", len(MAGIC) + 4),
        ("registry_manifest_sha256", len(MAGIC) + 36),
        ("circuit_identity_sha256", len(MAGIC) + 68),
    ):
        assert raw[offset:offset + 32].hex() == saved[field]
    for name, offset in (
        ("magic", 0), ("count", len(MAGIC)),
        ("roster", len(MAGIC) + 1), ("schema", len(MAGIC) + 2),
        ("source", len(MAGIC) + 4), ("registry", len(MAGIC) + 36),
        ("identity", len(MAGIC) + 68),
        *((f"sum{i}", SUMS_OFFSET + 16 * i) for i in range(1 + 2 * count)),
        ("proof_tail", len(raw) - 1),
    ):
        changed = bytearray(raw)
        changed[offset] ^= 1
        altered = work / f"bad-{count}-{name}.bin"
        altered.write_bytes(changed)
        verify_rejects(verifier, altered, statement)
    for field, value in (
        ("schema", "s31-mixed-public-words-n4-v2"),
        ("source_sha256", "0" * 64),
        ("selected_manifest_sha256", "0" * 64),
        ("registry_manifest_sha256", "0" * 64),
        ("circuit_identity_sha256", "0" * 64),
        ("public_words", [0] * 8),
    ):
        altered = work / f"bad-{count}-{field}.json"
        altered.write_text(json.dumps({**saved, field: value}))
        verify_rejects(verifier, proof, altered)
    if count in (1, 3, 8):
        for lane, original in enumerate(saved["public_words"]):
            words = saved["public_words"].copy()
            words[lane] = (original + 1) % MODULUS
            altered = work / f"bad-{count}-public-word-{lane}.json"
            altered.write_text(json.dumps({**saved, "public_words": words}))
            verify_rejects(verifier, proof, altered)
        # Preserve the total QM31 claimed sum while changing two individual
        # component claims. The transcript and installed AIR claims must still
        # reject this coordinated mutation.
        compensated = bytearray(raw)
        first = int.from_bytes(compensated[SUMS_OFFSET:SUMS_OFFSET + 4], "little")
        second_at = SUMS_OFFSET + 16
        second = int.from_bytes(compensated[second_at:second_at + 4], "little")
        compensated[SUMS_OFFSET:SUMS_OFFSET + 4] = ((first + 1) % MODULUS).to_bytes(4, "little")
        compensated[second_at:second_at + 4] = ((second - 1) % MODULUS).to_bytes(4, "little")
        altered = work / f"bad-{count}-compensated-sums.bin"
        altered.write_bytes(compensated)
        verify_rejects(verifier, altered, statement)
        header_end = SUMS_OFFSET + 16 * (1 + 2 * count)
        for label, data in (
            ("truncated-header", raw[:header_end - 1]),
            ("truncated-postcard", raw[:-1]),
            ("trailing-postcard", raw + b"\x00"),
            ("malformed-postcard", raw[:header_end] + b"\xff" * 64),
            ("oversized-wire", raw + b"\x00" * ((16 << 20) + 1 - len(raw))),
        ):
            altered = work / f"bad-{count}-{label}.bin"
            altered.write_bytes(data)
            verify_rejects(verifier, altered, statement)
    malformed = work / f"malformed-{count}.json"
    malformed.write_text(json.dumps({**saved, "unknown_field": 1}))
    verify_rejects(verifier, proof, malformed)
    malformed.write_text(json.dumps(saved)[:-1] + ',"public_words":[0,0,0,0,0,0,0,0]}')
    verify_rejects(verifier, proof, malformed)
    noncanonical = {**saved, "public_words": saved["public_words"].copy()}
    noncanonical["public_words"][0] = MODULUS
    malformed.write_text(json.dumps(noncanonical))
    verify_rejects(verifier, proof, malformed)
    invalid = json.loads(assignment.read_text())
    invalid["private_inputs"]["x"][0] += 1
    wrong = work / f"wrong-{count}.json"
    wrong.write_text(json.dumps(invalid))
    run(str(prover), str(wrong), str(work / "bad.proof"), str(work / "bad.statement"), accept=False)
    invalid = json.loads(assignment.read_text())
    invalid["public_outputs"]["sum"][0] = (invalid["public_outputs"]["sum"][0] + 1) % MODULUS
    wrong.write_text(json.dumps(invalid))
    run(str(prover), str(wrong), str(work / "bad.proof"), str(work / "bad.statement"), accept=False)
    if count in (1, 3, 8):
        changed_source = work / f"changed-source-{count}.s31.json"
        changed_source.write_bytes(source.read_bytes() + b" ")
        _, other_verifier, other_manifest_bin = build(
            changed_source, work / f"changed-source-{count}")
        other_manifest = json.loads(run(str(other_manifest_bin)).stdout)
        if (other_manifest["source_sha256"] != hashlib.sha256(changed_source.read_bytes()).hexdigest() or
                other_manifest["source_sha256"] == manifest["source_sha256"] or
                other_manifest["call_count"] != count or
                other_manifest["slot_count"] != 1 + 2 * count or
                other_manifest["registry_manifest_sha256"] != registry_manifest_digest(other_manifest)):
            raise AssertionError("changed-source verifier was not built for this exact call roster")
        resealed = {**saved,
                    "source_sha256": other_manifest["source_sha256"],
                    "selected_manifest_sha256": other_manifest["manifest_sha256"],
                    "registry_manifest_sha256": other_manifest["registry_manifest_sha256"],
                    "circuit_identity_sha256": other_manifest["circuit_identity_sha256"]}
        malformed.write_text(json.dumps(resealed))
        verify_rejects(other_verifier, proof, malformed)
        resealed_proof = bytearray(raw)
        for field, offset in (
            ("source_sha256", len(MAGIC) + 4),
            ("registry_manifest_sha256", len(MAGIC) + 36),
            ("circuit_identity_sha256", len(MAGIC) + 68),
        ):
            resealed_proof[offset:offset + 32] = bytes.fromhex(resealed[field])
        resealed_path = work / f"bad-{count}-resealed-source.bin"
        resealed_path.write_bytes(resealed_proof)
        rejected = subprocess.run((str(other_verifier), str(resealed_path), str(malformed)),
                                  text=True, capture_output=True, check=False, timeout=30)
        if (rejected.returncode == 0 or rejected.returncode < 0 or
                "InvalidMixedNativeEnvelope" in rejected.stderr or
                "InvalidMixedStatementIdentity" in rejected.stderr):
            raise AssertionError(
                "changed-source resealed proof escaped or failed at a surface mismatch: "
                f"{rejected.stderr}")
    return {"calls": count, "proof_bytes": len(raw), "proof_sha256": hashlib.sha256(raw).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--counts", nargs="+", type=int, default=list(range(1, 9)))
    parser.add_argument("--static", action="store_true",
                        help="check source/manifest mapping and mutants without native builds")
    args = parser.parse_args()
    if args.static:
        print(json.dumps(static_mapping_checks(), sort_keys=True))
        return
    if len(set(args.counts)) != len(args.counts) or any(not 1 <= count <= 8 for count in args.counts):
        parser.error("counts must be distinct values in 1..8")
    with tempfile.TemporaryDirectory(prefix="s31-mixed-general-") as directory:
        work = Path(directory)
        results = []
        for count in args.counts:
            print(f"checking {count}-call mixed profile", file=sys.stderr, flush=True)
            results.append(exercise(work, count))
        print(json.dumps({"schema": "s31-mixed-general-acceptance-v3",
                          "profiles": results, "accepted": True}, sort_keys=True))


if __name__ == "__main__":
    main()
