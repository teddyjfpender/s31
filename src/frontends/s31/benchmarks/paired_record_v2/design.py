"""Deterministic, native-free paired record ABI v2 workload inventory.

Every generic/mixed pair is built from exactly the same normalized source
bytes and canonical typed statement. This module never invokes Zig.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import binding_digest, statement_from_assignment
from oracle import evaluate_relation
from package.context import parse_source_json

P = (1 << 31) - 1
DESIGN_PATH = ROOT / "design/s31/measurements/language/paired-record-v2-prospective.json"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def design() -> dict:
    value = json.loads(DESIGN_PATH.read_bytes())
    if (value.get("schema") != "s31-paired-record-v2-prospective-v1" or
            value.get("status") != "designed-not-frozen-no-native-observations" or
            value.get("train_call_counts") != [1, 2, 4, 6] or
            value.get("heldout_call_counts") != [3, 5, 7, 8] or
            value.get("assignments_per_call_count") != 100 or
            value.get("source_template") != "src/frontends/s31/examples/boundary/record_mixed1.s31.json" or
            value.get("source_version") != 2 or
            value.get("generic_lowering") != "direct-gate" or
            value.get("mixed_lowering") != "direct-mixed-general" or
            value.get("build_mode") != "ReleaseFast" or
            value.get("assignment_seed") != 9102400 or
            value.get("balanced_order_seed") != "s31-paired-record-v2-order-20261011" or
            value.get("bootstrap_seed") != 9102419 or
            value.get("bootstrap_resamples") != 10000 or
            value.get("minimum_available_disk_bytes_before_native_phase") != 8 * 1024**3 or
            "both arms invoke prover without internal native verification" not in
                value.get("first_verified_proof_boundary", "") or
            "externally timestamp the full phase-root digest before audit or summary" not in
                value.get("phase_integrity_gate", "") or
            "audit rederives every reported build duration" not in
                value.get("build_integrity_gate", "") or
            "identical complete FriConfigV2 and interaction PoW bits" not in
                value.get("live_security_config_gate", "") or
            value.get("automatic_lowering_selection_enabled") is not False or
            value.get("speedup_threshold", "missing") is not None or
            set(value.get("prefreeze_pins", {})) != {
                "source_base_commit", "compiler_sha256", "engine_gitlink_commit",
                "measurement_tool_sha256", "host_identity",
                "generated_inventory_sha256",
            } or
            any(pin is not None for pin in value["prefreeze_pins"].values())):
        raise ValueError("paired design was changed or masquerades as frozen")
    if sorted(value["train_call_counts"] + value["heldout_call_counts"]) != list(range(1, 9)):
        raise ValueError("paired call-count roster changed")
    return value


def flat(source: dict) -> dict:
    raw = {**source, "version": 1}
    raw.pop("public_abi")
    return raw


def source(count: int, cfg: dict) -> bytes:
    if count not in range(1, 9):
        raise ValueError("supported call count is 1..8")
    base = parse_source_json((ROOT / cfg["source_template"]).read_bytes())
    if base.get("version") != 2 or len(base.get("inputs", [])) != 1 or \
            len(base.get("public_outputs", [])) != 1:
        raise ValueError("record source template differs from admitted ABI")
    input_name = base["inputs"][0]["name"]
    output_name = base["public_outputs"][0]
    nodes = []
    for index in range(count):
        nodes.append({"name": f"r{index}", "op": "repeat",
                      "lhs": input_name if index == 0 else f"r{index - 1}",
                      "rounds": 16,
                      "body": [{"op": "square"}, {"op": "add_const", "constant": 13 + index}]})
    nodes.append({"name": output_name, "op": "add", "lhs": f"r{count - 1}",
                  "rhs": input_name})
    relation = {**base, "name": f"paired_record_v2_n{count}", "nodes": nodes}
    binding_digest(flat(relation), relation["public_abi"])
    return canonical(relation)


def case(count: int, index: int, cfg: dict) -> tuple[bytes, bytes, bytes]:
    if not 0 <= index < cfg["assignments_per_call_count"]:
        raise ValueError("assignment index out of range")
    source_bytes = source(count, cfg)
    relation = parse_source_json(source_bytes)
    seed = cfg["assignment_seed"] + count * 100_000 + index * 17
    words = [(seed * (lane + 11) + lane * lane + 3) % P for lane in range(4)]
    output = words[:]
    for call in range(count):
        for _ in range(16):
            output = [(value * value + 13 + call) % P for value in output]
    output = [(value + start) % P for value, start in zip(output, words)]
    assignment = {
        "public_inputs": {relation["inputs"][0]["name"]: words},
        "private_inputs": {},
        "public_outputs": {relation["public_outputs"][0]: output},
    }
    independent = evaluate_relation(flat(relation), assignment)
    if independent != assignment["public_outputs"]:
        raise ValueError("independent relation oracle disagrees with arithmetic recurrence")
    typed = statement_from_assignment(relation, assignment)
    decoded = json.loads(typed)
    descriptors = [*relation["public_abi"]["inputs"][0]["leaves"],
                   *relation["public_abi"]["result"]["leaves"]]
    if (decoded.get("version") != 2 or
            decoded.get("abi_sha256") != binding_digest(flat(relation), relation["public_abi"]) or
            len(decoded.get("leaves", [])) != 2 or
            [leaf.get("path") for leaf in decoded["leaves"]] !=
                [leaf["path"] for leaf in descriptors] or
            decoded["leaves"][0].get("words") != words or
            decoded["leaves"][1].get("words") != output):
        raise ValueError("typed statement differs from independent record-path/value check")
    return source_bytes, canonical(assignment), typed


def balanced_order(count: int, cfg: dict) -> list[str]:
    """Freeze a balanced but randomized per-count arm order before timing."""
    import random

    n = cfg["assignments_per_call_count"]
    if n % 2:
        raise ValueError("balanced order requires an even sample count")
    order = ["generic-first"] * (n // 2) + ["mixed-first"] * (n // 2)
    seed = int(sha(f"{cfg['balanced_order_seed']}:{count}".encode()), 16)
    random.Random(seed).shuffle(order)
    return order


def inventory(cfg: dict) -> dict:
    result = {}
    for split, counts in (("train", cfg["train_call_counts"]),
                          ("heldout", cfg["heldout_call_counts"])):
        rows = {}
        for count in counts:
            generated = [case(count, index, cfg) for index in range(cfg["assignments_per_call_count"])]
            source_bytes = generated[0][0]
            if any(row[0] != source_bytes for row in generated):
                raise ValueError("pair source bytes differ across assignments")
            relation = parse_source_json(source_bytes)
            rows[str(count)] = {
                "source_sha256": sha(source_bytes),
                "semantic_relation_sha256": sha(canonical(flat(relation))),
                "public_record_abi_sha256": binding_digest(flat(relation), relation["public_abi"]),
                "assignment_sha256": [sha(row[1]) for row in generated],
                "statement_sha256": [sha(row[2]) for row in generated],
                "order": balanced_order(count, cfg),
            }
        result[split] = rows
    all_sources = [entry["source_sha256"] for split in result.values() for entry in split.values()]
    all_assignments = [digest for split in result.values() for entry in split.values()
                       for digest in entry["assignment_sha256"]]
    if len(set(all_sources)) != 8 or len(set(all_assignments)) != 800:
        raise ValueError("paired inventory reuses source or assignment bytes")
    return result


if __name__ == "__main__":
    cfg = design()
    print(json.dumps({"schema": "s31-paired-record-v2-inventory-preview",
                      "sha256": sha(canonical(inventory(cfg))),
                      "cases": 8, "assignments": 800, "arm_trials": 1600}, sort_keys=True))
