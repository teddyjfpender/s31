"""Native-free, prospective source-shape transfer inventory for mixed cost v1.

This reads the old committed protocol only for source/assignment/claim hashes.
It never reads the old timed corpus, held-out evaluation, or native proof files.
No command in this module starts a native build or measures a proof.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/paired_record_v2"))
sys.path.insert(0, str(HERE))  # transfer modules win over paired-study names

from abi.binding_v2 import binding_digest, statement_from_assignment  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import parse_source_json  # noqa: E402
from design import canonical, flat, sha  # noqa: E402

P = (1 << 31) - 1
DESIGN_PATH = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-prospective.json"
REFERENCE_PATH = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-protocol.json"
SHAPES = ("control", "feeder", "fork", "deep32")
COUNTS = (2, 4, 6)
SCHEMA = "s31-mixed-stage-cost-transfer-v1-prospective"


def design() -> dict:
    value = json.loads(DESIGN_PATH.read_bytes())
    gate = {
        "minimum_programs": 12,
        "minimum_verified_trials_per_program": 30,
        "control_wall_program_median_p90_relative_error_max": .25,
        "control_proof_program_median_p90_relative_error_max": .10,
        "transfer_wall_program_median_p90_relative_error_max": .30,
        "transfer_proof_program_median_p90_relative_error_max": .15,
        "wall_trial_interval_coverage_by_shape_min": .75,
        "proof_trial_interval_coverage_by_shape_min": .80,
        "wall_median_interval_upper_to_measured_median_max": 8.0,
        "proof_median_interval_upper_to_measured_median_max": 1.5,
    }
    if (value.get("schema") != SCHEMA or
            value.get("status") != "design-only-no-native-measurements" or
            value.get("reference_protocol_sha256") !=
                "6eeade0dca2f1052c7865fc76849241058b2b3212daf4bcb93b9fbb57aa75d9a" or
            value.get("reference_train_model_sha256") !=
                "92d4bc1847f7ad69b08c3405e84f7df7e69e9492f403fd7a6286d59c75e9e9f3" or
            value.get("reference_model_anchor_commit") !=
                "52cdce6942579e9b10f0b953df125bd078b6ede8" or
            value.get("source_template") !=
                "src/frontends/s31/examples/boundary/record_mixed1.s31.json" or
            value.get("source_name_prefix") != "mixed_stage_transfer_v1_" or
            value.get("shapes") != list(SHAPES) or
            value.get("call_counts") != list(COUNTS) or
            value.get("assignments_per_program") != 30 or
            value.get("assignment_seed") != 2026101127 or
            value.get("trial_order") !=
                "sha256-shuffled-per-assignment-index-across-12-programs" or
            value.get("build_mode") != "ReleaseFast" or
            value.get("lowering") != "direct-mixed-general" or
            value.get("minimum_available_disk_bytes_at_phase_start") != 12 * 1024**3 or
            value.get("minimum_available_disk_bytes_before_native_unit") != 8 * 1024**3 or
            value.get("reference_heldout_observations_allowed_in_fit_or_gate_selection") is not False or
            value.get("refitting_allowed") is not False or
            value.get("automatic_lowering_selection_enabled") is not False or
            value.get("speedup_claim_enabled") is not False or
            value.get("diagnostic_gates") != gate):
        raise ValueError("transfer design differs from its reviewed prospective roster")
    return value


def _repeat(name: str, lhs: str, count: int, shape: str) -> dict:
    return {"name": name, "op": "repeat", "lhs": lhs,
            "rounds": 32 if shape == "deep32" else 16,
            "body": [{"op": "square"},
                     {"op": "add_const", "constant": 13 + count}]}


def source(shape: str, count: int, cfg: dict) -> bytes:
    if shape not in SHAPES or count not in COUNTS:
        raise ValueError("source shape or call count is outside the prospective roster")
    base = parse_source_json((ROOT / cfg["source_template"]).read_bytes())
    if (base.get("version") != 2 or len(base.get("inputs", [])) != 1 or
            len(base.get("public_outputs", [])) != 1):
        raise ValueError("record ABI v2 template changed")
    input_name = base["inputs"][0]["name"]
    output_name = base["public_outputs"][0]
    nodes: list[dict] = []
    if shape == "fork":
        for index in range(count):
            nodes.append(_repeat(f"r{index}", input_name, index, shape))
        previous = "r0"
        for index in range(1, count):
            name = f"sum{index}"
            nodes.append({"name": name, "op": "add", "lhs": previous,
                          "rhs": f"r{index}"})
            previous = name
    else:
        previous = input_name
        for index in range(count):
            if shape == "feeder":
                add_name, mul_name = f"feed_add{index}", f"feed_mul{index}"
                nodes.append({"name": add_name, "op": "add_const",
                              "lhs": previous, "constant": 5 + index})
                nodes.append({"name": mul_name, "op": "mul_const",
                              "lhs": add_name, "constant": 3 + index})
                previous = mul_name
            nodes.append(_repeat(f"r{index}", previous, index, shape))
            previous = f"r{index}"
    nodes.append({"name": output_name, "op": "add", "lhs": previous,
                  "rhs": input_name})
    relation = {**base, "name": f"{cfg['source_name_prefix']}{shape}_n{count}",
                "nodes": nodes}
    binding_digest(flat(relation), relation["public_abi"])
    return canonical(relation)


def _rounds(words: list[int], index: int, shape: str) -> list[int]:
    values = words[:]
    for _ in range(32 if shape == "deep32" else 16):
        values = [(value * value + 13 + index) % P for value in values]
    return values


def output_words(shape: str, count: int, words: list[int]) -> list[int]:
    if shape == "fork":
        outputs = [_rounds(words, index, shape) for index in range(count)]
        result = [sum(lane) % P for lane in zip(*outputs)]
    else:
        result = words[:]
        for index in range(count):
            if shape == "feeder":
                result = [((value + 5 + index) * (3 + index)) % P
                          for value in result]
            result = _rounds(result, index, shape)
    return [(value + start) % P for value, start in zip(result, words)]


def case(shape: str, count: int, index: int, cfg: dict) -> tuple[bytes, bytes, bytes]:
    if shape not in SHAPES or count not in COUNTS or \
            not 0 <= index < cfg["assignments_per_program"]:
        raise ValueError("case is outside the prospective roster")
    source_bytes = source(shape, count, cfg)
    relation = parse_source_json(source_bytes)
    seed = (cfg["assignment_seed"] + SHAPES.index(shape) * 10_000_000 +
            count * 100_000 + index * 17)
    words = [(seed * (lane + 11) + lane * lane + 3) % P for lane in range(4)]
    output = output_words(shape, count, words)
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output}}
    if evaluate_relation(flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent relation oracle disagrees with transfer generator")
    typed = statement_from_assignment(relation, assignment)
    return source_bytes, canonical(assignment), typed


def reference_inventory(cfg: dict) -> tuple[dict, dict[str, set[str]]]:
    if sha(REFERENCE_PATH.read_bytes()) != cfg["reference_protocol_sha256"]:
        raise ValueError("reference protocol changed after frozen v1 study")
    protocol = json.loads(REFERENCE_PATH.read_bytes())
    if protocol.get("schema") != "s31-mixed-stage-cost-v1-protocol":
        raise ValueError("wrong reference protocol")
    old = {"source": set(), "assignment": set(), "typed_statement": set()}
    for split in ("train", "heldout"):
        for record in protocol["inventory"][split].values():
            old["source"].add(record["source_sha256"])
            old["assignment"].update(record["assignment_sha256"])
            old["typed_statement"].update(record["typed_statement_sha256"])
    return protocol, old


def inventory(cfg: dict) -> dict:
    _, old = reference_inventory(cfg)
    seen = {name: set(values) for name, values in old.items()}
    result = {}
    for shape in SHAPES:
        for count in COUNTS:
            name = f"{shape}_n{count}"
            cases = [case(shape, count, index, cfg)
                     for index in range(cfg["assignments_per_program"])]
            source_hash = sha(cases[0][0])
            assignment_hashes = [sha(row[1]) for row in cases]
            statement_hashes = [sha(row[2]) for row in cases]
            for kind, hashes in (("source", [source_hash]),
                                 ("assignment", assignment_hashes),
                                 ("typed_statement", statement_hashes)):
                if len(set(hashes)) != len(hashes) or seen[kind] & set(hashes):
                    raise ValueError(f"prospective {kind} reused old or new evidence")
                seen[kind].update(hashes)
            if any(row[0] != cases[0][0] for row in cases):
                raise ValueError("source bytes vary within a program")
            result[name] = {"shape": shape, "call_count": count,
                            "total_rounds": count * (32 if shape == "deep32" else 16),
                            "chip_slots": 1 + 2 * count,
                            "source_sha256": source_hash,
                            "assignment_sha256": assignment_hashes,
                            "typed_statement_sha256": statement_hashes}
    return result


def trial_order(index: int, cfg: dict) -> list[str]:
    """Spread every source's trials over the whole phase without timing input."""
    if not 0 <= index < cfg["assignments_per_program"]:
        raise ValueError("trial index outside prospective roster")
    names = [f"{shape}_n{count}" for shape in SHAPES for count in COUNTS]
    return sorted(names, key=lambda name: sha(
        f"mixed-transfer-v1-order:{cfg['assignment_seed']}:{index}:{name}".encode()))


def materialize(out: Path, cfg: dict) -> dict:
    """Write only source/assignment/statement bytes, never timed evidence."""
    if out.exists():
        raise ValueError("fresh materialization path required")
    expected = inventory(cfg)
    out.mkdir(parents=True, exist_ok=False)
    for name, record in expected.items():
        directory = out / name
        directory.mkdir()
        shape, count = record["shape"], record["call_count"]
        for index in range(cfg["assignments_per_program"]):
            source_bytes, assignment, statement = case(shape, count, index, cfg)
            if index == 0:
                (directory / "source.s31.json").write_bytes(source_bytes)
            if (sha(source_bytes) != record["source_sha256"] or
                    sha(assignment) != record["assignment_sha256"][index] or
                    sha(statement) != record["typed_statement_sha256"][index]):
                raise ValueError("materialized bytes differ from prospective inventory")
            (directory / f"assignment-{index:02d}.json").write_bytes(assignment)
            (directory / f"statement-{index:02d}.json").write_bytes(statement)
    return {"programs": len(expected),
            "assignments": len(expected) * cfg["assignments_per_program"],
            "inventory_sha256": sha(canonical(expected))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("preview", "materialize"))
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    cfg = design()
    if args.command == "materialize":
        if args.out is None:
            parser.error("materialize requires --out")
        print(json.dumps(materialize(args.out, cfg), sort_keys=True))
    else:
        rows = inventory(cfg)
        print(json.dumps({"schema": "s31-mixed-stage-cost-transfer-v1-preview",
                          "inventory_sha256": sha(canonical(rows)),
                          "programs": len(rows),
                          "assignments": len(rows) * cfg["assignments_per_program"]},
                         sort_keys=True))


if __name__ == "__main__":
    main()
