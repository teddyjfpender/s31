#!/usr/bin/env python3
"""Pinned Lean and complete fixed-row admission for one-field public records.

The checker proves exact-source v2 erasure into the actual typed Program and
checks the public statement with Program.evaluate. A pinned native inspector
exports the fixed cells, which are replayed against a source-derived direct
Gate schedule and the pinned key's preprocessed root. This is an opt-in narrow
release gate; it does not prove the native AIR or PCS/FRI implementation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import invoke  # noqa: E402
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, replay_direct_topology, same_json_shape,
)
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from package.lean_effects_admission import _pinned_checker  # noqa: E402
from package.record_source_fragment import (  # noqa: E402
    check_package_record_source_relation, parse_record_source_fragment,
)
from package.trust import PIN_RE, admitted_snapshot  # noqa: E402
from runtime.proof_inputs import proof_inputs_snapshot  # noqa: E402

REQUIRED = ("source.s31", "source.s31.json", "public-abi.json",
            "typed-structural-derivation.json", "component-manifest.json",
            "cost-report.json", "verification-key.json")


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _lean(checker: Path, files: list[Path]) -> None:
    if any(path.stat().st_size > (131072 if path.name ==
                                  "typed-structural-derivation.json" else 65536)
           for path in files):
        raise ValueError("record Lean input exceeds byte bound")
    try:
        result = subprocess.run([str(checker), *(str(path) for path in files)],
                                capture_output=True, text=True, timeout=30,
                                check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError("pinned Lean record checker did not complete") from exc
    if result.returncode or not result.stdout.startswith(
            "accepted: record-v2 public Program run "):
        raise ValueError("pinned Lean record checker rejected: " +
                         (result.stderr + result.stdout).strip()[:512])


def _source_topology(relation_digest: str, root: str, gates: dict,
                     n_vars: int, n_rows: int) -> dict:
    """Build every fixed cell from the independent source Gate schedule."""
    output = [2, *range(3, 11)]
    uses = [0] * n_vars
    for kind in ("add", "sub", "mul", "pointwise_mul"):
        for gate in gates[kind]:
            uses[gate["in0"]] += 1
            uses[gate["in1"]] += 1
    for address in output:
        uses[address] += 1
    columns = [[] for _ in DIRECT_COLUMN_IDS]
    for flag, kind in enumerate(("add", "sub", "mul", "pointwise_mul")):
        for gate in gates[kind]:
            cells = [*(int(index == flag) for index in range(4)),
                     gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]]
            for column, value in zip(columns, cells, strict=True):
                column.append(value)
    if any(len(column) != n_rows for column in columns):
        raise ValueError("source-derived Gate column length differs")
    return {"schema": "s31-direct-gate-topology-v2",
            "program_sha256": relation_digest, "preprocessed_root": root,
            "n_vars": n_vars, "output": output,
            **gates, "permutation_ends": [], "permutation_inputs": [],
            "permutation_outputs": [], "first_permutation_row": n_rows,
            "columns": [{"id": name, "values": values}
                        for name, values in zip(DIRECT_COLUMN_IDS, columns, strict=True)]}


def check_fixed_rows(snapshot: Path, manifest: dict) -> None:
    """Rebuild the one-field graph from source, then replay every fixed cell."""
    if (manifest.get("lowering") != "direct-gate" or
            manifest.get("text_frontend_version") != 1 or
            not set(REQUIRED).issubset(manifest.get("artifacts", {}))):
        raise ValueError("record row gate requires a direct-gate text package")
    check_package_record_source_relation(snapshot)
    source = (snapshot / "source.s31").read_bytes()
    relation_bytes = (snapshot / "source.s31.json").read_bytes()
    relation = json.loads(relation_bytes)
    source_relation = parse_record_source_fragment(source)
    if not same_json_shape(relation, source_relation):
        raise ValueError("record relation differs from independent source parse")
    inputs, nodes, outputs = (relation[key] for key in
                              ("inputs", "nodes", "public_outputs"))
    if (len(inputs) != 1 or len(nodes) != 1 or len(outputs) != 1 or
            inputs[0] != {"name": "_s31_abi_input_0", "kind": "m31",
                          "length": 1, "visibility": "public"} or
            relation["assertions"] != [] or
            nodes[0]["op"] != "add" or
            nodes[0]["lhs"] != inputs[0]["name"] or
            nodes[0]["rhs"] != inputs[0]["name"] or
            outputs[0] != nodes[0]["name"]):
        raise ValueError("record is outside the reviewed one-field public add class")
    key = json.loads((snapshot / "verification-key.json").read_bytes())
    component = json.loads((snapshot / "component-manifest.json").read_bytes())
    report = json.loads((snapshot / "cost-report.json").read_bytes())
    abi = json.loads((snapshot / "public-abi.json").read_bytes())
    relation_digest = _sha(relation_bytes)
    if (key.get("schema") != "s31-verification-key-direct-record-v2" or
            key.get("profile") != "direct-m31-v4" or key.get("chip") is not None or
            key.get("program_sha256") != relation_digest or
            key.get("fri", {}).get("fold_step") != 1 or
            component.get("schema") != "s31-component-manifest-direct-gate-v1" or
            component.get("profile") != "direct-m31-v4" or
            component.get("program_sha256") != relation_digest or
            report.get("program_sha256") != relation_digest or
            not same_json_shape(component, key.get("component_manifest")) or
            not same_json_shape(component, report.get("component_manifest")) or
            any(component.get(field) != key.get(field) for field in
                ("canonical_ir_sha256", "circuit_hash", "air_bundle_sha256")) or
            any(item.get("preprocessed_root") != key.get("preprocessed_root")
                for item in (component, report)) or
            abi.get("schema") != "s31-public-abi-v2" or
            key.get("public_abi_sha256") != abi.get("boundary_sha256")):
        raise ValueError("record key, component, report, or ABI differs")
    input_name, node_name = inputs[0]["name"], nodes[0]["name"]
    expected_map = [
        {"name": input_name, "canonical_id": 0, "qm31_start": 0, "qm31_end": 0},
        {"name": node_name, "canonical_id": 1, "qm31_start": 0, "qm31_end": 1},
    ]
    for row in expected_map:
        for kind in ("eq", "triple_xor", "m31_to_u32", "blake_g"):
            row[f"{kind}_start"] = row[f"{kind}_end"] = 0
    expected_binding = [
        {"name": input_name, "word_start": 0, "word_count": 1,
         "conversion_qm31_start": 1, "conversion_qm31_end": 1,
         "conversion_m31_to_u32_start": 0, "conversion_m31_to_u32_end": 0,
         "binding_qm31_start": 2, "binding_qm31_end": 3},
        {"name": node_name, "word_start": 1, "word_count": 1,
         "conversion_qm31_start": 1, "conversion_qm31_end": 2,
         "conversion_m31_to_u32_start": 0, "conversion_m31_to_u32_end": 0,
         "binding_qm31_start": 3, "binding_qm31_end": 4},
    ]
    if (not same_json_shape(report.get("source_map"), expected_map) or
            not same_json_shape(report.get("public_binding"), expected_binding) or
            not same_json_shape(report.get("input_packing"), [
                {"name": input_name, "lanes": 1, "qm31_wires": 1}])):
        raise ValueError("record native source spans or public words differ")
    expected, variables, rows, _ = exact_direct_gate_schedule({
        "lane_count": 1, "input_count": 1,
        "instructions": [{"id": 1, "name": node_name, "op": "add",
                          "lhs": 0, "rhs": 0}], "output": 1})
    topology = _source_topology(relation_digest, key["preprocessed_root"],
                                expected, variables, rows)
    replay_direct_topology(topology, component, report, relation_digest)
    prover = snapshot / "bin" / f"s31-{manifest['name']}-prover"
    with tempfile.TemporaryDirectory(prefix="s31-record-fixed-columns-") as temp:
        columns_path = Path(temp) / "fixed-columns.json"
        columns_path.write_text(json.dumps({
            "schema": "s31-direct-gate-fixed-columns-v1",
            "fixed_columns": [item["values"] for item in topology["columns"]],
        }, separators=(",", ":")))
        recommitted = json.loads(invoke(str(prover),
                                        "inspect-fixed-root-from-columns",
                                        str(columns_path)))
    if (type(recommitted) is not dict or
            set(recommitted) != {"schema", "fixed_root"} or
            recommitted["schema"] != "s31-direct-gate-recommitted-fixed-root-v1" or
            type(recommitted["fixed_root"]) is not str or
            PIN_RE.fullmatch(recommitted["fixed_root"]) is None or
            recommitted["fixed_root"] != key["preprocessed_root"]):
        raise ValueError("source-derived fixed Gate columns differ from pinned key root")


def verify(package: Path, proof: Path, statement: Path,
           pins: dict[str, str], checker_path: Path,
           checker_sha256: str) -> str:
    with proof_inputs_snapshot(proof, statement) as (captured_proof, captured_statement):
        with _pinned_checker(checker_path, checker_sha256) as checker:
            with admitted_snapshot(package, pins) as (snapshot, manifest):
                files = [snapshot / name for name in (
                    "source.s31", "typed-structural-derivation.json",
                    "source.s31.json", "public-abi.json")]
                _lean(checker, files + [captured_statement])
                check_fixed_rows(snapshot, manifest)
                verifier = snapshot / "bin" / f"s31-{manifest['name']}-native-verifier"
                key = snapshot / "verification-key.json"
                invoke(str(verifier), "check-key", str(key))
                return invoke(str(verifier), str(captured_proof),
                              str(captured_statement), str(key))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--statement", type=Path, required=True)
    parser.add_argument("--lean-checker", type=Path, required=True)
    parser.add_argument("--lean-checker-sha256", required=True)
    for kind in ("source", "key", "prover", "verifier", "text"):
        parser.add_argument(f"--{kind}-sha256", required=True)
    args = parser.parse_args(argv)
    pins = {kind: getattr(args, f"{kind}_sha256") for kind in
            ("source", "key", "prover", "verifier", "text")}
    try:
        print(verify(args.package, args.proof, args.statement, pins,
                     args.lean_checker, args.lean_checker_sha256), end="")
    except (OSError, ValueError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"record release rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
