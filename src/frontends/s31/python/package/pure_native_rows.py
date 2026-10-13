"""Source-bound native rows for short all-public M31 arithmetic graphs.

The four-lane case already has a separate direct-gate certificate. This
checker reuses its full exported-column/manifest replay, then compares every
native gate against an independent, shape-indexed schedule. The fixed-root
comparison relies on the pinned native inspector and verifier; this is not a
PCS/FRI soundness theorem. Static tuple construction and projection are
admitted only when exact source bytes independently erase to that graph.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Any

from package.correspondence import (check_exported_root, parse_canonical_json,
                                    replay_direct_topology, same_json_shape)
from package.context import AIR_BUNDLE_SHA256, PROJECTION_SHA256
from package.direct_gate_schedule import exact_direct_gate_schedule
from package.manifest_digest import direct_gate_v2_digest
from package.source_relation_fragment import check_source_relation_certificate
from package.source_relation_fragment import (LEAN_EFFECTS_PROFILE,
                                              LEAN_SEMANTIC_PROFILE,
                                              parse_source_fragment)

SCHEMA = "s31-pure-linear-native-rows-v1"
ARTIFACT = "pure-native-rows-certificate.json"
TOPOLOGY = "gate-topology.json"


class UnsupportedPureNativeRows(ValueError):
    """The source-bound graph has no reviewed short-lane native schedule."""


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def admitted_ssa(certificate: dict[str, Any], source_bytes: bytes | None = None) -> bool:
    """Admit pure arithmetic or a checked static product erased to that graph.

    Effectful-profile certificates are eligible only when exact source bytes
    independently parse as a static product. The graph restrictions below
    then exclude constants, assertions, private inputs, and unsupported AIR
    layouts. Omitting source bytes never admits that wider profile.
    """
    profile = certificate.get("lean_semantic_profile")
    if certificate.get("unmodeled_features") != []:
        return False
    if profile == LEAN_EFFECTS_PROFILE:
        if source_bytes is None:
            return False
        products: list[bool] = []
        try:
            parse_source_fragment(source_bytes, _static_products=products)
        except ValueError:
            return False
        if products != [True]:
            return False
    elif profile != LEAN_SEMANTIC_PROFILE:
        return False
    ssa = certificate["ssa"]
    inputs, nodes, lanes = ssa["inputs"], ssa["nodes"], ssa["lane_count"]
    input_count = len(inputs)
    if (type(lanes) is not int or
            not ((input_count == 1 and 1 <= lanes <= 3) or
                 (input_count == 2 and 1 <= lanes <= 2)) or
            any(item["id"] != index or item["visibility"] != "public"
                for index, item in enumerate(inputs)) or
            not 1 <= len(nodes) <= 16 or ssa["assertions"]):
        return False
    seen: set[tuple[str, int, int]] = set()
    for index, node in enumerate(nodes, input_count):
        op, lhs, rhs = node["op"], node["lhs"], node["rhs"]
        if (node["id"] != index or op not in {"add", "sub", "mul"} or
                type(lhs) is not int or type(rhs) is not int or
                not 0 <= lhs < index or not 0 <= rhs < index or
                (op != "sub" and lhs > rhs)):
            return False
        key = (op, lhs, rhs)
        if key in seen:
            return False
        seen.add(key)
    # Selecting a raw public input skips the native unpack conversion rows.
    # The reviewed schedule applies only when the selected value is a node.
    return (type(ssa["output"]) is int and
            input_count <= ssa["output"] < input_count + len(nodes))


def _read(package: Path, name: str) -> dict[str, Any]:
    return parse_canonical_json((package / name).read_bytes(), name)


def make_certificate(package: Path) -> dict[str, Any]:
    """Recompute source, public projection, full fixed cells and sealed root."""
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    source_certificate_bytes = (package / "source-relation-certificate.json").read_bytes()
    source_certificate = check_source_relation_certificate(
        source_bytes, relation_bytes, source_certificate_bytes)
    if not admitted_ssa(source_certificate, source_bytes):
        raise UnsupportedPureNativeRows("outside reviewed one/two public input pure graph")
    ssa = source_certificate["ssa"]
    lanes = ssa["lane_count"]
    inputs = ssa["inputs"]
    input_count = len(inputs)
    manifest, key, report, component, topology = (
        _read(package, name) for name in ("manifest.json", "verification-key.json",
                                     "cost-report.json", "component-manifest.json",
                                     TOPOLOGY))
    relation = _read(package, "source.s31.json")
    relation_sha256 = _hash(relation_bytes)
    if (manifest.get("lowering") != "direct-gate" or
            not same_json_shape(manifest.get("fri_fold_step"), 1) or
            manifest.get("name") != relation["name"] or
            manifest.get("source_text_sha256") != _hash(source_bytes) or
            manifest.get("program_sha256") != relation_sha256 or
            key.get("schema") != "s31-verification-key-direct-manifest-v2" or
            key.get("profile") != "direct-m31-v4" or
            key.get("chip") is not None or
            key.get("projection_sha256") != PROJECTION_SHA256 or
            key.get("air_bundle_sha256") != AIR_BUNDLE_SHA256 or
            not same_json_shape(key.get("fri", {}).get("fold_step"), 1) or
            key.get("program_sha256") != relation_sha256 or
            component.get("schema") != "s31-component-manifest-direct-gate-v2" or
            component.get("profile") != "direct-m31-v4" or
            not same_json_shape(component.get("claimed_sums"), 1) or
            key.get("manifest_precommitment_sha256") != direct_gate_v2_digest(component) or
            report.get("manifest_precommitment_sha256") != key.get("manifest_precommitment_sha256") or
            not same_json_shape(component, key.get("component_manifest")) or
            not same_json_shape(component, report.get("component_manifest")) or
            any(not same_json_shape(report.get(field), key.get(field)) for field in (
                "program_sha256", "canonical_ir_sha256", "profile", "chip",
                "preprocessed_root", "circuit_hash", "padded", "trace_log_size", "fri")) or
            any(not same_json_shape(component.get(field), key.get(field)) for field in (
                "program_sha256", "canonical_ir_sha256", "preprocessed_root",
                "circuit_hash", "air_bundle_sha256")) or
            topology.get("schema") != "s31-direct-gate-topology-v2" or
            any(value.get("preprocessed_root") != key.get("preprocessed_root")
                for value in (component, report))):
        raise ValueError("short-lane native key or component manifest differs from source")
    if not check_exported_root(topology, key):
        raise ValueError("short-lane topology lacks an exported fixed root")
    expected_abi = {
        "schema": "s31-public-abi-v1",
        "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
        "public_inputs": [{"name": item["name"], "kind": "m31", "length": lanes}
                          for item in inputs],
        "public_outputs": [{"name": relation["public_outputs"][0],
                            "kind": "m31", "length": lanes}],
    }
    if not same_json_shape(_read(package, "public-abi.json"), expected_abi):
        raise ValueError("short-lane public ABI differs from source")
    if not same_json_shape(report.get("input_packing"), [
            {"name": item["name"], "lanes": lanes, "qm31_wires": 1}
            for item in inputs]):
        raise ValueError("short-lane input packing differs from source")
    packed_rows_per_input = 2 * (lanes - 1)
    packed_rows = input_count * packed_rows_per_input
    expected_map = []
    for index, name in enumerate([*(item["name"] for item in inputs),
                                  *(node["name"] for node in ssa["nodes"])]):
        if index < input_count:
            start = index * packed_rows_per_input
            end = start + packed_rows_per_input
        else:
            start = packed_rows + index - input_count
            end = start + 1
        row = {"name": name, "canonical_id": index,
               "qm31_start": start, "qm31_end": end}
        for component_name in ("eq", "triple_xor", "m31_to_u32", "blake_g"):
            row[f"{component_name}_start"] = 0
            row[f"{component_name}_end"] = 0
        expected_map.append(row)
    if not same_json_shape(report.get("source_map"), expected_map):
        raise ValueError("short-lane native source spans differ from checked SSA")
    source_end = packed_rows + len(ssa["nodes"])
    binding_start = source_end + 2 * lanes - 1
    expected_bindings = []
    for index, name in enumerate((*(item["name"] for item in inputs),
                                  relation["public_outputs"][0])):
        start = index * lanes
        conversion_start = source_end
        conversion_end = source_end if index < input_count else binding_start
        expected_bindings.append({
            "name": name, "word_start": start, "word_count": lanes,
            "conversion_qm31_start": conversion_start,
            "conversion_qm31_end": conversion_end,
            "conversion_m31_to_u32_start": 0, "conversion_m31_to_u32_end": 0,
            "binding_qm31_start": binding_start + start,
            "binding_qm31_end": binding_start + start + lanes,
        })
    if not same_json_shape(report.get("public_binding"), expected_bindings):
        raise ValueError("short-lane public word projection differs from source")

    expected_gates, n_vars, n_rows, source_gates = exact_direct_gate_schedule({
        "lane_count": lanes, "input_count": input_count,
        "instructions": ssa["nodes"], "output": ssa["output"]})
    actual_gates = replay_direct_topology(topology, component, report, relation_sha256)
    if (not same_json_shape(topology["n_vars"], n_vars) or
            not same_json_shape(topology["first_permutation_row"], n_rows) or
            any(not same_json_shape(actual_gates[kind], expected_gates[kind])
                for kind in ("add", "sub", "mul", "pointwise_mul"))):
        raise ValueError("short-lane native gates differ from source-derived full schedule")
    source_rows = []
    kinds = ("add", "sub", "mul", "pointwise_mul")
    for node, gate in zip(ssa["nodes"], source_gates, strict=True):
        kind = "pointwise_mul" if node["op"] == "mul" else node["op"]
        position = expected_gates[kind].index({field: gate[field] for field in ("in0", "in1", "out")})
        trace_row = sum(len(expected_gates[prior]) for prior in kinds[:kinds.index(kind)]) + position
        source_rows.append({"id": node["id"], "op": node["op"],
                            "trace_row": trace_row, "in0": gate["in0"],
                            "in1": gate["in1"], "out": gate["out"]})
    return {"schema": SCHEMA, "capability": "source-relation-to-native-fixed-rows-only",
            "source_sha256": _hash(source_bytes), "relation_sha256": relation_sha256,
            "source_relation_certificate_sha256": _hash(source_certificate_bytes),
            "topology_sha256": _hash((package / TOPOLOGY).read_bytes()),
            "preprocessed_root": key["preprocessed_root"],
            "lane_count": lanes, "source_rows": source_rows,
            "gate_counts": {kind: len(expected_gates[kind]) for kind in kinds}}


def verify_artifact(package: Path, manifest: dict[str, Any]) -> bool:
    """Require this artifact exactly for admitted short-lane text packages."""
    artifacts = manifest["artifacts"]
    certificate_path = package / ARTIFACT
    topology_path = package / TOPOLOGY
    listed = ARTIFACT in artifacts
    present = certificate_path.exists() or certificate_path.is_symlink()
    if "source_text_sha256" not in manifest or manifest.get("lowering") != "direct-gate":
        if listed or present:
            raise ValueError("short-lane native artifact requires direct-gate text source")
        return False
    source_path = package / "source-relation-certificate.json"
    if not source_path.is_file():
        if listed or present:
            raise ValueError("short-lane native artifact lacks source certificate")
        return False
    source_cert = check_source_relation_certificate(
        (package / "source.s31").read_bytes(),
        (package / "source.s31.json").read_bytes(), source_path.read_bytes())
    if not admitted_ssa(source_cert, (package / "source.s31").read_bytes()):
        if listed or present:
            raise ValueError("unsupported source carries short-lane native artifact")
        return False
    if (ARTIFACT not in artifacts or TOPOLOGY not in artifacts or
            not certificate_path.is_file() or not topology_path.is_file() or
            certificate_path.is_symlink() or topology_path.is_symlink()):
        raise ValueError("admitted short-lane source lacks native row artifacts")
    expected = make_certificate(package)
    if not same_json_shape(_read(package, ARTIFACT), expected):
        raise ValueError("short-lane native row certificate differs from replay")
    return True
