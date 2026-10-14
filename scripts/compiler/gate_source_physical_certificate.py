"""Strict structural check of the noninstalled Gate source-row certificate.

The native audit derives the certificate from parsed source, canonical IR,
builder gates and installed preprocessed cells. This checker independently
validates identities, source order, alias consistency, physical partitions and
the packaged source map. It does not authenticate arbitrary PCS openings.
"""

from __future__ import annotations

from typing import Any

CLASSES = ("add", "sub", "mul", "pointwise_mul")


def _integer(value: Any) -> bool:
    return type(value) is int and value >= 0


def validate(certificate: Any, source: dict, manifest: dict, key: dict,
             report: dict, receipt: dict) -> None:
    if (type(certificate) is not dict or set(certificate) != {
            "schema", "program_sha256", "canonical_ir_sha256",
            "preprocessed_root", "n_vars", "canonical_node_count", "qm31_binary_rows",
            "source_qm31_rows", "primitive_nodes_checked", "add_const_compositions",
            "source_map"} or
            certificate["schema"] != "s31-gate-source-physical-v2" or
            certificate["program_sha256"] != manifest["program_sha256"] or
            certificate["canonical_ir_sha256"] != key["canonical_ir_sha256"] or
            certificate["preprocessed_root"] != key["preprocessed_root"]):
        raise ValueError("Gate physical certificate: identity differs from sealed key")
    nodes = certificate["source_map"]
    names = [item["name"] for item in source["inputs"] + source["nodes"]]
    reported = report.get("source_map")
    count = certificate["canonical_node_count"]
    binary_rows = certificate["qm31_binary_rows"]
    n_vars = certificate["n_vars"]
    if (not all(_integer(item) for item in (n_vars, count, binary_rows,
                                           certificate["source_qm31_rows"],
                                           certificate["primitive_nodes_checked"])) or
            count > len(names) or not isinstance(nodes, list) or
            len(nodes) != len(names) or not isinstance(reported, list) or
            len(reported) != len(names) or
            receipt.get("source_nodes_mapped") != len(names) or
            receipt.get("source_qm31_rows") != certificate["source_qm31_rows"] or
            binary_rows > report["padded"]["qm31_ops"]):
        raise ValueError("Gate physical certificate: invalid source or row count")
    by_id: dict[int, dict] = {}
    for index, (name, node, span) in enumerate(zip(names, nodes, reported,
                                                    strict=True)):
        if (type(node) is not dict or set(node) != {
                "name", "canonical_id", "canonical_tag", "packed_outputs", *CLASSES} or
                node["name"] != name or not _integer(node["canonical_id"]) or
                node["canonical_id"] >= count or
                type(node["canonical_tag"]) is not str or not node["canonical_tag"] or
                type(node["packed_outputs"]) is not list or
                not all(_integer(address) and address < n_vars
                        for address in node["packed_outputs"]) or
                type(span) is not dict or
                span.get("name") != name or
                span.get("canonical_id") != node["canonical_id"] or
                not _integer(span.get("qm31_start")) or
                not _integer(span.get("qm31_end")) or
                span["qm31_start"] > span["qm31_end"]):
            raise ValueError(f"Gate physical certificate: source map differs at {index}")
        owner = node["canonical_id"]
        if owner in by_id:
            # Names may differ for CSE aliases; physical intervals must agree.
            if (any(by_id[owner][kind] != node[kind] for kind in CLASSES) or
                    by_id[owner]["packed_outputs"] != node["packed_outputs"] or
                    by_id[owner]["canonical_tag"] != node["canonical_tag"]):
                raise ValueError("Gate physical certificate: aliased source spans differ")
        else:
            by_id[owner] = node
        owned_rows = 0
        for kind in CLASSES:
            interval = node[kind]
            if (type(interval) is not dict or set(interval) != {"start", "end"} or
                    not _integer(interval["start"]) or not _integer(interval["end"]) or
                    interval["start"] > interval["end"] or
                    interval["end"] > binary_rows):
                raise ValueError("Gate physical certificate: invalid physical interval")
            owned_rows += interval["end"] - interval["start"]
        if owned_rows != span["qm31_end"] - span["qm31_start"]:
            raise ValueError("Gate physical certificate: source span count differs from package")
    if set(by_id) != set(range(count)):
        raise ValueError("Gate physical certificate: canonical node omitted")
    if certificate["primitive_nodes_checked"] != sum(
            by_id[index]["canonical_tag"] in {"add", "sub", "mul"}
            for index in range(count)):
        raise ValueError("Gate physical certificate: primitive node count differs")
    compositions = certificate["add_const_compositions"]
    if type(compositions) is not list:
        raise ValueError("Gate physical certificate: add_const composition list missing")
    source_ids = {node["name"]: node["canonical_id"] for node in nodes}
    composed: set[int] = set()
    for composition in compositions:
        if type(composition) is not dict or set(composition) != {
                "canonical_id", "lhs_canonical_id", "constant", "constant_address",
                "lhs_packed_outputs", "output_packed_outputs", "add"}:
            raise ValueError("Gate physical certificate: malformed add_const composition")
        owner = composition["canonical_id"]
        lhs = composition["lhs_canonical_id"]
        constant = composition["constant"]
        if (not _integer(owner) or owner >= count or owner in composed or
                not _integer(lhs) or lhs >= owner or
                not _integer(constant) or constant == 0 or constant >= 2147483647 or
                not _integer(composition["constant_address"]) or
                composition["constant_address"] >= n_vars or
                by_id[owner]["canonical_tag"] != "add_const" or
                composition["lhs_packed_outputs"] != by_id[lhs]["packed_outputs"] or
                composition["output_packed_outputs"] != by_id[owner]["packed_outputs"] or
                composition["add"] != by_id[owner]["add"] or
                composition["add"]["end"] - composition["add"]["start"] !=
                len(composition["output_packed_outputs"])):
            raise ValueError("Gate physical certificate: add_const physical ports differ")
        if not any(source_ids[raw["name"]] == owner and raw["op"] == "add_const" and
                   raw["constant"] == constant and source_ids[raw["lhs"]] == lhs
                   for raw in source["nodes"]):
            raise ValueError("Gate physical certificate: add_const differs from source")
        composed.add(owner)
    if composed != {index for index in range(count)
                    if by_id[index]["canonical_tag"] == "add_const"}:
        raise ValueError("Gate physical certificate: add_const canonical node omitted")
    total = 0
    previous_class_end = 0
    for kind in CLASSES:
        class_spans = [by_id[index][kind] for index in range(count)]
        if class_spans:
            if class_spans[0]["start"] < previous_class_end:
                raise ValueError("Gate physical certificate: operation classes overlap")
            for left, right in zip(class_spans, class_spans[1:]):
                if left["end"] != right["start"]:
                    raise ValueError("Gate physical certificate: physical source row gap")
            previous_class_end = class_spans[-1]["end"]
            total += previous_class_end - class_spans[0]["start"]
    if total != certificate["source_qm31_rows"]:
        raise ValueError("Gate physical certificate: total source row count differs")
