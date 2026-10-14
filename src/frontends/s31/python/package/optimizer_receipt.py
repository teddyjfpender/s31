"""Bind the opt-in native pure-field optimizer audit to a sealed package."""

from __future__ import annotations

import json
from pathlib import Path

SCHEMA = "s31-optimizer-correspondence-pure-field-v2"
LEGACY_SCHEMA = "s31-optimizer-correspondence-pure-field-v1"
ARTIFACT = "optimizer-correspondence.json"
LEGACY_OPS = {"constant", "cast_m31", "add", "sub", "mul", "add_const", "mul_const"}
OPS = LEGACY_OPS | {"inv", "is_zero", "select"}
FIELDS = {"schema", "program_sha256", "canonical_ir_sha256",
          "source_nodes", "canonical_nodes", "aliases"}


def eligible(source: dict) -> bool:
    """The exact native v1 fragment; unsupported relations get no receipt."""
    return (source.get("version") == 1 and
            source.get("proof_mode", "transparent") == "transparent" and
            isinstance(source.get("inputs"), list) and
            isinstance(source.get("nodes"), list) and
            all(isinstance(item, dict) and item.get("kind") == "m31"
                for item in source["inputs"]) and
            all(isinstance(item, dict) and item.get("op") in OPS
                for item in source["nodes"]))


def validate(receipt: dict, source: dict, program_sha256: str,
             canonical_ir_sha256: str) -> None:
    if not eligible(source):
        raise ValueError("optimizer receipt is outside the pure-field v1 fragment")
    input_count = len(source["inputs"])
    source_count = len(source["nodes"])
    receipt_schema = receipt.get("schema") if isinstance(receipt, dict) else None
    if (not isinstance(receipt, dict) or set(receipt) != FIELDS or
            receipt_schema not in {SCHEMA, LEGACY_SCHEMA} or
            (receipt_schema == LEGACY_SCHEMA and
             any(node["op"] not in LEGACY_OPS for node in source["nodes"])) or
            receipt.get("program_sha256") != program_sha256 or
            receipt.get("canonical_ir_sha256") != canonical_ir_sha256 or
            type(receipt.get("source_nodes")) is not int or
            receipt["source_nodes"] != source_count or
            type(receipt.get("canonical_nodes")) is not int or
            type(receipt.get("aliases")) is not int or
            receipt["aliases"] < 0 or receipt["aliases"] > source_count or
            receipt["canonical_nodes"] != input_count + source_count - receipt["aliases"]):
        raise ValueError("optimizer receipt differs from sealed source or IR identity")


def verify_artifact(package: Path, manifest: dict, key: dict, source: dict) -> bool:
    artifacts = manifest["artifacts"]
    path = package / ARTIFACT
    listed = ARTIFACT in artifacts
    present = path.exists() or path.is_symlink()
    declared = manifest.get("optimizer_correspondence_schema")
    if declared is None and not listed and not present:
        return False  # Legacy package without this opt-in audit.
    if (declared not in {SCHEMA, LEGACY_SCHEMA} or not listed or not present or
            manifest.get("lowering") in {"sha-joint", "sha-shift", "sha-fused"}):
        raise ValueError("optimizer receipt is missing or undeclared")
    receipt = json.loads(path.read_text())
    if not isinstance(receipt, dict) or receipt.get("schema") != declared:
        raise ValueError("optimizer receipt schema differs from package declaration")
    validate(receipt, source, manifest["program_sha256"],
             key["canonical_ir_sha256"])
    if receipt["canonical_ir_sha256"] != manifest["canonical_ir_sha256"]:
        raise ValueError("optimizer receipt IR digest differs from package manifest")
    return True
