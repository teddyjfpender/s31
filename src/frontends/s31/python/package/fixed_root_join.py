"""Join a checked direct-Gate package's fixed cells to an accepted proof.

This is a package-level, honest-proof diagnostic for the public four-lane
1..16-gate correspondence fragment. It does not prove arbitrary PCS opening
authentication, Merkle binding, FRI, or compiler correctness outside that
fragment.
"""

from __future__ import annotations

import hashlib
import json
import re
import struct
import subprocess
import tempfile
from pathlib import Path

from package.correspondence import read_canonical_json
from package.release_admission import bounded_direct_gate_snapshot


MAGIC = b"S31NAT7G"
CONFIG = (26, 1, 70, 0, 1)
ROOT = re.compile(r"[0-9a-f]{64}\Z")
P = (1 << 31) - 1
MAX_PROOF_BYTES = 64 * 1024 * 1024
MAX_STATEMENT_BYTES = 1024 * 1024


def proof_roots(raw: bytes) -> tuple[bytes, bytes, int]:
    """Decode the bounded direct-Gate postcard's first two commitment roots.

    Call this only *after* the generated native verifier accepts these exact
    bytes. The bounded parser identifies the serialized roots; it is not a
    second proof verifier.
    """
    if raw[:8] != MAGIC or len(raw) < 128:
        raise ValueError("wrong bounded direct-Gate proof profile")
    offset = 8 + 8 + 16  # envelope magic, interaction nonce, one QM31 sum

    def varint() -> int:
        nonlocal offset
        value = 0
        start = offset
        for shift in range(0, 70, 7):
            if offset >= len(raw):
                raise ValueError("truncated proof varint")
            byte = raw[offset]
            offset += 1
            value |= (byte & 127) << shift
            if byte < 128:
                if value >= 1 << 64 or (offset - start > 1 and byte == 0):
                    raise ValueError("noncanonical proof varint")
                return value
        raise ValueError("oversized proof varint")

    if tuple(varint() for _ in range(5)) != CONFIG or offset >= len(raw) or raw[offset] != 0:
        raise ValueError("direct-Gate proof PCS config changed")
    offset += 1  # optional lifting log size: None
    if varint() != 4 or offset + 64 > len(raw):
        raise ValueError("wrong direct-Gate commitment count")
    return raw[offset:offset + 32], raw[offset + 32:offset + 64], offset + 32


def _invoke(binary: Path, *arguments: Path | str) -> str:
    result = subprocess.run((str(binary), *(str(argument) for argument in arguments)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode:
        raise ValueError(f"{binary.name} rejected input: {result.stderr.strip()}")
    return result.stdout + result.stderr


def _fixed_words(topology: dict) -> tuple[list[list[int]], bytes]:
    exported = topology.get("columns")
    if (type(exported) is not list or len(exported) != 8 or
            any(type(item) is not dict for item in exported)):
        raise ValueError("checked direct-Gate fixed column roster is missing")
    columns = [item.get("values") for item in exported]
    if (any(type(column) is not list or len(column) != 512 for column in columns) or
            any(type(word) is not int or not 0 <= word < P
                for column in columns for word in column)):
        raise ValueError("checked direct-Gate fixed column word is noncanonical")
    return columns, b"".join(struct.pack("<I", word)
                             for column in columns for word in column)


def _bounded_bytes(path: Path, limit: int, name: str) -> bytes:
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise ValueError(f"{name} exceeds the diagnostic byte limit")
    return data


def check(package: Path, proof: Path, statement: Path, pins: dict[str, str]) -> dict:
    """Check exact package source/key/proof identity and recommit all fixed cells.

    The required pins come from outside the package. The same strict snapshot
    admission as `verify-release` checks the source certificate, sealed key,
    and five external digests before executing copied package binaries. Exact
    proof and statement bytes are also copied before verification. Caller
    authentication of the pins remains an assumption.
    """
    proof_bytes = _bounded_bytes(proof, MAX_PROOF_BYTES, "proof")
    statement_bytes = _bounded_bytes(statement, MAX_STATEMENT_BYTES, "statement")
    with bounded_direct_gate_snapshot(package, pins) as (snapshot, manifest, certificate):
        with tempfile.TemporaryDirectory(prefix="s31-fixed-root-join-input-") as directory:
            proof_copy = Path(directory) / "proof.bin"
            statement_copy = Path(directory) / "statement.json"
            proof_copy.write_bytes(proof_bytes)
            statement_copy.write_bytes(statement_bytes)
            result = _check_snapshot(snapshot, manifest, certificate,
                                     proof_copy, statement_copy,
                                     proof_bytes, statement_bytes)
    result["pinned_artifacts_sha256"] = dict(sorted(pins.items()))
    return result


def _check_snapshot(package: Path, manifest: dict, certificate: dict,
                    proof: Path, statement: Path,
                    proof_bytes: bytes, statement_bytes: bytes) -> dict:
    if (manifest.get("lowering") != "direct-gate" or
            certificate.get("status", {}).get("source_to_normalized") !=
            "source-to-normalized-checked"):
        raise ValueError("package is outside checked direct-Gate source fragment")
    topology = read_canonical_json(package / "gate-topology.json")
    key = read_canonical_json(package / "verification-key.json")
    if topology.get("schema") != "s31-direct-gate-topology-v2":
        raise ValueError("checked direct-Gate package lacks a rooted topology")
    name = manifest["name"]
    prover = package / "bin" / f"s31-{name}-prover"
    verifier = package / "bin" / f"s31-{name}-native-verifier"
    fresh = json.loads(_invoke(prover, "inspect-topology"))
    if fresh != topology:
        raise ValueError("fresh source-bound topology differs from sealed package")
    columns, words = _fixed_words(topology)
    with tempfile.TemporaryDirectory(prefix="s31-fixed-root-join-") as directory:
        fixed_input = Path(directory) / "fixed-columns.json"
        fixed_input.write_text(json.dumps({
            "schema": "s31-direct-gate-fixed-columns-v1",
            "fixed_columns": columns,
        }, separators=(",", ":")))
        recommitted = json.loads(_invoke(prover, "inspect-fixed-root-from-columns", fixed_input))
    if (type(recommitted) is not dict or set(recommitted) != {"schema", "fixed_root"} or
            recommitted["schema"] != "s31-direct-gate-recommitted-fixed-root-v1" or
            type(recommitted["fixed_root"]) is not str or
            ROOT.fullmatch(recommitted["fixed_root"]) is None):
        raise ValueError("invalid native fixed-column recommitment report")
    fixed_root = recommitted["fixed_root"]
    if (fixed_root != key.get("preprocessed_root") or
            fixed_root != topology.get("preprocessed_root")):
        raise ValueError("recommitted fixed cells differ from sealed verification key")

    # Verify the exact caller-supplied proof and statement before interpreting
    # the proof header. The generated verifier consumes its package's key.
    _invoke(verifier, proof, statement, package / "verification-key.json")
    if proof.read_bytes() != proof_bytes or statement.read_bytes() != statement_bytes:
        raise ValueError("private proof or statement snapshot changed during verification")
    proof_fixed, proof_main, _ = proof_roots(proof_bytes)
    if proof_fixed.hex() != fixed_root:
        raise ValueError("accepted proof fixed root differs from recommitted source roster")
    return {
        "schema": "s31-direct-gate-package-fixed-root-join-v1",
        "scope": "checked public four-lane 1..16-gate fragment; one accepted proof",
        "source_text_sha256": manifest["source_text_sha256"],
        "program_sha256": manifest["program_sha256"],
        "canonical_ir_sha256": key["canonical_ir_sha256"],
        "fixed_columns_sha256": hashlib.sha256(words).hexdigest(),
        "fixed_cells": 4096,
        "sealed_key_root": fixed_root,
        "recommitted_fixed_root": fixed_root,
        "accepted_proof_fixed_root": proof_fixed.hex(),
        "accepted_proof_main_root": proof_main.hex(),
        "proof_sha256": hashlib.sha256(proof_bytes).hexdigest(),
        "proof_bytes": len(proof_bytes),
        "statement_sha256": hashlib.sha256(statement_bytes).hexdigest(),
        "native_verifier_accepted": True,
    }
