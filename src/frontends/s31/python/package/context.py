"""Shared paths, identity and source metadata for sealed S31 packages."""

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

S31_DIR = Path(__file__).resolve().parents[2]
ROOT = S31_DIR.parents[2]
ENGINE_ROOT = ROOT / "deps/stwo-zig"
BUILD_FILE = S31_DIR / "build.zig"
PROJECTION_SHA256 = "ceea3c293a4fcd3ca8a20ba62f4845732f8725bdf610fe6367c83adcb8be7e09"
AIR_BUNDLE_SHA256 = "7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2"
PINNED_ASSETS = (
    ENGINE_ROOT / "vectors/circuit/official/compiled_air_constraints_v1.bin",
    ENGINE_ROOT / "vectors/circuit/official/circuit_air.air_programs_v1.bin",
)
LIBRARY_SOURCE_FILES = (
    "s31_stdlib.py", "s31_mathlib.py",
    "library/__init__.py", "library/stdlib.py", "library/math.py",
)
TEXT_FRONTEND_SOURCES = (
    S31_DIR / "python/text_frontend.py",
    *sorted((S31_DIR / "python/language").glob("*.py")),
    *sorted((S31_DIR / "python/library").glob("*.py")),
    *sorted((S31_DIR / "python/inspection").glob("*.py")),
    *sorted((S31_DIR / "python/package").glob("*.py")),
    *(S31_DIR / "python" / name for name in ("s31_stdlib.py", "s31_mathlib.py")),
    S31_DIR / "python/proof_privacy.py",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_hash(path: Path) -> str:
    return sha256(path.read_bytes())


def compiler_fingerprint() -> str:
    """Invalidate local packages when compiler, verifier, AIR, or Zig changes."""
    digest = hashlib.sha256()
    excluded = {".zig-cache", "zig-out", "target"}
    sources = sorted(
        path for path in (ROOT / "src").rglob("*")
        if path.is_file() and path.suffix in {".zig", ".zon"}
        and not excluded.intersection(path.parts)
    )
    for path in [*sources, S31_DIR / "python/s31.py", *TEXT_FRONTEND_SOURCES, *PINNED_ASSETS]:
        digest.update(str(path.relative_to(ROOT)).encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(file_hash(path)))
    engine_commit = subprocess.check_output(
        ["git", "-C", str(ENGINE_ROOT), "rev-parse", "HEAD"], text=True,
    ).strip()
    if subprocess.check_output(
        ["git", "-C", str(ENGINE_ROOT), "status", "--porcelain", "--untracked-files=no"],
        text=True,
    ).strip():
        raise RuntimeError("pinned stwo-zig dependency has local modifications")
    digest.update(b"stwo-zig-commit\0")
    digest.update(engine_commit.encode())
    digest.update(invoke("zig", "version").strip().encode())
    return digest.hexdigest()


def invoke(*args: str) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{' '.join(args)} failed ({result.returncode})\n{result.stdout}{result.stderr}")
    return result.stdout + result.stderr


def load_source(path: Path) -> tuple[dict, bytes]:
    data = path.read_bytes()
    source = json.loads(data)
    if source.get("version") != 1 or not isinstance(source.get("name"), str):
        raise ValueError("S31 v0.1 requires a version 1 relation source")
    return source, data


def abi(source: dict, lowering: str) -> dict:
    shapes = {item["name"]: {"kind": item["kind"], "length": item["length"]} for item in source["inputs"]}
    for node in source["nodes"]:
        op = node["op"]
        if op in {"constant", "array_slice"}:
            length = node["length"]
        elif op in {"sum_lanes", "u256_le", "u32_lt", "int_le", "array_get"}:
            length = 1
        elif op == "array_concat":
            length = shapes[node["lhs"]]["length"] + shapes[node["rhs"]]["length"]
        elif op in {"hash_sha256d_header", "bitcoin_target_mainnet", "bitcoin_block_work", "bitcoin_prev_hash", "bitcoin_genesis_hash_mainnet"}:
            length = 16
        elif op in {"bitcoin_header_bits", "bitcoin_header_time"}:
            length = 2
        elif op in {"hash_blake2s", "hash_blake2s_leaf", "hash_blake2s_pair",
                    "hash_poseidon2_leaf", "hash_poseidon2_pair"}:
            length = 8
        else:
            length = shapes[node["lhs"]]["length"]
        shapes[node["name"]] = {"kind": (shapes[node["lhs"]]["kind"] if op in {"array_get", "array_concat", "array_slice", "select"} else
                                         "u16" if op in {"int_view", "int_add_checked", "int_add_wrapping", "int_sub_checked", "int_sub_wrapping", "u256_add", "u256_add_checked", "u256_sub", "u256_sub_checked", "hash_sha256d_header", "bitcoin_target_mainnet", "bitcoin_block_work", "bitcoin_prev_hash", "bitcoin_header_bits", "bitcoin_header_time", "bitcoin_genesis_hash_mainnet"} else "m31"), "length": length}
    return {
        "schema": "s31-public-abi-v1",
        "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero" if lowering.startswith("direct-") or lowering in {"sha-shift", "sha-fused"} else "eight little-endian u32 words; unused words are zero",
        "public_inputs": [
            {"name": item["name"], "kind": item["kind"], "length": item["length"]}
            for item in source["inputs"] if item["visibility"] == "public"
        ],
        "public_outputs": [{"name": name, **shapes[name]} for name in source["public_outputs"]],
    }


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def standard_library_lock(explicit_import: bool) -> dict:
    from s31_stdlib import STDLIB_ABI_VERSION

    return {
        "schema": "s31-stdlib-lock-v1",
        "package": "std",
        "version": STDLIB_ABI_VERSION,
        "explicit_import": explicit_import,
        "sources": {
            name: file_hash(S31_DIR / "python" / name)
            for name in LIBRARY_SOURCE_FILES
        },
    }


def lower_text(source_path: Path) -> tuple[dict, bytes, dict]:
    from text_frontend import compile_file

    relation, source_map = compile_file(source_path)
    encoded = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    return relation, encoded, source_map


def text_interface(circuit: object, explicit_import: bool) -> dict:
    def type_entry(typ: object) -> dict:
        kind = typ.kind[4:] if typ.kind.startswith("int_") else typ.kind
        return {"kind": kind, "length": typ.length,
                **({"family": typ.family} if typ.family else {})}

    return {
        "schema": "s31-text-interface-v1",
        "inputs": [{"name": name, "visibility": visibility, "type": type_entry(typ)}
                   for name, typ, visibility in circuit.params],
        "output": type_entry(circuit.result),
        **({"proof_mode": "blinded"} if circuit.proof_mode == "blinded" else {}),
        "stdlib": {"package": "std", "version": standard_library_lock(explicit_import)["version"],
                   "explicit_import": explicit_import},
    }
