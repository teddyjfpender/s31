"""Build source-bound S31 packages and native verifiers atomically."""

from __future__ import annotations

import json
import os
import shutil
import tempfile
from pathlib import Path

import proof_privacy
from package.context import (
    AIR_BUNDLE_SHA256, BUILD_FILE, PROJECTION_SHA256, ROOT, abi,
    compiler_fingerprint, file_hash, invoke, load_source, lower_text, sha256,
    standard_library_lock, text_interface, write_json,
)
from package.verify import verify_package


def build_json(source_path: Path, output: Path, lowering: str = "gate",
               library_lock: dict | None = None, fri_fold_step: int = 1) -> Path:
    if lowering not in {"gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"}:
        raise ValueError("invalid S31 lowering")
    if type(fri_fold_step) is not int or fri_fold_step not in (1, 4) or (fri_fold_step == 4 and lowering not in {"gate", "sparse-wide-gate"}):
        raise ValueError("FRI fold step 4 requires gate or sparse-wide-gate lowering; supported steps are 1 and 4")
    source_path = source_path.resolve()
    source, data = load_source(source_path)
    privacy = proof_privacy.policy_for(source, lowering, fri_fold_step)
    lock_bytes = ((json.dumps(library_lock, indent=2, sort_keys=True) + "\n").encode()
                  if library_lock is not None else None)
    lock_digest = sha256(lock_bytes) if lock_bytes is not None else None
    lock_option = (f"-Ds31-stdlib-sha256={lock_digest}",) if lock_digest is not None else ()
    compiler_sha256 = compiler_fingerprint()
    output = output.resolve()
    if output.exists():
        manifest = verify_package(output)
        if manifest["program_sha256"] != sha256(data):
            raise FileExistsError(f"package already exists for a different source: {output}")
        if manifest.get("compiler_sha256") != compiler_sha256:
            raise FileExistsError(f"package was built with different compiler inputs: {output}")
        if manifest.get("lowering", "gate") != lowering:
            raise FileExistsError(f"package was built with different lowering: {output}")
        if manifest.get("fri_fold_step", 1) != fri_fold_step:
            raise FileExistsError(f"package was built with a different FRI fold step: {output}")
        if manifest.get("stdlib_lock_sha256") != lock_digest:
            raise FileExistsError(f"package was built with a different standard library lock: {output}")
        return output

    output.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{output.name}.build-", dir=output.parent))
    try:
        name = source["name"]
        invoke(
            "zig", "build", "--build-file", str(BUILD_FILE), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=1",
            f"-Ds31-lowering={lowering}", f"-Ds31-fri-fold-step={fri_fold_step}",
            f"-Ds31-source={source_path}", f"-Ds31-name={name}",
            *lock_option,
            "--prefix", str(staging),
        )
        prover = staging / "bin" / f"s31-{name}-prover"
        verifier = staging / "bin" / f"s31-{name}-native-verifier"
        invoke(str(prover), "check")
        inspection = json.loads(invoke(str(prover), "inspect"))
        if inspection["program_sha256"] != sha256(data):
            raise RuntimeError("compiled program does not match source")
        key = {
            "schema": proof_privacy.KEY_SCHEMA if privacy else "s31-verification-key-v5p" if inspection["profile"] == "direct-m31-private-v5" else "s31-verification-key-sha-fused-v4" if lowering == "sha-fused" else "s31-verification-key-sha-shift-v3" if lowering == "sha-shift" else "s31-verification-key-sha-joint-v1" if lowering == "sha-joint" else "s31-verification-key-direct-manifest-v1" if lowering == "direct-gate" else "s31-verification-key-v4" if lowering.startswith("direct-") else "s31-verification-key-v5" if lowering == "sparse-wide-gate" else "s31-verification-key-v3" if lowering.startswith("sparse-") else "s31-verification-key-v2" if lowering == "chip" else "s31-verification-key-v1",
            "profile": inspection["profile"],
            "chip": inspection["chip"],
            "name": name,
            "program_sha256": inspection["program_sha256"],
            "canonical_ir_sha256": inspection["canonical_ir_sha256"],
            "preprocessed_root": inspection["preprocessed_root"],
            "circuit_hash": inspection["circuit_hash"],
            "padded": inspection["padded"],
            "trace_log_size": inspection["trace_log_size"],
            "projection_sha256": PROJECTION_SHA256,
            "air_bundle_sha256": AIR_BUNDLE_SHA256,
            "fri": inspection["fri"],
        }
        if privacy is not None:
            if not proof_privacy.matches_policy(inspection.get("proof_privacy"), privacy):
                raise RuntimeError("compiled blinding policy does not match source")
            key["proof_privacy"] = privacy
        if lock_digest is not None:
            key["stdlib_lock_sha256"] = lock_digest
        if lowering == "sha-joint":
            key["sha_joint"] = inspection["sha_joint"]
        if lowering == "sha-shift":
            key["sha_shift"] = inspection["sha_shift"]
        if lowering == "sha-fused":
            key["sha_fused"] = inspection["sha_fused"]
        if inspection["profile"] == "direct-m31-private-v5":
            key["private_boundary"] = inspection["private_boundary"]
        if lowering == "direct-gate":
            component_manifest = inspection.get("component_manifest")
            if not isinstance(component_manifest, dict) or component_manifest.get("schema") != "s31-component-manifest-direct-gate-v1":
                raise RuntimeError("direct-gate compiler did not produce a component manifest")
            key["component_manifest"] = component_manifest
            write_json(staging / "component-manifest.json", component_manifest)
        (staging / "source.s31.json").write_bytes(data)
        write_json(staging / "verification-key.json", key)
        if lock_bytes is not None:
            (staging / "stdlib-lock.json").write_bytes(lock_bytes)
        recursive_option: tuple[str, ...] = ()
        recursive_next_option: tuple[str, ...] = ()
        fold_option: tuple[str, ...] = ()
        state_fold_option: tuple[str, ...] = ()
        if privacy is None and lowering in {"gate", "sparse-wide-gate"}:
            recursive_key = staging / "recursive-verification-key.json"
            invoke(str(prover), "recurse-keygen", str(staging / "verification-key.json"),
                   str(recursive_key))
            recursive_option = (f"-Ds31-recursive-key={recursive_key}",)
            recursive_next_key = staging / "recursive-verification-key-level2.json"
            invoke(str(prover), "recurse-keygen-next", str(staging / "verification-key.json"),
                   str(recursive_key), str(recursive_next_key))
            recursive_next_option = (f"-Ds31-recursive-next-key={recursive_next_key}",)
            if lowering == "sparse-wide-gate":
                fold_key = staging / "fixed-fold-verification-key.json"
                invoke(str(prover), "wide-fold-keygen", str(staging / "verification-key.json"),
                       str(recursive_key), str(recursive_next_key), str(fold_key))
                fold_option = (f"-Ds31-fold-key={fold_key}",)
        if privacy is None and lowering == "gate":
            fold_key = staging / "fixed-fold-verification-key.json"
            invoke(str(prover), "fold-keygen", str(staging / "verification-key.json"),
                   str(recursive_key), str(fold_key))
            fold_option = (f"-Ds31-fold-key={fold_key}",)
            if inspection.get("state_fold_step") is not None:
                state_fold_key = staging / "state-fold-verification-key.json"
                invoke(str(prover), "state-fold-keygen", str(staging / "verification-key.json"),
                       str(recursive_key), str(state_fold_key))
                state_fold_option = (f"-Ds31-state-fold-key={state_fold_key}",)
        invoke(
            "zig", "build", "--build-file", str(BUILD_FILE), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=1",
            f"-Ds31-lowering={lowering}", f"-Ds31-fri-fold-step={fri_fold_step}",
            f"-Ds31-source={source_path}", f"-Ds31-name={name}",
            f"-Ds31-key={staging / 'verification-key.json'}",
            *recursive_option,
            *recursive_next_option,
            *fold_option,
            *state_fold_option,
            *lock_option,
            "--prefix", str(staging),
        )
        write_json(staging / "public-abi.json", abi(source, lowering))
        write_json(staging / "cost-report.json", inspection)
        artifacts = [
            "source.s31.json", "verification-key.json", "public-abi.json",
            "cost-report.json", f"bin/{prover.name}", f"bin/{verifier.name}",
        ]
        if lowering == "direct-gate":
            artifacts.append("component-manifest.json")
        if lock_bytes is not None:
            artifacts.append("stdlib-lock.json")
        if recursive_option:
            artifacts.append("recursive-verification-key.json")
        if recursive_next_option:
            artifacts.append("recursive-verification-key-level2.json")
        if fold_option:
            artifacts.append("fixed-fold-verification-key.json")
            if state_fold_option:
                artifacts.append("state-fold-verification-key.json")
        manifest = {
            "schema": "s31-package-v1",
            "name": name,
            "lowering": lowering,
            "fri_fold_step": fri_fold_step,
            "program_sha256": sha256(data),
            "compiler_sha256": compiler_sha256,
            "canonical_ir_sha256": inspection["canonical_ir_sha256"],
            "zig_version": invoke("zig", "version").strip(),
            "optimize": "ReleaseFast",
            "artifacts": {item: file_hash(staging / item) for item in artifacts},
        }
        if recursive_option:
            manifest["recursive_fri_fold_step"] = 4 if lowering == "sparse-wide-gate" else fri_fold_step
        if privacy is not None:
            manifest["proof_mode"] = "blinded"
            manifest["proof_privacy"] = privacy
        if fold_option:
            manifest["capabilities"] = ["s31-fixed-fold-batch-v1"]
        if state_fold_option:
            manifest.setdefault("capabilities", []).append("s31-state-fold-batch-v2")
        if lock_digest is not None:
            manifest["stdlib_lock_sha256"] = lock_digest
        if source_path.read_bytes() != data or compiler_fingerprint() != compiler_sha256:
            raise RuntimeError("S31 source or compiler inputs changed during package build")
        write_json(staging / "manifest.json", manifest)
        os.rename(staging, output)
        return output
    except Exception:
        shutil.rmtree(staging)
        raise


def build_text(source_path: Path, output: Path, lowering: str = "gate", fri_fold_step: int = 1) -> Path:
    from text_frontend import Parser

    source_path = source_path.resolve()
    output = output.resolve()
    text_data = source_path.read_bytes()
    _, normalized, source_map = lower_text(source_path)
    parser = Parser(text_data.decode(), str(source_path))
    _, circuit = parser.parse()
    library_lock = standard_library_lock(parser.stdlib_explicit)
    typed_interface = text_interface(circuit, parser.stdlib_explicit)
    if output.exists():
        manifest = verify_package(output)
        if manifest.get("source_text_sha256") != sha256(text_data) or manifest["program_sha256"] != sha256(normalized):
            raise FileExistsError(f"package already exists for a different source: {output}")
        if manifest["compiler_sha256"] != compiler_fingerprint() or manifest["lowering"] != lowering:
            raise FileExistsError(f"package was built with different compiler inputs or lowering: {output}")
        if manifest.get("fri_fold_step", 1) != fri_fold_step:
            raise FileExistsError(f"package was built with a different FRI fold step: {output}")
        return output
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=f".{output.name}.text-", dir=output.parent) as directory:
        staging_root = Path(directory)
        normalized_path = staging_root / "normalized.s31.json"
        normalized_path.write_bytes(normalized)
        package = build_json(normalized_path, staging_root / "package", lowering, library_lock, fri_fold_step)
        (package / "source.s31").write_bytes(text_data)
        write_json(package / "source-map.json", {
            "schema": "s31-text-source-map-v1", "source_sha256": sha256(text_data),
            "nodes": source_map,
        })
        write_json(package / "typed-interface.json", typed_interface)
        manifest_path = package / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["source_text_sha256"] = sha256(text_data)
        manifest["text_frontend_version"] = 1
        for name in ("source.s31", "source-map.json", "typed-interface.json"):
            manifest["artifacts"][name] = file_hash(package / name)
        if source_path.read_bytes() != text_data or manifest["compiler_sha256"] != compiler_fingerprint():
            raise RuntimeError("S31 text source or compiler inputs changed during package build")
        write_json(manifest_path, manifest)
        os.rename(package, output)
    return output


def build(source_path: Path, output: Path, lowering: str = "gate", fri_fold_step: int = 1) -> Path:
    if source_path.suffix == ".s31":
        return build_text(source_path, output, lowering, fri_fold_step)
    return build_json(source_path, output, lowering, fri_fold_step=fri_fold_step)


def package_for(source_or_package: Path) -> Path:
    if source_or_package.is_dir():
        verify_package(source_or_package)
        return source_or_package.resolve()
    if source_or_package.suffix == ".s31":
        data = source_or_package.read_bytes()
    else:
        _, data = load_source(source_or_package)
    digest = sha256(data)
    return build(source_or_package, ROOT / "zig-out/s31/mvp-cache" / f"{digest}-{compiler_fingerprint()}")
