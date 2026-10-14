#!/usr/bin/env python3
"""Rebuild a sealed Gate verifier before executing any packaged binary.

This establishes reproducibility relative to the checked-out sources, pinned
engine gitlink, installed Zig compiler and build recipe. It does not prove
compiler correctness, authenticate the checkout/toolchain, or establish PCS
soundness. The package is copied and checked without running its executable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import struct
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src/frontends/s31/python"))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from package.context import BUILD_FILE, ROOT, compiler_fingerprint  # noqa: E402
from package.trust import unpinned_snapshot  # noqa: E402
from scripts.release.pcs_fri_gate_final_domain import extract_gate  # noqa: E402

NAME = re.compile(r"[A-Za-z0-9_-]+\Z")
KEYS = (
    ("verification-key.json", "s31-key"),
    ("recursive-verification-key.json", "s31-recursive-key"),
    ("recursive-verification-key-level2.json", "s31-recursive-next-key"),
    ("fixed-fold-verification-key.json", "s31-fold-key"),
)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1 << 20):
            h.update(chunk)
    return h.hexdigest()


def mach_o_execution_image(path: Path, verifier: str) -> bytes:
    """Normalize only measured Mach-O linker metadata, preserving loadable bytes.

    The UUID, one Zig object timestamp/cache key, and the ad-hoc signature
    change between equivalent links. Everything else, including dyld records,
    code, constants, indirect symbols, and all load commands, must match.
    """
    raw = bytearray(path.read_bytes())
    if len(raw) < 32 or struct.unpack_from("<I", raw)[0] != 0xfeedfacf:
        raise ValueError("unsupported verifier executable format")
    ncmds, command_bytes = struct.unpack_from("<II", raw, 16)
    if ncmds > 256 or command_bytes > len(raw) - 32:
        raise ValueError("invalid Mach-O load commands")
    symtab = signature = uuid = None
    position = 32
    for _ in range(ncmds):
        if position + 8 > 32 + command_bytes:
            raise ValueError("truncated Mach-O load command")
        kind, size = struct.unpack_from("<II", raw, position)
        if size < 8 or position + size > 32 + command_bytes:
            raise ValueError("invalid Mach-O load command size")
        if kind == 0x1b:
            if size != 24 or uuid is not None:
                raise ValueError("invalid Mach-O UUID")
            uuid = (position + 8, position + 24)
        elif kind == 0x2:
            if size != 24 or symtab is not None:
                raise ValueError("invalid Mach-O symbol table")
            symtab = struct.unpack_from("<IIII", raw, position + 8)
        elif kind == 0x1d:
            if size != 16 or signature is not None:
                raise ValueError("invalid Mach-O signature")
            signature = struct.unpack_from("<II", raw, position + 8)
        position += size
    if position != 32 + command_bytes or uuid is None or symtab is None or signature is None:
        raise ValueError("incomplete Mach-O linker metadata")
    symoff, nsyms, stroff, strsize = symtab
    sigoff, sigsize = signature
    if (nsyms > 100000 or symoff < 32 + command_bytes or
            symoff + nsyms * 16 > stroff or stroff + strsize > sigoff or
            sigsize == 0 or sigoff + sigsize != len(raw)):
        raise ValueError("invalid Mach-O symbol or signature bounds")
    pattern = re.compile(rb"src/frontends/s31/\.zig-cache/o/([0-9a-f]{32})/" +
                         re.escape(verifier.encode()) + rb"_zcu\.o\Z")
    matched = 0
    for index in range(nsyms):
        offset = symoff + index * 16
        strindex, kind = struct.unpack_from("<IB", raw, offset)
        if kind != 0x66:  # N_OSO: local object-file debug record.
            continue
        if strindex >= strsize:
            raise ValueError("invalid Mach-O object symbol name")
        start = stroff + strindex
        end = raw.find(b"\x00", start, stroff + strsize)
        if end < 0:
            raise ValueError("unterminated Mach-O object symbol name")
        found = pattern.fullmatch(raw[start:end])
        if found is None:
            continue
        matched += 1
        raw[offset + 8:offset + 16] = b"\x00" * 8  # object timestamp
        raw[start + found.start(1):start + found.end(1)] = b"0" * 32
    if matched != 1:
        raise ValueError("expected exactly one Zig verifier object record")
    raw[uuid[0]:uuid[1]] = b"\x00" * 16
    raw[sigoff:sigoff + sigsize] = b"\x00" * sigsize
    return bytes(raw)


def same_executable_image(packaged: Path, rebuilt: Path, verifier: str) -> bool:
    if digest(packaged) == digest(rebuilt):
        return True
    for path in (packaged, rebuilt):
        checked = subprocess.run(["codesign", "--verify", "--strict", str(path)],
                                 capture_output=True, text=True, check=False,
                                 timeout=10)
        if checked.returncode:
            raise ValueError("Mach-O code signature does not validate")
    return mach_o_execution_image(packaged, verifier) == mach_o_execution_image(rebuilt, verifier)


def build_command(snapshot: Path, manifest: dict, output: Path, jobs: int) -> list[str]:
    """The reviewed legacy Gate ReleaseFast verifier build recipe."""
    name = manifest.get("name")
    if (not isinstance(name, str) or not NAME.fullmatch(name) or
            manifest.get("schema") != "s31-package-v1" or
            manifest.get("lowering") != "gate" or
            manifest.get("fri_fold_step") != 1 or
            manifest.get("optimize") != "ReleaseFast" or
            manifest.get("proof_mode") is not None or
            not isinstance(jobs, int) or isinstance(jobs, bool) or
            not 1 <= jobs <= max(1, min(12, int((os.cpu_count() or 1) * 0.7)))):
        raise ValueError("unreviewed sealed Gate build profile or job limit")
    source = json.loads((snapshot / "source.s31.json").read_text())
    if source.get("version") != 1 or source.get("name") != name:
        raise ValueError("unreviewed Gate relation source")
    for filename, _ in KEYS:
        if not (snapshot / filename).is_file():
            raise ValueError(f"missing sealed Gate build input: {filename}")
    result = [
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=gate",
        "-Ds31-fri-fold-step=1", f"-Ds31-source={snapshot / 'source.s31.json'}",
        f"-Ds31-name={name}",
        *(f"-D{option}={snapshot / filename}" for filename, option in KEYS),
    ]
    state_fold = snapshot / "state-fold-verification-key.json"
    if state_fold.is_file():
        result.append(f"-Ds31-state-fold-key={state_fold}")
    lock = snapshot / "stdlib-lock.json"
    if lock.is_file():
        lock_digest = digest(lock)
        if manifest.get("stdlib_lock_sha256") != lock_digest:
            raise ValueError("standard-library lock differs from sealed manifest")
        result.append(f"-Ds31-stdlib-sha256={lock_digest}")
    elif manifest.get("stdlib_lock_sha256") is not None:
        raise ValueError("sealed manifest requires a missing standard-library lock")
    result.extend(("--prefix", str(output), f"-j{jobs}"))
    return result


def accepted_gate_geometry(geometry: dict, proof_control: dict,
                           rebuilt_verifier_sha256: str) -> dict:
    """Join one successful rebuilt-verifier run to its conditional P01 domain.

    This is a proof-acceptance witness for the *native* FRI geometry, not an
    identification of the paper's original-plus-quotient oracle domain.
    """
    gate = geometry.get("gate_final_domain", {})
    checks = geometry.get("package_checks", {})
    log_size = gate.get("fri_input_domain_log")
    required_gate = ("fri_input_degree_bound_log",
                     "candidate_paper_protocol4_D0_if_N_is_trace_rows",
                     "native_fri_domain_equals_candidate_paper_protocol4_D0")
    digests = (proof_control.get("proof_sha256"), proof_control.get("statement_sha256")) \
        if isinstance(proof_control, dict) else ()
    if (gate.get("status") != "conditional_source_bound_geometry" or
            checks.get("native_check_key") != "accepted" or
            geometry.get("status") != "incomplete" or
            geometry.get("proven_release_admissible") is not False or
            any(not isinstance(value, str) or not re.fullmatch("[0-9a-f]{64}", value)
                for value in (*digests, rebuilt_verifier_sha256)) or
            len(digests) != 2 or
            any(key not in gate for key in required_gate) or
            any(key not in checks for key in ("verification_key_sha256", "package_manifest_sha256")) or
            "engine_gitlink" not in geometry.get("source_binding", {}) or
            type(log_size) is not int or not 0 <= log_size <= 30 or
            type(gate.get("fri_input_domain_rows")) is not int or
            gate["fri_input_domain_rows"] != 1 << log_size or
            gate["fri_input_domain_rows"] != geometry.get("theorem_inputs", {}).get("D_final_fri_domain")):
        raise ValueError("accepted Gate proof and conditional native geometry do not join")
    return {
        "status": "accepted_native_proof_with_conditional_source_geometry",
        "native_fri_input_domain_rows": gate["fri_input_domain_rows"],
        "native_fri_input_degree_bound_log": gate["fri_input_degree_bound_log"],
        "candidate_paper_protocol4_D0_if_N_is_trace_rows":
            gate["candidate_paper_protocol4_D0_if_N_is_trace_rows"],
        "native_fri_domain_equals_candidate_paper_protocol4_D0":
            gate["native_fri_domain_equals_candidate_paper_protocol4_D0"],
        "proof_sha256": proof_control["proof_sha256"],
        "statement_sha256": proof_control["statement_sha256"],
        "rebuilt_verifier_sha256": rebuilt_verifier_sha256,
        "verification_key_sha256": checks["verification_key_sha256"],
        "package_manifest_sha256": checks["package_manifest_sha256"],
        "engine_gitlink": geometry["source_binding"]["engine_gitlink"],
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
    }


def rebuild_verifier(package: Path, jobs: int = 8,
                     proof: Path | None = None,
                     statement: Path | None = None) -> dict:
    if (proof is None) != (statement is None):
        raise ValueError("proof and public statement must be supplied together")
    with unpinned_snapshot(package) as (snapshot, manifest):
        # No binary from the package has been executed at this point.
        compiler = compiler_fingerprint()
        zig_version = subprocess.run(["zig", "version"], capture_output=True,
                                     text=True, check=True, timeout=10).stdout.strip()
        if manifest.get("compiler_sha256") != compiler or manifest.get("zig_version") != zig_version:
            raise ValueError("sealed package differs from current compiler inputs or Zig version")
        with tempfile.TemporaryDirectory(prefix="s31-gate-verifier-rebuild-") as directory:
            rebuilt = Path(directory)
            command = build_command(snapshot, manifest, rebuilt, jobs)
            result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                    text=True, check=False, timeout=600)
            if result.returncode:
                raise ValueError(f"trusted verifier rebuild failed: {(result.stderr + result.stdout)[-1600:]}")
            verifier = f"s31-{manifest['name']}-native-verifier"
            installed = snapshot / "bin" / verifier
            independent = rebuilt / "bin" / verifier
            if not independent.is_file() or not same_executable_image(installed, independent, verifier):
                raise ValueError("rebuilt verifier differs from package executable")
            # Only the fresh verifier is executed after a loadable-image match.
            geometry = extract_gate(snapshot, ROOT)
            accepted = None
            if proof is not None:
                result = subprocess.run([str(independent), str(proof.resolve()),
                                         str(statement.resolve()),
                                         str(snapshot / "verification-key.json")],
                                        capture_output=True, text=True, timeout=90, check=False)
                if result.returncode:
                    raise ValueError(f"rebuilt verifier rejected supplied proof: {result.stderr[-600:]}")
                accepted = {"proof_sha256": digest(proof),
                            "statement_sha256": digest(statement)}
            verifier_sha256 = digest(independent)
            return {
                "schema": "s31-gate-verifier-rebuild-v1",
                "status": "conditional_binary_reproducibility_observed",
                "engine_gitlink": geometry["source_binding"]["engine_gitlink"],
                "compiler_sha256": compiler,
                "zig_version": zig_version,
                "rebuild_jobs": jobs,
                "verifier_sha256": verifier_sha256,
                "package_verifier_byte_identical": digest(installed) == digest(independent),
                "package_verifier_execution_image_identical": True,
                "package_verifier_sha256": digest(installed),
                "native_check_key": geometry["package_checks"]["native_check_key"],
                "supplied_proof": accepted,
                "accepted_proof_gate_geometry": (
                    accepted_gate_geometry(geometry, accepted, verifier_sha256)
                    if accepted is not None else None),
                "native_proven_security_bits": None,
                "proven_release_admissible": False,
                "remaining_premises": [
                    "checkout and Zig toolchain authenticity; reproducibility is not compiler correctness",
                    "whole native verifier, AIR and PCS/FRI correspondence with a published theorem",
                    "complete theorem parameters, round errors and cryptographic reductions",
                ],
            }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--proof", type=Path)
    parser.add_argument("--statement", type=Path)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = rebuild_verifier(args.package.resolve(), args.jobs,
                                  args.proof, args.statement)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"S31 Gate verifier rebuild rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
