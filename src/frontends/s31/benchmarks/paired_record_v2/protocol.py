"""Separate freeze for the v2 record generic/mixed paired study.

No native build or trial is authorized by the prospective design. A committed
protocol, committed anchor, externally recorded full hashes, and exact local
compiler/engine/host identities are required by the runner.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks"))

from benchmark_whole_prover_cost_v3 import host_identity
from package.context import compiler_fingerprint
from design import DESIGN_PATH, canonical, design, inventory, sha

PROTOCOL = ROOT / "design/s31/measurements/language/paired-record-v2-protocol.json"
ANCHOR = ROOT / "design/s31/measurements/language/paired-record-v2-freeze.json"
SCHEMA = "s31-paired-record-v2-protocol-v1"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", "-C", str(cwd), *args], text=True).strip()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def require_committed(path: Path, revision: str = "HEAD") -> None:
    name = relative(path)
    try:
        saved = subprocess.check_output(["git", "-C", str(ROOT), "show", f"{revision}:{name}"],
                                        stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as exc:
        raise ValueError(f"uncommitted paired study input: {name}") from exc
    if saved != path.read_bytes():
        raise ValueError(f"paired study input differs from {revision}: {name}")


def tool_paths() -> list[Path]:
    # A conservative transitive envelope: every benchmark helper and every
    # Python frontend/oracle module. Future edits invalidate the freeze.
    return sorted({*(S31 / "benchmarks").rglob("*.py"),
                   *(S31 / "python").rglob("*.py"),
                   S31 / "tests/acceptance/mixed_boundary/registry_manifest_digest.py"})


def tool_sha256() -> str:
    h = hashlib.sha256()
    for path in tool_paths():
        h.update(relative(path).encode())
        h.update(b"\0")
        h.update(bytes.fromhex(sha(path.read_bytes())))
    return h.hexdigest()


def clean_and_pinned() -> None:
    cfg = design()
    for path in [DESIGN_PATH, ROOT / cfg["source_template"], *tool_paths()]:
        require_committed(path)
    engine = ROOT / "deps/stwo-zig"
    if (git("rev-parse", "HEAD", cwd=engine) != git("rev-parse", "HEAD:deps/stwo-zig") or
            git("status", "--porcelain", "--untracked-files=no", cwd=engine)):
        raise ValueError("engine differs from clean pinned gitlink")
    if git("status", "--porcelain", "--untracked-files=no", "--", "src"):
        raise ValueError("compiler or measurement source has uncommitted tracked edits")


def draft() -> str:
    """Write the protocol for review; commit and externally timestamp it later."""
    if PROTOCOL.exists():
        raise ValueError("paired protocol already exists; never refreeze in place")
    clean_and_pinned()
    cfg = design()
    generated = inventory(cfg)
    value = {
        "schema": SCHEMA,
        "status": "frozen-before-paired-measurement-build-under-this-revision",
        "prospective_design_sha256": sha(DESIGN_PATH.read_bytes()),
        "source_template_sha256": sha((ROOT / cfg["source_template"]).read_bytes()),
        "source_base_commit": git("rev-parse", "HEAD"),
        "engine_gitlink_commit": git("rev-parse", "HEAD:deps/stwo-zig"),
        "compiler_sha256": compiler_fingerprint(),
        "measurement_tool_paths": [relative(path) for path in tool_paths()],
        "measurement_tool_sha256": tool_sha256(),
        "host": host_identity(),
        "build_mode": cfg["build_mode"],
        "source_version": 2,
        "generic_lowering": cfg["generic_lowering"],
        "mixed_lowering": cfg["mixed_lowering"],
        "samples_per_call_count": cfg["assignments_per_call_count"],
        "first_verified_proof_boundary": cfg["first_verified_proof_boundary"],
        "phase_integrity_gate": cfg["phase_integrity_gate"],
        "live_security_config_gate": cfg["live_security_config_gate"],
        "bootstrap_seed": cfg["bootstrap_seed"],
        "bootstrap_resamples": cfg["bootstrap_resamples"],
        "minimum_available_disk_bytes_before_native_phase": cfg["minimum_available_disk_bytes_before_native_phase"],
        "automatic_lowering_selection_enabled": False,
        "inventory": generated,
        "inventory_sha256": sha(canonical(generated)),
    }
    PROTOCOL.write_bytes(canonical(value))
    return sha(PROTOCOL.read_bytes())


def check(expected_protocol_sha256: str, anchor_commit: str) -> dict:
    if not HEX64.fullmatch(expected_protocol_sha256 or "") or \
            not HEX40.fullmatch(anchor_commit or ""):
        raise ValueError("full externally recorded protocol SHA and anchor commit required")
    if not PROTOCOL.is_file() or not ANCHOR.is_file():
        raise ValueError("paired protocol and anchor must exist")
    require_committed(PROTOCOL)
    require_committed(ANCHOR, anchor_commit)
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       anchor_commit, "HEAD"], check=False).returncode:
        raise ValueError("paired anchor is not an ancestor")
    if sha(PROTOCOL.read_bytes()) != expected_protocol_sha256:
        raise ValueError("paired protocol differs from externally recorded SHA")
    anchor = json.loads(ANCHOR.read_bytes())
    try:
        timestamp = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("paired anchor needs a UTC timestamp") from exc
    if (anchor.get("schema") != "s31-paired-record-v2-freeze-v1" or
            anchor.get("protocol_sha256") != expected_protocol_sha256 or
            timestamp.utcoffset() is None or timestamp.utcoffset().total_seconds() != 0 or
            timestamp > datetime.now(timezone.utc)):
        raise ValueError("paired anchor differs from external timestamp or protocol")
    value = json.loads(PROTOCOL.read_bytes())
    cfg = design()
    clean_and_pinned()
    if (value.get("schema") != SCHEMA or
            value.get("status") != "frozen-before-paired-measurement-build-under-this-revision" or
            value.get("prospective_design_sha256") != sha(DESIGN_PATH.read_bytes()) or
            value.get("source_template_sha256") != sha((ROOT / cfg["source_template"]).read_bytes()) or
            value.get("engine_gitlink_commit") != git("rev-parse", "HEAD:deps/stwo-zig") or
            value.get("compiler_sha256") != compiler_fingerprint() or
            value.get("measurement_tool_sha256") != tool_sha256() or
            value.get("measurement_tool_paths") != [relative(path) for path in tool_paths()] or
            value.get("host") != host_identity() or
            value.get("build_mode") != cfg["build_mode"] or
            value.get("source_version") != cfg["source_version"] or
            value.get("generic_lowering") != cfg["generic_lowering"] or
            value.get("mixed_lowering") != cfg["mixed_lowering"] or
            value.get("samples_per_call_count") != cfg["assignments_per_call_count"] or
            value.get("first_verified_proof_boundary") != cfg["first_verified_proof_boundary"] or
            value.get("phase_integrity_gate") != cfg["phase_integrity_gate"] or
            value.get("live_security_config_gate") != cfg["live_security_config_gate"] or
            value.get("bootstrap_seed") != cfg["bootstrap_seed"] or
            value.get("bootstrap_resamples") != cfg["bootstrap_resamples"] or
            value.get("minimum_available_disk_bytes_before_native_phase") !=
                cfg["minimum_available_disk_bytes_before_native_phase"] or
            value.get("inventory") != inventory(cfg) or
            value.get("inventory_sha256") != sha(canonical(value["inventory"])) or
            value.get("automatic_lowering_selection_enabled") is not False):
        raise ValueError("paired protocol differs from exact frozen stack or workload")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       value["source_base_commit"], anchor_commit], check=False).returncode:
        raise ValueError("paired source base does not precede anchor")
    return value


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("draft", "check"))
    parser.add_argument("--expected-protocol-sha256")
    parser.add_argument("--anchor-commit")
    args = parser.parse_args()
    if args.command == "draft":
        print(draft())
    else:
        print(check(args.expected_protocol_sha256, args.anchor_commit)["inventory_sha256"])
