"""Prospective freeze and exact-stack admission for mixed stage cost v1.

The design file authorizes no native measurement. A reviewer must commit the
draft protocol and a UTC freeze anchor, then independently record their full
hashes before the first timed build. The caller supplies those hashes here.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from cohort import DESIGN_PATH, ROOT, S31, canonical, design, inventory, sha

sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks"))
from benchmark_whole_prover_cost_v3 import host_identity  # noqa: E402
from package.context import compiler_fingerprint  # noqa: E402

PROTOCOL = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-protocol.json"
ANCHOR = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-freeze.json"
SCHEMA = "s31-mixed-stage-cost-v1-protocol"
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", "-C", str(cwd), *args], text=True).strip()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def committed(path: Path, revision: str = "HEAD") -> None:
    name = relative(path)
    try:
        saved = subprocess.check_output(["git", "-C", str(ROOT), "show", f"{revision}:{name}"],
                                        stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as exc:
        raise ValueError(f"uncommitted mixed cost source: {name}") from exc
    if saved != path.read_bytes():
        raise ValueError(f"mixed cost source differs from {revision}: {name}")


def tool_paths() -> list[Path]:
    # The cohort and auditor import Python ABI, oracle, package, and benchmark
    # helpers transitively. Pin the full source envelope so a changed oracle
    # cannot silently alter a frozen native study.
    return sorted({*(S31 / "benchmarks").rglob("*.py"),
                   *(S31 / "python").rglob("*.py"),
                   S31 / "tests/acceptance/mixed_boundary/registry_manifest_digest.py"})


def tool_sha256() -> str:
    digest = hashlib.sha256()
    for path in tool_paths():
        digest.update(relative(path).encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(sha(path.read_bytes())))
    return digest.hexdigest()


def clean_stack() -> None:
    cfg = design()
    for path in [DESIGN_PATH, ROOT / cfg["source_template"], *tool_paths()]:
        committed(path)
    engine = ROOT / "deps/stwo-zig"
    if (git("rev-parse", "HEAD", cwd=engine) != git("rev-parse", "HEAD:deps/stwo-zig") or
            git("status", "--porcelain", "--untracked-files=no", cwd=engine)):
        raise ValueError("mixed cost engine differs from pinned clean gitlink")
    if git("status", "--porcelain", "--untracked-files=no", "--", "src"):
        raise ValueError("mixed cost compiler or collector has uncommitted tracked edits")


def draft() -> str:
    """Create a candidate protocol; never measure until it is anchored."""
    if PROTOCOL.exists():
        raise ValueError("mixed cost protocol already exists; do not refreeze in place")
    clean_stack()
    cfg = design()
    roster = inventory(cfg)
    value = {
        "schema": SCHEMA,
        "status": "frozen-before-first-mixed-stage-build-under-this-revision",
        "design_sha256": sha(DESIGN_PATH.read_bytes()),
        "source_template_sha256": sha((ROOT / cfg["source_template"]).read_bytes()),
        "source_base_commit": git("rev-parse", "HEAD"),
        "engine_gitlink_commit": git("rev-parse", "HEAD:deps/stwo-zig"),
        "compiler_sha256": compiler_fingerprint(),
        "tool_paths": [relative(path) for path in tool_paths()],
        "tool_sha256": tool_sha256(),
        "host": host_identity(),
        "build_mode": cfg["build_mode"],
        "lowering": cfg["lowering"],
        "samples_per_call_count": cfg["assignments_per_call_count"],
        "first_verified_boundary": cfg["first_verified_boundary"],
        "model_features": cfg["model_features"],
        "model_fit": cfg["model_fit"],
        "accuracy_gate": cfg["accuracy_gate"],
        "minimum_available_disk_bytes_before_native_phase":
            cfg["minimum_available_disk_bytes_before_native_phase"],
        "minimum_available_disk_bytes_at_phase_start":
            cfg["minimum_available_disk_bytes_at_phase_start"],
        "prior_study_data_allowed_in_fit": False,
        "automatic_lowering_selection_enabled": False,
        "speedup_claim_enabled": False,
        "inventory": roster,
        "inventory_sha256": sha(canonical(roster)),
    }
    PROTOCOL.write_bytes(canonical(value))
    return sha(PROTOCOL.read_bytes())


def check(expected_protocol_sha256: str, anchor_commit: str) -> dict:
    if not HEX64.fullmatch(expected_protocol_sha256 or "") or not HEX40.fullmatch(anchor_commit or ""):
        raise ValueError("full externally recorded protocol hash and anchor commit required")
    if not PROTOCOL.is_file() or not ANCHOR.is_file():
        raise ValueError("committed mixed cost protocol and freeze anchor required")
    committed(PROTOCOL)
    committed(ANCHOR, anchor_commit)
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       anchor_commit, "HEAD"], check=False).returncode:
        raise ValueError("mixed cost freeze anchor is not an ancestor")
    if sha(PROTOCOL.read_bytes()) != expected_protocol_sha256:
        raise ValueError("mixed cost protocol differs from externally recorded hash")
    anchor = json.loads(ANCHOR.read_bytes())
    try:
        timestamp = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("mixed cost anchor needs a UTC timestamp") from exc
    if (anchor.get("schema") != "s31-mixed-stage-cost-v1-freeze" or
            anchor.get("protocol_sha256") != expected_protocol_sha256 or
            timestamp.utcoffset() is None or timestamp.utcoffset().total_seconds() != 0 or
            timestamp > datetime.now(timezone.utc)):
        raise ValueError("mixed cost anchor differs from frozen protocol")
    cfg = design()
    value = json.loads(PROTOCOL.read_bytes())
    clean_stack()
    roster = inventory(cfg)
    if (value.get("schema") != SCHEMA or
            value.get("status") != "frozen-before-first-mixed-stage-build-under-this-revision" or
            value.get("design_sha256") != sha(DESIGN_PATH.read_bytes()) or
            value.get("source_template_sha256") != sha((ROOT / cfg["source_template"]).read_bytes()) or
            value.get("engine_gitlink_commit") != git("rev-parse", "HEAD:deps/stwo-zig") or
            value.get("compiler_sha256") != compiler_fingerprint() or
            value.get("tool_paths") != [relative(path) for path in tool_paths()] or
            value.get("tool_sha256") != tool_sha256() or
            value.get("host") != host_identity() or
            value.get("build_mode") != cfg["build_mode"] or
            value.get("lowering") != cfg["lowering"] or
            value.get("samples_per_call_count") != cfg["assignments_per_call_count"] or
            value.get("first_verified_boundary") != cfg["first_verified_boundary"] or
            value.get("model_features") != cfg["model_features"] or
            value.get("model_fit") != cfg["model_fit"] or
            value.get("accuracy_gate") != cfg["accuracy_gate"] or
            value.get("minimum_available_disk_bytes_before_native_phase") !=
                cfg["minimum_available_disk_bytes_before_native_phase"] or
            value.get("minimum_available_disk_bytes_at_phase_start") !=
                cfg["minimum_available_disk_bytes_at_phase_start"] or
            value.get("prior_study_data_allowed_in_fit") is not False or
            value.get("automatic_lowering_selection_enabled") is not False or
            value.get("speedup_claim_enabled") is not False or
            value.get("inventory") != roster or
            value.get("inventory_sha256") != sha(canonical(roster))):
        raise ValueError("mixed cost protocol differs from exact frozen stack or workload")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       value["source_base_commit"], anchor_commit], check=False).returncode:
        raise ValueError("mixed cost source base does not precede anchor")
    return value


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("draft", "check"))
    parser.add_argument("--expected-protocol-sha256")
    parser.add_argument("--anchor-commit")
    args = parser.parse_args()
    print(draft() if args.command == "draft" else
          check(args.expected_protocol_sha256, args.anchor_commit)["inventory_sha256"])
