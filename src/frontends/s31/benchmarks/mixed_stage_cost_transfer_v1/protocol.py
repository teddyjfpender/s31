"""Draft a source/stack-pinned candidate transfer protocol; no native work.

Commit this tool and design first. ``draft`` requires a clean committed stack,
then writes an unanchored candidate protocol. A later native collector must
require a committed freeze anchor and externally recorded full hash/commit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from cohort import (DESIGN_PATH, REFERENCE_PATH, ROOT, S31, canonical, design,
                    inventory, reference_inventory, sha)

sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks"))
from benchmark_whole_prover_cost_v3 import host_identity  # noqa: E402
from package.context import compiler_fingerprint  # noqa: E402

PROTOCOL = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-protocol.json"
ANCHOR = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-freeze.json"
MODEL_ANCHOR = ROOT / "design/s31/measurements/language/mixed-stage-cost-v1-model-freeze.json"


def git(*args: str) -> str:
    return subprocess.check_output(["git", "-C", str(ROOT), *args], text=True).strip()


def path_name(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def tools() -> list[Path]:
    # Pin transitive Python imports, including the ABI and independent oracle.
    return sorted({*(S31 / "benchmarks").rglob("*.py"),
                   *(S31 / "python").rglob("*.py"),
                   S31 / "tests/acceptance/mixed_boundary/registry_manifest_digest.py"})


def tool_sha256(paths: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in paths:
        digest.update(path_name(path).encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(sha(path.read_bytes())))
    return digest.hexdigest()


def committed(path: Path) -> None:
    try:
        saved = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                         f"HEAD:{path_name(path)}"],
                                        stderr=subprocess.DEVNULL)
    except subprocess.CalledProcessError as exc:
        raise ValueError(f"uncommitted transfer source: {path_name(path)}") from exc
    if saved != path.read_bytes():
        raise ValueError(f"transfer source differs from HEAD: {path_name(path)}")


def clean_stack(cfg: dict, paths: list[Path]) -> None:
    for path in [DESIGN_PATH, REFERENCE_PATH, MODEL_ANCHOR,
                 ROOT / cfg["source_template"], *paths]:
        committed(path)
    if git("status", "--porcelain", "--untracked-files=all", "--",
           "src/frontends/s31", "design/s31/measurements/language"):
        raise ValueError("transfer compiler, source, or tool has uncommitted files")
    if git("submodule", "status", "deps/stwo-zig").lstrip().startswith(("+", "-", "U")):
        raise ValueError("engine checkout does not match the pinned gitlink")
    engine = ROOT / "deps/stwo-zig"
    if engine.exists() and subprocess.run(["git", "-C", str(engine), "status",
                                           "--porcelain", "--untracked-files=all"],
                                          capture_output=True, check=False).stdout:
        raise ValueError("engine submodule is dirty")


def draft() -> dict:
    if PROTOCOL.exists():
        raise ValueError("candidate transfer protocol already exists; do not refreeze")
    cfg = design()
    paths = tools()
    clean_stack(cfg, paths)
    reference, _ = reference_inventory(cfg)
    model_anchor = json.loads(MODEL_ANCHOR.read_bytes())
    if (model_anchor.get("schema") != "s31-mixed-stage-cost-v1-model-freeze" or
            model_anchor.get("model_sha256") != cfg["reference_train_model_sha256"] or
            model_anchor.get("protocol_sha256") != cfg["reference_protocol_sha256"]):
        raise ValueError("reference training-only model anchor differs")
    saved_anchor = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                            f"{cfg['reference_model_anchor_commit']}:{path_name(MODEL_ANCHOR)}"])
    if (saved_anchor != MODEL_ANCHOR.read_bytes() or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            cfg["reference_model_anchor_commit"], "HEAD"],
                           check=False).returncode):
        raise ValueError("reference training model freeze is not an unchanged ancestor")
    executable = shutil.which("zig")
    if executable is None:
        raise ValueError("Zig executable is unavailable")
    roster = inventory(cfg)
    value = {
        "schema": "s31-mixed-stage-cost-transfer-v1-protocol-candidate",
        "status": "prepared-for-prospective-freeze",
        "design_sha256": sha(DESIGN_PATH.read_bytes()),
        "reference_protocol_sha256": cfg["reference_protocol_sha256"],
        "reference_inventory_sha256": sha(canonical(reference["inventory"])),
        "reference_train_model_sha256": cfg["reference_train_model_sha256"],
        "reference_model_anchor_commit": cfg["reference_model_anchor_commit"],
        "reference_model_anchor_sha256": sha(MODEL_ANCHOR.read_bytes()),
        "source_template_sha256": sha((ROOT / cfg["source_template"]).read_bytes()),
        "source_base_commit": git("rev-parse", "HEAD"),
        "engine_gitlink_commit": git("rev-parse", "HEAD:deps/stwo-zig"),
        "compiler_sha256": compiler_fingerprint(),
        "zig_executable_sha256": sha(Path(executable).resolve().read_bytes()),
        "host": host_identity(),
        "tool_paths": [path_name(path) for path in paths],
        "tool_sha256": tool_sha256(paths),
        "build_mode": cfg["build_mode"],
        "lowering": cfg["lowering"],
        "first_verified_boundary": cfg["first_verified_boundary"],
        "assignments_per_program": cfg["assignments_per_program"],
        "diagnostic_gates": cfg["diagnostic_gates"],
        "minimum_available_disk_bytes_at_phase_start":
            cfg["minimum_available_disk_bytes_at_phase_start"],
        "minimum_available_disk_bytes_before_native_unit":
            cfg["minimum_available_disk_bytes_before_native_unit"],
        "reference_heldout_observations_allowed_in_fit_or_gate_selection": False,
        "refitting_allowed": False,
        "automatic_lowering_selection_enabled": False,
        "speedup_claim_enabled": False,
        "inventory": roster,
        "inventory_sha256": sha(canonical(roster)),
    }
    PROTOCOL.write_bytes(canonical(value))
    return {"candidate_protocol_sha256": sha(PROTOCOL.read_bytes()),
            "inventory_sha256": value["inventory_sha256"],
            "source_base_commit": value["source_base_commit"]}


def check(expected_sha256: str, anchor_commit: str) -> dict:
    if (len(expected_sha256) != 64 or len(anchor_commit) != 40 or
            any(char not in "0123456789abcdef" for char in expected_sha256 + anchor_commit)):
        raise ValueError("full protocol SHA-256 and externally recorded anchor commit required")
    if not PROTOCOL.is_file() or not ANCHOR.is_file():
        raise ValueError("transfer protocol and freeze anchor must exist")
    cfg = design()
    paths = tools()
    clean_stack(cfg, paths)
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       anchor_commit, "HEAD"], check=False).returncode:
        raise ValueError("transfer freeze anchor is not an ancestor")
    for path in (PROTOCOL, ANCHOR):
        committed(path)
        saved = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                         f"{anchor_commit}:{path_name(path)}"])
        if saved != path.read_bytes():
            raise ValueError("transfer protocol or anchor differs from anchor commit")
    if sha(PROTOCOL.read_bytes()) != expected_sha256:
        raise ValueError("transfer protocol differs from externally recorded hash")
    anchor = json.loads(ANCHOR.read_bytes())
    try:
        instant = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as exc:
        raise ValueError("transfer freeze anchor requires UTC time") from exc
    if (anchor.get("schema") != "s31-mixed-stage-cost-transfer-v1-freeze" or
            anchor.get("protocol_sha256") != expected_sha256 or
            instant.utcoffset() is None or instant.utcoffset().total_seconds() != 0 or
            instant > datetime.now(timezone.utc)):
        raise ValueError("transfer freeze anchor differs from declared protocol")
    value = json.loads(PROTOCOL.read_bytes())
    reference, _ = reference_inventory(cfg)
    model_anchor = json.loads(MODEL_ANCHOR.read_bytes())
    executable = shutil.which("zig")
    if executable is None:
        raise ValueError("Zig executable is unavailable")
    roster = inventory(cfg)
    if (value.get("schema") != "s31-mixed-stage-cost-transfer-v1-protocol-candidate" or
            value.get("status") != "prepared-for-prospective-freeze" or
            value.get("design_sha256") != sha(DESIGN_PATH.read_bytes()) or
            value.get("reference_protocol_sha256") != cfg["reference_protocol_sha256"] or
            value.get("reference_inventory_sha256") != sha(canonical(reference["inventory"])) or
            value.get("reference_train_model_sha256") != cfg["reference_train_model_sha256"] or
            value.get("reference_model_anchor_commit") != cfg["reference_model_anchor_commit"] or
            value.get("reference_model_anchor_sha256") != sha(MODEL_ANCHOR.read_bytes()) or
            model_anchor.get("model_sha256") != cfg["reference_train_model_sha256"] or
            value.get("source_template_sha256") != sha((ROOT / cfg["source_template"]).read_bytes()) or
            value.get("engine_gitlink_commit") != git("rev-parse", "HEAD:deps/stwo-zig") or
            value.get("compiler_sha256") != compiler_fingerprint() or
            value.get("zig_executable_sha256") != sha(Path(executable).resolve().read_bytes()) or
            value.get("host") != host_identity() or
            value.get("tool_paths") != [path_name(path) for path in paths] or
            value.get("tool_sha256") != tool_sha256(paths) or
            value.get("build_mode") != cfg["build_mode"] or
            value.get("lowering") != cfg["lowering"] or
            value.get("first_verified_boundary") != cfg["first_verified_boundary"] or
            value.get("assignments_per_program") != cfg["assignments_per_program"] or
            value.get("diagnostic_gates") != cfg["diagnostic_gates"] or
            value.get("minimum_available_disk_bytes_at_phase_start") !=
                cfg["minimum_available_disk_bytes_at_phase_start"] or
            value.get("minimum_available_disk_bytes_before_native_unit") !=
                cfg["minimum_available_disk_bytes_before_native_unit"] or
            value.get("reference_heldout_observations_allowed_in_fit_or_gate_selection") is not False or
            value.get("refitting_allowed") is not False or
            value.get("automatic_lowering_selection_enabled") is not False or
            value.get("speedup_claim_enabled") is not False or
            value.get("inventory") != roster or
            value.get("inventory_sha256") != sha(canonical(roster))):
        raise ValueError("transfer protocol differs from exact prospective stack or roster")
    saved_model_anchor = subprocess.check_output(
        ["git", "-C", str(ROOT), "show",
         f"{cfg['reference_model_anchor_commit']}:{path_name(MODEL_ANCHOR)}"])
    if (saved_model_anchor != MODEL_ANCHOR.read_bytes() or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            cfg["reference_model_anchor_commit"],
                            value["source_base_commit"]], check=False).returncode):
        raise ValueError("reference training model freeze is not an unchanged ancestor")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       value["source_base_commit"], anchor_commit],
                      check=False).returncode:
        raise ValueError("transfer source base must precede freeze anchor")
    return value


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("draft", "check"))
    parser.add_argument("--expected-protocol-sha256")
    parser.add_argument("--anchor-commit")
    args = parser.parse_args()
    print(json.dumps(draft() if args.command == "draft" else
                     {"inventory_sha256": check(args.expected_protocol_sha256,
                                                args.anchor_commit)["inventory_sha256"]},
                     sort_keys=True))
