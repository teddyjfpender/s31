#!/usr/bin/env python3
"""Check finite S31 v0.1 release-candidate evidence without running native proofs.

This checks report consistency and repository identity. It does not turn local
test reports, Lean models, or a remote branch into a soundness certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
AUDIT_CASES = frozenset({
    "gate", "gate-fri4", "chip", "sparse-gate", "sparse-chip",
    "sparse-wide-gate", "sparse-wide-gate-fri4", "direct-gate", "direct-chip",
    "sha-joint", "sha-shift", "sha-fused",
})
# This duplicates the finite audit inventory deliberately: a changed audit
# script or report must not silently choose different source/assignment bytes.
AUDIT_FIXTURES = {
    "gate": ("arithmetic/functional_square4.s31", "arithmetic/functional_square4.valid.json", "arithmetic/functional_square4_manual.s31"),
    "gate-fri4": ("arithmetic/functional_square4.s31", "arithmetic/functional_square4.valid.json", "arithmetic/functional_square4_manual.s31"),
    "chip": ("recurrence/functional_step16.s31", "recurrence/functional_step16.valid.json", "recurrence/functional_step16_manual.s31"),
    "sparse-gate": ("arithmetic/functional_square4.s31", "arithmetic/functional_square4.valid.json", "arithmetic/functional_square4_manual.s31"),
    "sparse-chip": ("recurrence/functional_step16.s31", "recurrence/functional_step16.valid.json", "recurrence/functional_step16_manual.s31"),
    "sparse-wide-gate": ("wide/functional_u256_sum.s31", "wide/u256_sum_checked.valid.json", "wide/functional_u256_sum_manual.s31"),
    "sparse-wide-gate-fri4": ("wide/functional_u256_sum.s31", "wide/u256_sum_checked.valid.json", "wide/functional_u256_sum_manual.s31"),
    "direct-gate": ("arithmetic/functional_square4.s31", "arithmetic/functional_square4.valid.json", "arithmetic/functional_square4_manual.s31"),
    "direct-chip": ("recurrence/functional_step16.s31", "recurrence/functional_step16.valid.json", "recurrence/functional_step16_manual.s31"),
    "sha-joint": ("bitcoin/bitcoin_header_pow.s31.json", "bitcoin/bitcoin_header_pow.valid.json", None),
    "sha-shift": ("bitcoin/bitcoin_header_pow.s31.json", "bitcoin/bitcoin_header_pow.valid.json", None),
    "sha-fused": ("bitcoin/bitcoin_header_pow.s31.json", "bitcoin/bitcoin_header_pow.valid.json", None),
}
FEATURE_CASES = frozenset({
    "v1-source-relation", "v2-record-source-relation", "static-sum-dce-source",
    "static-enum-effects-source",
    "direct-add-source", "direct-sub-le-source", "direct-mul-source",
    "record-u8-source", "record-u16-source", "record-u32-source",
    "static-sum-dce-native", "static-enum-if-native", "v2-record-source-native",
    "direct-add-all-native", "direct-sub-le-all-native", "direct-mul-all-native",
    "record-u8-native", "record-u16-native", "record-u32-native",
})
# Exact finite commands expected from the pinned full-mode feature runner.
# The interpreter path may vary by host; the script and arguments may not.
FEATURE_COMMANDS = {
    "v1-source-relation": ("src/frontends/s31/tests/python/security/test_source_relation_fragment.py",),
    "v2-record-source-relation": ("src/frontends/s31/tests/python/security/test_record_source_fragment.py",),
    "static-sum-dce-source": ("src/frontends/s31/tests/python/functional/test_static_sum_dce.py",),
    "static-enum-effects-source": ("src/frontends/s31/tests/python/generated/test_static_enum_effect_generated.py",),
    "direct-add-source": ("src/frontends/s31/tests/acceptance/math/addition.py", "--source-only"),
    "direct-sub-le-source": ("src/frontends/s31/tests/acceptance/math/direct_binary.py",),
    "direct-mul-source": ("src/frontends/s31/tests/acceptance/math/direct_multiplication.py",),
    "record-u8-source": ("src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py",),
    "record-u16-source": ("src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py",),
    "record-u32-source": ("src/frontends/s31/tests/acceptance/record_abi/public_u32_direct_gate_v2.py",),
    "static-sum-dce-native": ("src/frontends/s31/tests/acceptance/functional/static_sum_dce.py",),
    "static-enum-if-native": ("src/frontends/s31/tests/acceptance/functional/static_enum_if.py",),
    "v2-record-source-native": ("src/frontends/s31/tests/acceptance/record_abi/record_source_fragment_v2.py",),
    "direct-add-all-native": ("src/frontends/s31/tests/acceptance/math/addition.py", "--lowering", "direct-gate"),
    "direct-sub-le-all-native": ("src/frontends/s31/tests/acceptance/math/direct_binary.py", "--native"),
    "direct-mul-all-native": ("src/frontends/s31/tests/acceptance/math/direct_multiplication.py", "--native", "--mode", "both"),
    "record-u8-native": ("src/frontends/s31/tests/acceptance/record_abi/public_u8_direct_gate_v2.py", "--native"),
    "record-u16-native": ("src/frontends/s31/tests/acceptance/record_abi/public_u16_direct_gate_v2.py", "--native"),
    "record-u32-native": ("src/frontends/s31/tests/acceptance/record_abi/public_u32_direct_gate_v2.py", "--native"),
}
FORMAL_COMMANDS = {
    "bindings": ["python3", "-B", "scripts/s31_formal.py"],
    "lake_build": ["lake", "build", "S31"],
    "leanchecker": ["lake", "env", "leanchecker", "S31"],
}
FORMAL_FILES = {
    "inventory_sha256": "formal/s31/proof-inventory.json",
    "bindings_sha256": "formal/s31/source-bindings.json",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def sha(value: object) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def oid(value: object) -> bool:
    return isinstance(value, str) and len(value) in (40, 64) and all(c in "0123456789abcdef" for c in value)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load(path: Path) -> dict:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"{path}: expected JSON object")
    return value


def validate_reports(audit: dict, feature: dict, formal: dict, *, compiler: str,
                     root: Path = ROOT) -> dict:
    """Validate finite reports; returns identities for the live git check."""
    require(sha(compiler), "compiler pin must be a lowercase SHA-256")
    require(audit.get("schema") == "s31-v01-supported-profile-audit-v1", "wrong audit schema")
    require(audit.get("release_claim") == "not-established", "audit overclaims release status")
    audit_script = root / "scripts/release/s31_v01_audit.py"
    require(audit_script.is_file() and
            audit.get("audit_script_sha256") == digest(audit_script),
            "audit script differs from current tree")
    for key in ("selected_passed", "fixture_identity_consistent", "matrix_identity_consistent",
                "complete_profile_matrix_passed", "release_candidate_worktree_clean"):
        require(audit.get(key) is True, f"audit control failed: {key}")
    require(audit.get("compiler_sha256_at_end") == compiler, "audit compiler pin mismatch")
    rows = audit.get("cases")
    require(isinstance(rows, dict) and set(rows) == AUDIT_CASES, "audit matrix is incomplete or changed")
    require(audit.get("summary") == {"passed": 12, "failed": 0, "not-run": 0},
            "audit summary is not 12/12")
    for name, row in rows.items():
        require(isinstance(row, dict) and row.get("status") == "passed", f"audit row failed: {name}")
        require(row.get("compiler_sha256") == compiler, f"audit row compiler mismatch: {name}")
        source, assignment, manual = AUDIT_FIXTURES[name]
        require(row.get("source") == source and row.get("assignment") == assignment and
                row.get("handwritten_equivalent") == manual,
                f"audit row {name}: fixture identity mismatch")
        expected_kind = "json-relation" if source.endswith(".json") else "text"
        expected_fold = 4 if name in {"gate-fri4", "sparse-wide-gate-fri4"} else 1
        require(row.get("source_kind") == expected_kind and
                row.get("fri_fold_step") == expected_fold,
                f"audit row {name}: source kind or FRI schedule mismatch")
        for path, key in ((source, "source_sha256"), (assignment, "assignment_sha256"),
                          (manual, "handwritten_source_sha256")):
            if path is not None:
                fixture = root / "src/frontends/s31/examples" / path
                require(fixture.is_file() and not fixture.is_symlink() and
                        row.get(key) == digest(fixture),
                        f"audit row {name}: current fixture differs: {path}")
        for key in ("native_verifier_accepted", "changed_public_statement_rejected",
                    "altered_key_rejected", "altered_proof_rejected",
                    "independent_value_oracle_passed"):
            require(row.get(key) is True, f"audit row {name}: missing {key}")
        if row.get("source_kind") == "text":
            for key in ("same_relation_shape_as_handwritten", "same_canonical_ir_as_handwritten",
                        "same_reported_air_geometry_as_handwritten"):
                require(row.get(key) is True, f"audit row {name}: missing {key}")
        else:
            require(name in {"sha-joint", "sha-shift", "sha-fused"} and
                    row.get("source_kind") == "json-relation", f"audit row {name}: wrong source kind")
    repo = audit.get("repository", {})
    repo_end = audit.get("repository_at_end", {})
    engine = audit.get("engine", {})
    engine_end = audit.get("engine_at_end", {})
    require(all(isinstance(x, dict) for x in (repo, repo_end, engine, engine_end)),
            "audit git identity malformed")
    source_commit = repo.get("commit")
    require(oid(source_commit) and source_commit == repo_end.get("commit"),
            "audit source commit changed")
    require(oid(engine.get("commit")) and engine.get("commit") == engine_end.get("commit"),
            "audit engine commit changed")
    require(all(x.get("worktree_clean") is True for x in (repo, repo_end, engine, engine_end)),
            "audit ran from dirty source or engine")

    require(feature.get("schema") == "s31-scoped-feature-gate-v1", "wrong feature schema")
    gate_script = root / "scripts/release/s31_feature_gate.py"
    require(gate_script.is_file() and not gate_script.is_symlink() and
            feature.get("gate_script_sha256") == digest(gate_script),
            "feature gate script differs from current tree")
    require(feature.get("mode") == "full", "feature gate was not full mode")
    require(feature.get("release_claim") == "not-established", "feature report overclaims release status")
    for key in ("selected_passed", "mode_complete", "compiler_identity_consistent",
                "script_identity_consistent"):
        require(feature.get(key) is True, f"feature control failed: {key}")
    require(feature.get("compiler_sha256_start") == compiler and
            feature.get("compiler_sha256_end") == compiler, "feature compiler pin mismatch")
    require(feature.get("selected") == sorted(FEATURE_CASES), "feature selection is not all 19 checks")
    checks = feature.get("cases")
    require(isinstance(checks, dict) and set(checks) == FEATURE_CASES,
            "feature matrix is incomplete or changed")
    for name, row in checks.items():
        require(isinstance(row, dict) and row.get("status") == "passed" and
                row.get("returncode") == 0 and isinstance(row.get("controls"), dict),
                f"feature row failed: {name}")
        for key in ("command_sha256", "result_sha256", "stdout_sha256", "stderr_sha256"):
            require(sha(row.get(key)), f"feature row {name}: invalid {key}")
        outcome = {key: row[key] for key in
                   ("command_sha256", "returncode", "stdout_sha256", "stderr_sha256")}
        require(row["result_sha256"] == hashlib.sha256(canonical(outcome)).hexdigest(),
                f"feature row {name}: result identity mismatch")
        command = row.get("command")
        require(isinstance(command, dict) and row["command_sha256"] ==
                hashlib.sha256(canonical(command)).hexdigest(),
                f"feature row {name}: command identity mismatch")
        argv = command.get("argv")
        require(isinstance(argv, list) and len(argv) >= 3 and
                isinstance(argv[0], str) and argv[0] != "" and argv[1] == "-B" and
                tuple(argv[2:]) == FEATURE_COMMANDS[name] and
                command.get("cwd") == str(root),
                f"feature row {name}: command differs from expected full-mode check")
        script = (root / argv[2]).resolve()
        require(script.is_relative_to(root.resolve()) and script.is_file() and
                command.get("script_sha256") == digest(script),
                f"feature row {name}: script differs from current tree")

    require(formal.get("schema") == "s31-v01-formal-checks-v1", "wrong formal report schema")
    require(formal.get("compiler_sha256") == compiler, "formal compiler pin mismatch")
    require(oid(formal.get("source_commit")), "formal source commit is missing")
    for key, name in FORMAL_FILES.items():
        path = root / name
        require(path.is_file() and not path.is_symlink() and formal.get(key) == digest(path),
                f"formal {key} differs from current tree")
    commands = formal.get("checks")
    require(isinstance(commands, dict) and set(commands) == set(FORMAL_COMMANDS),
            "formal command evidence is incomplete")
    for name, expected in FORMAL_COMMANDS.items():
        row = commands[name]
        require(isinstance(row, dict) and row.get("command") == expected and
                row.get("returncode") == 0, f"formal command failed: {name}")
        log_name = row.get("log")
        require(isinstance(log_name, str) and log_name != "", f"formal log missing: {name}")
        log = Path(log_name)
        if not log.is_absolute():
            log = root / log
        require(log.is_file() and not log.is_symlink() and row.get("log_sha256") == digest(log),
                f"formal log digest mismatch: {name}")
    return {"source_commit": source_commit, "formal_commit": formal["source_commit"],
            "engine_commit": engine["commit"],
            "compiler_sha256": compiler, "audit_profiles": 12, "feature_checks": 19,
            "formal_commands": 3}


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def require_formal_tree_unchanged(root: Path, formal_commit: str, head: str) -> None:
    # The JSON inventory alone cannot reveal new or edited Lean modules.
    result = subprocess.run(
        ["git", "-C", str(root), "diff", "--quiet", formal_commit, head,
         "--", "formal/s31", "scripts/s31_formal.py"], check=False)
    require(result.returncode == 0,
            "formal sources or binding checker changed since formal report")


def validate_live_identity(identity: dict, *, root: Path, remote: str, branch: str) -> dict:
    sys.path.insert(0, str(root / "src/frontends/s31/python"))
    from package.context import compiler_fingerprint  # noqa: E402

    require(compiler_fingerprint() == identity["compiler_sha256"],
            "candidate compiler differs from pinned reports")
    head = git(root, "rev-parse", "HEAD")
    require(oid(head), "invalid candidate commit")
    require(not git(root, "status", "--porcelain", "--untracked-files=normal"),
            "candidate worktree is dirty")
    require(git(root / "deps/stwo-zig", "rev-parse", "HEAD") == identity["engine_commit"],
            "pinned engine differs from audit")
    require(not git(root / "deps/stwo-zig", "status", "--porcelain", "--untracked-files=normal"),
            "pinned engine worktree is dirty")
    for name in ("source_commit", "formal_commit"):
        result = subprocess.run(["git", "-C", str(root), "merge-base", "--is-ancestor",
                                 identity[name], head], check=False)
        require(result.returncode == 0, f"{name} is not an ancestor of candidate")
    # A descendant commit may update Lean sources, lake dependencies, or the
    # source-binding checker while leaving the inventory JSON byte-identical.
    # Require a fresh formal report after any such update.
    require_formal_tree_unchanged(root, identity["formal_commit"], head)
    refs = git(root, "ls-remote", "--heads", remote, branch).splitlines()
    require(len(refs) == 1 and refs[0].split() == [head, f"refs/heads/{branch}"],
            "candidate HEAD is not the remote branch tip")
    return {**identity, "candidate_commit": head, "remote": remote, "branch": branch,
            "status": "scoped-candidate-gates-passed",
            "scope": "finite supported profiles only; no general soundness, zero knowledge, or cost guarantee"}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--features", type=Path, required=True)
    parser.add_argument("--formal", type=Path, required=True)
    parser.add_argument("--compiler-sha256", required=True)
    parser.add_argument("--remote", default="origin")
    parser.add_argument("--branch", required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args(argv)
    try:
        identity = validate_reports(load(args.audit), load(args.features), load(args.formal),
                                    compiler=args.compiler_sha256)
        report = validate_live_identity(identity, root=ROOT, remote=args.remote, branch=args.branch)
        code = 0
    except (OSError, subprocess.CalledProcessError, ValueError, json.JSONDecodeError) as exc:
        report = {"schema": "s31-v01-candidate-check-v1", "status": "rejected",
                  "reason": f"{type(exc).__name__}: {exc}"}
        code = 1
    else:
        report = {"schema": "s31-v01-candidate-check-v1", **report}
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded)
    sys.stdout.write(encoded)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
