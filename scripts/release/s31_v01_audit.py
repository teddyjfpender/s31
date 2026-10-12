#!/usr/bin/env python3
"""Run a current-head native proof matrix for every S31 CLI lowering.

This is executable evidence, not a v0.1 release certificate or soundness proof.
Each row builds a fresh package, checks its source binding, proves an honest
assignment, asks its generated verifier to accept, asks that verifier to reject
a changed public claim, and requires the independent value oracle to pass.
Text rows additionally compare canonical relations and complete reported AIR
geometry with a handwritten first-order equivalent.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from cli.parser import make_parser  # noqa: E402
from text_frontend import compile_file  # noqa: E402


@dataclasses.dataclass(frozen=True)
class Case:
    lowering: str
    source: str
    assignment: str
    manual: str | None = None
    fri_fold_step: int = 1

    @property
    def id(self) -> str:
        return self.lowering if self.fri_fold_step == 1 else f"{self.lowering}-fri{self.fri_fold_step}"

    @property
    def source_kind(self) -> str:
        return "text" if self.source.endswith(".s31") else "json-relation"


CASES = (
    Case("gate", "arithmetic/functional_square4.s31",
         "arithmetic/functional_square4.valid.json",
         "arithmetic/functional_square4_manual.s31"),
    Case("gate", "arithmetic/functional_square4.s31",
         "arithmetic/functional_square4.valid.json",
         "arithmetic/functional_square4_manual.s31", fri_fold_step=4),
    Case("chip", "recurrence/functional_step16.s31",
         "recurrence/functional_step16.valid.json",
         "recurrence/functional_step16_manual.s31"),
    Case("sparse-gate", "arithmetic/functional_square4.s31",
         "arithmetic/functional_square4.valid.json",
         "arithmetic/functional_square4_manual.s31"),
    Case("sparse-chip", "recurrence/functional_step16.s31",
         "recurrence/functional_step16.valid.json",
         "recurrence/functional_step16_manual.s31"),
    Case("sparse-wide-gate", "wide/functional_u256_sum.s31",
         "wide/u256_sum_checked.valid.json",
         "wide/functional_u256_sum_manual.s31"),
    Case("sparse-wide-gate", "wide/functional_u256_sum.s31",
         "wide/u256_sum_checked.valid.json",
         "wide/functional_u256_sum_manual.s31", fri_fold_step=4),
    Case("direct-gate", "arithmetic/functional_square4.s31",
         "arithmetic/functional_square4.valid.json",
         "arithmetic/functional_square4_manual.s31"),
    Case("direct-chip", "recurrence/functional_step16.s31",
         "recurrence/functional_step16.valid.json",
         "recurrence/functional_step16_manual.s31"),
    Case("sha-joint", "bitcoin/bitcoin_header_pow.s31.json",
         "bitcoin/bitcoin_header_pow.valid.json"),
    Case("sha-shift", "bitcoin/bitcoin_header_pow.s31.json",
         "bitcoin/bitcoin_header_pow.valid.json"),
    Case("sha-fused", "bitcoin/bitcoin_header_pow.s31.json",
         "bitcoin/bitcoin_header_pow.valid.json"),
)

# Compare the same complete public cost fields used by the functional proof gate.
COST_FIELDS = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)


def cli_lowerings() -> set[str]:
    parser = make_parser()
    for action in parser._actions:
        if isinstance(action, argparse._SubParsersAction):
            build = action.choices["build"]
            for option in build._actions:
                if option.dest == "lowering":
                    return set(option.choices)
    raise RuntimeError("S31 build --lowering choices were not found")


def cli_fri_fold_steps() -> set[int]:
    parser = make_parser()
    for action in parser._actions:
        if isinstance(action, argparse._SubParsersAction):
            build = action.choices["build"]
            for option in build._actions:
                if option.dest == "fri_fold_step":
                    return set(option.choices)
    raise RuntimeError("S31 build --fri-fold-step choices were not found")


def case_ids() -> set[str]:
    return {case.id for case in CASES}


def fixture_digests_consistent(selected: set[str], rows: dict[str, dict]) -> bool:
    """Repeated fixtures must have one digest across every selected row."""
    seen: dict[str, str] = {}
    for case in CASES:
        if case.id not in selected:
            continue
        row = rows[case.id]
        if row["status"] != "passed":
            return False
        for path, field in ((case.source, "source_sha256"),
                            (case.assignment, "assignment_sha256"),
                            (case.manual, "handwritten_source_sha256")):
            if path is None:
                continue
            value = row.get(field)
            if (type(value) is not str or len(value) != 64 or
                    any(character not in "0123456789abcdef" for character in value)):
                return False
            if path in seen and seen[path] != value:
                return False
            seen[path] = value
    return True


def check_inventory() -> None:
    declared = [case.id for case in CASES]
    if len(declared) != len(set(declared)):
        raise ValueError("release matrix has duplicate case rows")
    actual = cli_lowerings()
    base = {case.lowering for case in CASES if case.fri_fold_step == 1}
    if base != actual:
        raise ValueError(f"release matrix differs from CLI lowering choices: "
                         f"missing={sorted(actual - base)}, "
                         f"extra={sorted(base - actual)}")
    extra = {(case.lowering, case.fri_fold_step) for case in CASES if case.fri_fold_step != 1}
    if cli_fri_fold_steps() != {1, 4}:
        raise ValueError(f"release matrix differs from CLI FRI fold choices: {sorted(cli_fri_fold_steps())}")
    if extra != {("gate", 4), ("sparse-wide-gate", 4)}:
        raise ValueError(f"release matrix FRI schedule rows changed: {sorted(extra)}")
    for case in CASES:
        for name in (case.source, case.assignment, case.manual):
            if name is not None and not (S31 / "examples" / name).is_file():
                raise ValueError(f"release matrix fixture is missing: {name}")


def git_identity(path: Path) -> dict:
    def git(*args: str) -> str:
        return subprocess.check_output(("git", "-C", str(path), *args),
                                       text=True, stderr=subprocess.DEVNULL).strip()
    tracked = git("status", "--porcelain", "--untracked-files=no")
    return {"commit": git("rev-parse", "HEAD"),
            "tracked_changes": tracked,
            "worktree_clean": not git("status", "--porcelain", "--untracked-files=normal")}


def run_case(case: Case, work: Path) -> dict:
    source = S31 / "examples" / case.source
    assignment = S31 / "examples" / case.assignment
    source_sha256 = s31.file_hash(source)
    assignment_sha256 = s31.file_hash(assignment)
    relation_shape_equal = None
    manual_sha256 = None
    if case.manual is not None:
        manual_source = S31 / "examples" / case.manual
        manual_sha256 = s31.file_hash(manual_source)
        relation, _ = compile_file(source)
        manual_relation, _ = compile_file(manual_source)
        # Generated temporary names may differ; the canonical IR digest below
        # is the alpha-invariant equality check.
        relation_shape_equal = (
            relation["inputs"] == manual_relation["inputs"] and
            relation["public_outputs"] == manual_relation["public_outputs"] and
            [node["op"] for node in relation["nodes"]] ==
            [node["op"] for node in manual_relation["nodes"]])
        if not relation_shape_equal:
            raise AssertionError(f"{case.lowering}: functional and handwritten relation shapes differ")

    package = s31.build(source, work / "package", case.lowering,
                        fri_fold_step=case.fri_fold_step)
    manifest = s31.verify_package(package)
    if (manifest["lowering"] != case.lowering or
            manifest.get("fri_fold_step", 1) != case.fri_fold_step):
        raise AssertionError(f"{case.lowering}: package selected a different lowering")
    if (case.source_kind == "text") != ("source_text_sha256" in manifest):
        raise AssertionError(f"{case.lowering}: source kind not bound in package")
    binding = manifest["source_text_sha256"] if case.source_kind == "text" else manifest["program_sha256"]
    if binding != source_sha256 or s31.file_hash(source) != source_sha256:
        raise AssertionError(f"{case.lowering}: source changed or package bound a different source")
    cost = json.loads((package / "cost-report.json").read_text())
    matching_geometry = None
    if case.manual is not None:
        manual_package = s31.build(S31 / "examples" / case.manual,
                                   work / "manual-package", case.lowering,
                                   fri_fold_step=case.fri_fold_step)
        manual_manifest = s31.verify_package(manual_package)
        if manual_manifest["compiler_sha256"] != manifest["compiler_sha256"]:
            raise AssertionError(f"{case.lowering}: handwritten equivalent used another compiler")
        direct_cost = json.loads((manual_package / "cost-report.json").read_text())
        different = [field for field in COST_FIELDS if cost[field] != direct_cost[field]]
        if different:
            raise AssertionError(f"{case.lowering}: functional AIR geometry differs: {different}")
        matching_geometry = True

    trial = s31.trial(package, assignment, work / "trial")
    if (s31.file_hash(source) != source_sha256 or
            s31.file_hash(assignment) != assignment_sha256 or
            (case.manual is not None and s31.file_hash(manual_source) != manual_sha256)):
        raise AssertionError(f"{case.lowering}: fixture changed while the native trial ran")
    if (trial["lowering"] != case.lowering or
            trial["fri_fold_step"] != case.fri_fold_step or
            trial["canonical_ir_sha256"] != cost["canonical_ir_sha256"]):
        raise AssertionError(f"{case.lowering}: trial reports a different package or relation")
    if (trial["native_verifier_accepted"] is not True or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{case.lowering}: native proof, negative claim, or oracle failed")
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key_path = package / "verification-key.json"
    proof_path = work / "trial/proof.bin"
    statement_path = work / "trial/statement.json"
    key = json.loads(key_path.read_text())
    original_root = key["preprocessed_root"]
    key["preprocessed_root"] = ("00" if original_root != "00" * 32 else "11") * 32
    altered_key_path = work / "altered-key.json"
    s31.write_json(altered_key_path, key)
    proof_data = bytearray(proof_path.read_bytes())
    proof_data[-1] ^= 1
    altered_proof_path = work / "altered-proof.bin"
    altered_proof_path.write_bytes(proof_data)
    for label, proof, verification_key in (
            ("altered key", proof_path, altered_key_path),
            ("altered proof", altered_proof_path, key_path)):
        result = subprocess.run((str(verifier), str(proof), str(statement_path),
                                 str(verification_key)), capture_output=True, text=True)
        if result.returncode != 1:
            raise AssertionError(f"{case.id}: verifier did not reject {label} cleanly "
                                 f"(exit {result.returncode})")
    return {
        "status": "passed", "source_kind": case.source_kind,
        "fri_fold_step": case.fri_fold_step,
        "source_sha256": source_sha256,
        "assignment_sha256": assignment_sha256,
        "handwritten_source_sha256": manual_sha256,
        "program_sha256": manifest["program_sha256"],
        "compiler_sha256": manifest["compiler_sha256"],
        "canonical_ir_sha256": cost["canonical_ir_sha256"],
        "key_sha256": s31.file_hash(package / "verification-key.json"),
        "native_verifier_sha256": s31.file_hash(
            package / "bin" / f"s31-{manifest['name']}-native-verifier"),
        "proof_sha256": trial["proof_sha256"],
        "proof_bytes": trial["proof_bytes"],
        "raw": cost["raw"], "padded": cost["padded"],
        "preprocessed_cells": cost["preprocessed_cells"],
        "fri": trial["visible_fri"],
        "native_verifier_accepted": True,
        "changed_public_statement_rejected": True,
        "altered_key_rejected": True,
        "altered_proof_rejected": True,
        "independent_value_oracle_passed": True,
        "same_relation_shape_as_handwritten": relation_shape_equal,
        "same_canonical_ir_as_handwritten": matching_geometry,
        "same_reported_air_geometry_as_handwritten": matching_geometry,
    }


def audit(selected: set[str], execute: bool, runner=run_case) -> dict:
    check_inventory()
    unknown = selected - case_ids()
    if unknown:
        raise ValueError(f"unknown lowerings: {sorted(unknown)}")
    report = {
        "schema": "s31-v01-supported-profile-audit-v1",
        "audit_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "repository": git_identity(ROOT),
        "engine": git_identity(ROOT / "deps/stwo-zig"),
        "scope": "one checked-in fixture per supported lowering/FRI pair; text zero-cost parity where a manual fixture exists",
        "limitations": [
            "This finite matrix is not a compiler correspondence or native PCS/FRI soundness proof.",
            "Specialized SHA rows use normalized JSON relations, not functional text source.",
            "Record ABI variants, recursion, and arbitrary programs require separate gates.",
            "Reported hashes are evidence identifiers; they are not independent distribution trust pins.",
        ],
        "cases": {},
    }
    for case in CASES:
        row = {"source": case.source, "assignment": case.assignment,
               "source_kind": case.source_kind,
               "fri_fold_step": case.fri_fold_step,
               "handwritten_equivalent": case.manual,
               "status": "not-run"}
        if execute and case.id in selected:
            if runner is run_case:
                print(f"auditing {case.id}...", file=sys.stderr, flush=True)
            try:
                with tempfile.TemporaryDirectory(prefix=f"s31-audit-{case.id}-") as directory:
                    row.update(runner(case, Path(directory)))
            except Exception as exc:
                row.update({"status": "failed", "error": f"{type(exc).__name__}: {exc}"})
            if runner is run_case:
                print(f"{case.id}: {row['status']}", file=sys.stderr, flush=True)
        report["cases"][case.id] = row
    report["selected_passed"] = all(report["cases"][name]["status"] == "passed"
                                    for name in selected) if execute else False
    report["fixture_identity_consistent"] = (
        execute and report["selected_passed"] and
        fixture_digests_consistent(selected, report["cases"]))
    report["repository_at_end"] = git_identity(ROOT)
    report["engine_at_end"] = git_identity(ROOT / "deps/stwo-zig")
    report["compiler_sha256_at_end"] = s31.compiler_fingerprint() if execute else None
    compiler_hashes = {report["cases"][name].get("compiler_sha256") for name in selected
                       if report["cases"][name]["status"] == "passed"}
    report["matrix_identity_consistent"] = (
        execute and report["selected_passed"] and report["fixture_identity_consistent"] and
        None not in compiler_hashes and
        compiler_hashes == {report["compiler_sha256_at_end"]} and
        report["repository"]["commit"] == report["repository_at_end"]["commit"] and
        report["engine"]["commit"] == report["engine_at_end"]["commit"])
    report["complete_profile_matrix_passed"] = (
        execute and selected == case_ids() and report["matrix_identity_consistent"])
    report["release_candidate_worktree_clean"] = (
        report["repository"]["worktree_clean"] and report["repository_at_end"]["worktree_clean"] and
        report["engine"]["worktree_clean"] and report["engine_at_end"]["worktree_clean"])
    report["summary"] = {
        status: sum(row["status"] == status for row in report["cases"].values())
        for status in ("passed", "failed", "not-run")
    }
    report["release_claim"] = "not-established"
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="validate and print the matrix without native work")
    parser.add_argument("--profile", action="append", choices=sorted(case_ids()),
                        help="run only this lowering/schedule row (repeatable); default runs all twelve")
    parser.add_argument("--out", type=Path, help="write the same JSON report to this file")
    args = parser.parse_args(argv)
    try:
        report = audit(set(args.profile or case_ids()), not args.list)
    except Exception as exc:
        report = {"schema": "s31-v01-supported-profile-audit-v1",
                  "status": "invalid-audit", "error": f"{type(exc).__name__}: {exc}"}
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded)
    return 1 if report.get("status") == "invalid-audit" or (
        not args.list and
        (not report["selected_passed"] or not report["matrix_identity_consistent"])) else 0


if __name__ == "__main__":
    raise SystemExit(main())
