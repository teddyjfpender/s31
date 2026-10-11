#!/usr/bin/env python3
"""Read-only replay of the frozen V6 transfer evidence.

The frozen runner and its thresholds are inputs, not dependencies of the
calculations below. Native verifier replay is opt-in so static audits do not
contend with an active measurement run.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import re
import statistics
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31_DIR = HERE.parents[1]
ROOT = S31_DIR.parents[2]
sys.path.insert(0, str(S31_DIR / "python"))

from oracle import evaluate_relation  # independent Python value semantics

FREEZE_COMMIT = "5fbf2fc05cd80a534c00efac6dfcae577e44137b"
PROTOCOL_REL = Path("design/s31/measurements/language/whole-prover-transfer-v1.json")
V6_REL = Path("design/s31/measurements/language/whole-prover-cost-v6-audit.json")
TARGETS = ("paired_prove_and_verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes")
CHANGED = re.compile(r"^(public_inputs|public_outputs)\.([A-Za-z_][A-Za-z0-9_]*)\[0\]$")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    return digest(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def same(actual: object, expected: object, label: str) -> None:
    """Compare serialized evidence, allowing only rounding of finite floats."""
    if isinstance(expected, float):
        require(isinstance(actual, (int, float)) and not isinstance(actual, bool)
                and math.isfinite(actual) and math.isclose(actual, expected, rel_tol=1e-12,
                                                            abs_tol=1e-9), label)
    elif isinstance(expected, dict):
        require(isinstance(actual, dict) and actual.keys() == expected.keys(), label)
        for key, value in expected.items():
            same(actual[key], value, f"{label}.{key}")
    elif isinstance(expected, list):
        require(isinstance(actual, list) and len(actual) == len(expected), label)
        for index, value in enumerate(expected):
            same(actual[index], value, f"{label}[{index}]")
    else:
        require(type(actual) is type(expected) and actual == expected, label)


def committed_bytes(relative: Path) -> bytes:
    return subprocess.check_output(["git", "-C", str(ROOT), "show",
                                    f"{FREEZE_COMMIT}:{relative.as_posix()}"])


def frozen_inputs() -> tuple[dict, dict]:
    protocol_bytes = (ROOT / PROTOCOL_REL).read_bytes()
    require(protocol_bytes == committed_bytes(PROTOCOL_REL), "protocol differs from freeze commit")
    protocol = json.loads(protocol_bytes)
    require(protocol["schema"] == "s31-whole-prover-v6-transfer-protocol-v1", "protocol schema")
    require(protocol["status"] == "frozen-before-native-transfer-observation", "freeze status")
    require(protocol["automatic_lowering_selection_enabled"] is False, "automatic lowering")
    audit_bytes = (ROOT / V6_REL).read_bytes()
    require(digest(audit_bytes) == protocol["v6_audit_sha256"], "V6 audit digest")
    audit = json.loads(audit_bytes)
    model = audit["model"]
    require(model["schema"] == "s31-whole-prover-cost-model-v6", "V6 model schema")
    require(model["compiler_sha256"] == protocol["v6_compiler_sha256"], "V6 compiler digest")
    require(model["training_host"] == protocol["host"], "training host")
    require(model["compiler_sha256"] != protocol["compiler_sha256"], "compiler revision")
    require(model["automatic_lowering_selection_enabled"] is False, "V6 automatic lowering")

    # The V1 protocol did not hash two transitive model/oracle modules. This
    # later checker closes the current-code audit gap by requiring the complete
    # Python source tree (except this new checker) to equal the freeze commit.
    frozen_python = set(subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", FREEZE_COMMIT,
         "src/frontends/s31/python", "src/frontends/s31/benchmarks"], text=True,
    ).splitlines())
    frozen_python = {name for name in frozen_python if name.endswith(".py")}
    current_python = {path.relative_to(ROOT).as_posix()
                      for directory in (S31_DIR / "python", S31_DIR / "benchmarks")
                      for path in directory.rglob("*.py")
                      if path.resolve() != Path(__file__).resolve()}
    require(current_python == frozen_python, "Python source roster changed after freeze")
    for name in frozen_python:
        relative = Path(name)
        require((ROOT / relative).read_bytes() == committed_bytes(relative),
                f"Python code changed after freeze: {relative}")
    tool = hashlib.sha256()
    for name in protocol["tool_paths"]:
        relative = Path(name)
        tool.update(relative.as_posix().encode())
        tool.update(b"\0")
        tool.update(bytes.fromhex(file_digest(ROOT / relative)))
    require(tool.hexdigest() == protocol["tool_sha256"], "V1 tool digest")
    return protocol, audit


def assignment_digest(path: Path) -> str:
    value = json.loads(path.read_bytes())
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":"),
                             ensure_ascii=True).encode())


def visible_fri(cost: dict, lowering: str) -> dict:
    fri = cost["fri"]
    last_layer = fri["last_layer_degree_bound"]
    if lowering in {"sha-shift", "sha-fused"}:
        last_layer = 1 << last_layer
    return {"pow_bits": fri["pow_bits"],
            "blowup_factor": 1 << fri["log_blowup_factor"],
            "last_layer_degree_bound": last_layer,
            "queries": fri["queries"], "fold_step": fri["fold_step"]}


def features(cost: dict, family: str, package: Path) -> dict:
    raw, padded = cost["raw"], cost["padded"]
    require(raw.keys() == padded.keys(), "raw/padded component sets")
    for table in (raw, padded):
        require(all(type(value) is int and value >= 0 for value in table.values()),
                "component row counts")
    result = {"raw_rows": float(sum(raw.values())),
              "padded_rows": float(sum(padded.values())),
              "preprocessed_cells": float(cost["preprocessed_cells"]),
              "hash_work": float(1 + raw.get("blake_g", 0)), "constant": 1.0}
    require(all(value > 0 for value in result.values()), "positive model features")
    if family == "chip":
        component = json.loads((package / "component-manifest.json").read_text())
        key = json.loads((package / "verification-key.json").read_text())
        require(component["schema"] == "s31-component-manifest-direct-chip-v2"
                and key["schema"] == "s31-verification-key-direct-chip-manifest-v2"
                and key["component_manifest"] == component, "sealed chip manifest")
        rows, cells = [], 0
        require([item["name"] for item in component["components"]] ==
                ["qm31_ops", "repeated_step_chip"], "chip component roster")
        for item in component["components"]:
            size = item["trace_log_size"]
            base = item["base_trace_columns"]
            interaction = item["interaction_trace_columns"]
            require(type(size) is int and 0 <= size <= 24 and type(base) is int
                    and base > 0 and type(interaction) is int and interaction > 0,
                    "chip geometry")
            row_count = 1 << size
            rows.append(row_count)
            cells += row_count * (base + interaction)
        require(component["chip_call"]["call_id"] == 0
                and component["chip_call"]["rounds"] == rows[1], "chip call rounds")
        result["chip_trace_cells"] = float(cells)
        result["chip_fri_domain_rows"] = float(max(rows))
    return result


def estimate(fit: dict, x: float) -> float:
    if "constant" in fit:
        return fit["constant"]
    return math.exp(fit["intercept"] + fit["slope"] * math.log(x))


def predict(policy: dict, case_features: dict) -> dict:
    wall = sum(estimate(stage["fit"], case_features[stage["feature"]])
               for stage in policy["wall_stages"].values())
    ratios = policy["wall_interval"]
    proof = policy["proof_bytes"]
    proof_center = estimate(proof["fit"], case_features[proof["feature"]])
    envelope = proof["training_loo_max_abs_log_error"]
    proof_low = proof.get("stochastic_trial_ratio_min", proof["training_trial_ratio_p05"])
    proof_high = proof.get("stochastic_trial_ratio_max", proof["training_trial_ratio_p95"])
    rss = policy["prover_peak_rss_bytes"]
    x = case_features[rss["feature"]]
    rss_center = (rss["fit"]["intercept_bytes"] + rss["fit"]["bytes_per_padded_row"] * x
                  if rss["fit_kind"] == "positive_affine_rss" else estimate(rss["fit"], x))
    require(rss_center > 0 and math.isfinite(rss_center), "positive RSS prediction")
    radius = max(rss["radius_bytes"], rss["relative_radius"] * rss_center)
    return {TARGETS[0]: {"center": wall, "lower": wall * ratios["ratio_p05"],
                         "upper": wall * ratios["ratio_p95"]},
            TARGETS[1]: {"center": proof_center,
                         "lower": proof_center * math.exp(-envelope) * proof_low,
                         "upper": proof_center * math.exp(envelope) * proof_high},
            TARGETS[2]: {"center": rss_center, "lower": max(0.0, rss_center - radius),
                         "upper": rss_center + radius}}


def positive(value: object, label: str) -> float:
    require(type(value) in (int, float) and math.isfinite(value) and value > 0, label)
    return float(value)


def trial_target(trial: dict, target: str) -> float:
    if target == TARGETS[0]:
        return positive(trial["prove_seconds"], "prove seconds") + positive(
            trial["verify_seconds"], "verify seconds")
    return positive(trial[target], target)


def target_results(trials: list[dict], predictions: dict) -> dict:
    result = {}
    for target in TARGETS:
        values = [trial_target(trial, target) for trial in trials]
        point = statistics.mean(values) if target == TARGETS[0] else statistics.median(values)
        predicted = predictions[target]
        result[target] = {"prediction": predicted, "measured_point": point,
                          "relative_point_error": abs(predicted["center"] - point) / point,
                          "covered_trials": sum(predicted["lower"] <= value <= predicted["upper"]
                                                for value in values),
                          "trial_count": len(values)}
    return result


def package_binding(package: Path, source: Path, item: dict, protocol: dict) -> tuple[dict, dict, dict]:
    manifest = json.loads((package / "manifest.json").read_text())
    cost = json.loads((package / "cost-report.json").read_text())
    relation = json.loads((package / "source.s31.json").read_text())
    require(manifest["compiler_sha256"] == protocol["compiler_sha256"], "package compiler")
    require(manifest["lowering"] == item["lowering"], "package lowering")
    require(manifest["canonical_ir_sha256"] == cost["canonical_ir_sha256"], "canonical IR")
    require(manifest["program_sha256"] == file_digest(package / "source.s31.json"), "program digest")
    require(relation["version"] == 1, "transfer replay expects flat v1 relations")
    if source.suffix == ".s31":
        require(manifest["source_text_sha256"] == file_digest(source), "text source digest")
        require(source.read_bytes() == (package / "source.s31").read_bytes(), "saved text source")
    else:
        require(source.read_bytes() == (package / "source.s31.json").read_bytes(),
                "saved JSON source")
    for name, expected in manifest["artifacts"].items():
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts, "artifact path")
        require(file_digest(package / relative) == expected, f"package artifact: {name}")
    return manifest, cost, relation


def check_changed_statement(statement: dict, changed: dict, field: str) -> None:
    match = CHANGED.fullmatch(field)
    require(match is not None, "changed public field label")
    category, name = match.groups()
    before = statement[category][name][0]
    after = changed[category][name][0]
    require(before != after, "changed public word is unchanged")
    expected = copy.deepcopy(statement)
    expected[category][name][0] = after
    require(changed == expected, "changed statement modified more than one word")


def verify_native(package: Path, manifest: dict, trial_dir: Path) -> None:
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    proof = trial_dir / "proof.bin"
    key = package / "verification-key.json"
    for statement, should_accept in (("statement.json", True),
                                     ("changed-statement.json", False)):
        result = subprocess.run([str(verifier), str(proof), str(trial_dir / statement),
                                 str(key)], capture_output=True, check=False)
        require((result.returncode == 0) is should_accept,
                f"native verifier control: {trial_dir}/{statement}")


def replay_trial(out: Path, name: str, index: int, assignment_path: Path,
                 compact: dict, package: Path, manifest: dict, relation: dict,
                 native: bool) -> None:
    trial_dir = out / name / "trials" / f"{index:02d}"
    full = json.loads((trial_dir / "trial-report.json").read_text())
    for key, value in compact.items():
        same(full[key], value, f"{name}[{index}].{key}")
    require(full["schema"] == "s31-trial-v1", "trial schema")
    require(full["program"] == manifest["name"], "trial program")
    require(Path(full["assignment"]).resolve() == assignment_path.resolve(), "trial assignment path")
    require(full["program_sha256"] == manifest["program_sha256"], "trial program digest")
    require(full["canonical_ir_sha256"] == manifest["canonical_ir_sha256"], "trial IR digest")
    proof = trial_dir / "proof.bin"
    require(proof.stat().st_size == compact["proof_bytes"]
            and file_digest(proof) == compact["proof_sha256"], "saved proof digest")
    assignment = json.loads(assignment_path.read_bytes())
    statement = json.loads((trial_dir / "statement.json").read_text())
    expected_statement = {key: assignment[key] for key in ("public_inputs", "public_outputs")}
    require(statement == expected_statement, "statement does not match assignment")
    changed = json.loads((trial_dir / "changed-statement.json").read_text())
    check_changed_statement(statement, changed, compact["changed_public_statement_rejected"])
    require(compact["native_verifier_accepted"] is True, "recorded native acceptance")
    require(compact["independent_value_oracle"]["status"] == "passed", "recorded oracle status")
    same(compact["independent_value_oracle"]["computed_public_outputs"],
         evaluate_relation(relation, assignment), "independent oracle replay")
    provenance = full["independent_value_oracle_provenance"]
    for filename in ("oracle.py", "poseidon2_oracle.py"):
        relative = (S31_DIR / "python" / filename).relative_to(ROOT).as_posix()
        require(provenance["source_sha256"][relative] == file_digest(ROOT / relative),
                f"oracle source provenance: {filename}")
    require(provenance["python_version"] == json.loads((ROOT / PROTOCOL_REL).read_text())["host"]["python"],
            "oracle Python version")
    for target in TARGETS:
        trial_target(compact, target)
    if native:
        verify_native(package, manifest, trial_dir)


def replay(out: Path, native: bool) -> dict:
    protocol, audit = frozen_inputs()
    model = audit["model"]
    corpus_path, summary_path = out / "corpus.json", out / "audit.json"
    corpus = json.loads(corpus_path.read_text())
    summary = json.loads(summary_path.read_text())
    require(corpus["schema"] == "s31-whole-prover-v6-transfer-corpus-v1", "corpus schema")
    require(summary["schema"] == "s31-whole-prover-v6-transfer-audit-v1", "summary schema")
    protocol_sha = file_digest(ROOT / PROTOCOL_REL)
    require(corpus["protocol_sha256"] == summary["protocol_sha256"] == protocol_sha,
            "corpus/protocol binding")
    require(summary["corpus_sha256"] == file_digest(corpus_path), "summary/corpus binding")
    for key in ("v6_audit_sha256", "compiler_sha256", "host"):
        same(corpus[key], protocol[key], f"corpus.{key}")
    for key in ("v6_audit_sha256", "compiler_sha256", "host"):
        same(summary[key], protocol[key], f"summary.{key}")
    require(corpus["engine_gitlink_commit"] == protocol["engine_gitlink_commit"],
            "engine gitlink")
    require(summary["automatic_lowering_selection_enabled"] is False, "summary lowering")
    require(set(protocol["diagnostic_gates"]["max_program_point_error"]) == set(TARGETS)
            and set(protocol["diagnostic_gates"]["min_pooled_trial_coverage"]) == set(TARGETS),
            "frozen diagnostic targets")
    specs = {item["name"]: item for item in protocol["programs"]}
    require(corpus["cases"].keys() == specs.keys(), "transfer program roster")
    training_sources = {row["source_sha256"] for row in audit["program_inventory"]["train"].values()}
    training_assignments = {sha for row in audit["program_inventory"]["train"].values()
                            for sha in row["assignment_sha256"]}
    require(training_sources == set(model["training_source_sha256"])
            and training_assignments == set(model["training_assignment_sha256"]),
            "V6 training inventory/model mismatch")
    old_sources = training_sources | {
        row["source_sha256"] for row in audit["program_inventory"]["validation"].values()}
    old_assignments = training_assignments | {
        sha for row in audit["program_inventory"]["validation"].values()
        for sha in row["assignment_sha256"]}
    seen_sources, seen_assignments = set(), set()
    checked_trials = 0
    recomputed_cases = {}
    for name, item in specs.items():
        case = corpus["cases"][name]
        require(case["family"] == item["family"] and case["size"] == item["size"],
                f"{name}: family/size")
        source_ext = ".s31" if item["family"] == "fixed_width" else ".s31.json"
        source = out / "sources" / f"{name}{source_ext}"
        source_sha = file_digest(source)
        require(source_sha == protocol["inventory"]["source_sha256"][name]
                == case["source_sha256"], f"{name}: source digest")
        require(source_sha not in old_sources | seen_sources, f"{name}: source overlap")
        seen_sources.add(source_sha)
        package = out / name / "package"
        manifest, cost, relation = package_binding(package, source, item, protocol)
        policy = model["families"][item["family"]]
        require(policy["lowering"] == item["lowering"] and policy["profile"] == cost["profile"],
                f"{name}: model profile")
        visible = visible_fri(cost, item["lowering"])
        same(visible, policy["visible_fri"], f"{name}: model FRI")
        same(case["visible_fri"], visible, f"{name}: corpus FRI")
        require(case["profile"] == cost["profile"], f"{name}: corpus profile")
        case_features = features(cost, item["family"], package)
        same(case["features"], case_features, f"{name}: model features")
        if item["family"] == "chip":
            binding = case["features"]
            require(binding["chip_trace_cells"] > 0, f"{name}: chip cells")
        require(case["build"]["package_reused"] is False, f"{name}: fresh package")
        compact_trials = case["trials"]
        require(len(compact_trials) == protocol["samples_per_program"], f"{name}: trial count")
        require(len(case["assignment_sha256"]) == len(compact_trials), f"{name}: digest count")
        for index, compact in enumerate(compact_trials):
            assignment_path = out / name / "assignments" / f"{index:02d}.json"
            assignment_sha = assignment_digest(assignment_path)
            require(assignment_sha == protocol["inventory"]["assignment_sha256"][name][index]
                    == case["assignment_sha256"][index], f"{name}[{index}]: assignment digest")
            require(assignment_sha not in old_assignments | seen_assignments,
                    f"{name}[{index}]: assignment overlap")
            seen_assignments.add(assignment_sha)
            replay_trial(out, name, index, assignment_path, compact, package, manifest,
                         relation, native)
            checked_trials += 1
        targets = target_results(compact_trials, predict(policy, case_features))
        same(case["targets"], targets, f"{name}: V6 target replay")
        recomputed_cases[name] = {"family": item["family"], "targets": targets}
    expected_family = {}
    for family in model["families"]:
        members = [case for case in recomputed_cases.values() if case["family"] == family]
        require(len(members) == 2, f"{family}: expected two transfer programs")
        expected_family[family] = {}
        for target in TARGETS:
            values = [case["targets"][target] for case in members]
            error = max(value["relative_point_error"] for value in values)
            coverage = sum(value["covered_trials"] for value in values) / sum(
                value["trial_count"] for value in values)
            expected_family[family][target] = {
                "max_program_point_error": error,
                "pooled_trial_coverage": coverage,
                "diagnostic_gate_pass": (
                    error <= protocol["diagnostic_gates"]["max_program_point_error"][target]
                    and coverage >= protocol["diagnostic_gates"]["min_pooled_trial_coverage"][target]),
            }
    same(summary["family_results"], expected_family, "frozen diagnostic gate replay")
    require(summary["diagnostic_gate_pass"] is all(
        result["diagnostic_gate_pass"] for family in expected_family.values()
        for result in family.values()), "overall diagnostic gate")
    return {"schema": "s31-whole-prover-v6-transfer-replay-v1",
            "freeze_commit": FREEZE_COMMIT, "protocol_sha256": protocol_sha,
            "corpus_sha256": file_digest(corpus_path), "audit_sha256": file_digest(summary_path),
            "source_count": len(seen_sources), "assignment_count": len(seen_assignments),
            "proofs_and_reports_checked": checked_trials,
            "native_original_and_changed_replayed": native,
            "diagnostic_gate_pass": summary["diagnostic_gate_pass"],
            "limitations": "Local read-only replay; the original freeze commit was not externally timestamped before observations. Native replay checks saved proof/statement acceptance, not source-to-circuit soundness or performance stability."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="completed transfer output directory")
    parser.add_argument("--native", action="store_true", help="rerun both native verifier controls for every proof")
    args = parser.parse_args()
    print(json.dumps(replay(args.out.resolve(), args.native), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
