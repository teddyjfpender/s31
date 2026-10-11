#!/usr/bin/env python3
"""Prospective V8r1 study protocol. No native work is allowed before anchoring.

This module deliberately does not contain fitted coefficients or observations.
The protocol is generated once, after the compiler and engine commits settle.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
S31_DIR = BENCH.parent
ROOT = S31_DIR.parents[2]
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(S31_DIR / "python"))

import s31
import v8r1_design
from benchmark_whole_prover_cost_v3 import host_identity

PROTOCOL = ROOT / "design/s31/measurements/language/whole-prover-cost-v8r1.json"
MODEL = ROOT / "design/s31/measurements/language/whole-prover-cost-v8r1-model.json"
PROTOCOL_ANCHOR = ROOT / "design/s31/measurements/language/whole-prover-cost-v8r1-protocol-freeze.json"
MODEL_ANCHOR = ROOT / "design/s31/measurements/language/whole-prover-cost-v8r1-model-freeze.json"
V6_AUDIT = ROOT / "design/s31/measurements/language/whole-prover-cost-v6-audit.json"
TRANSFER_PROTOCOL = ROOT / "design/s31/measurements/language/whole-prover-transfer-v1.json"
SCHEMA = "s31-whole-prover-cost-protocol-v8r1"
DESIGN = v8r1_design.read_design()
SAMPLES = DESIGN["samples_per_program"]
MIN_FREE_BYTES = DESIGN["minimum_available_disk_bytes_before_native_phase"]
SPLITS = DESIGN["splits"]
GATES = DESIGN["predictive_accuracy_gate"]
RSS_UNCERTAINTY = DESIGN["rss_uncertainty"]
PROFILE_BY_FAMILY = {
    "arithmetic": "direct-m31-v4", "chip": "direct-m31-v4",
    "hash": "circuit-v1", "fixed_width": "direct-m31-v4",
}
VISIBLE_FRI = {"pow_bits": 26, "blowup_factor": 2,
               "last_layer_degree_bound": 1, "queries": 70, "fold_step": 1}
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", "-C", str(cwd), *args], text=True).strip()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def tool_paths() -> list[Path]:
    """Pin the complete transitive Python source surface, including both oracles."""
    return sorted({*BENCH.rglob("*.py"), *(S31_DIR / "python").rglob("*.py")})


def tool_digest(paths: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in paths:
        digest.update(relative(path).encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(s31.file_hash(path)))
    return digest.hexdigest()


def require_committed(path: Path, commit: str = "HEAD") -> None:
    name = relative(path)
    try:
        saved = subprocess.check_output(
            ["git", "-C", str(ROOT), "show", f"{commit}:{name}"],
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError as error:
        raise ValueError(f"source is not committed: {name}") from error
    if saved != path.read_bytes():
        raise ValueError(f"source differs from committed bytes: {name}")


def require_clean_sources() -> None:
    for path in tool_paths():
        require_committed(path)
    require_fingerprinted_zig_sources_committed()
    changed = git("status", "--porcelain", "--untracked-files=no", "--", "src")
    if changed:
        raise ValueError("fingerprinted source tree has uncommitted tracked changes")
    expected_engine = git("rev-parse", "HEAD:deps/stwo-zig")
    actual_engine = git("rev-parse", "HEAD", cwd=ROOT / "deps/stwo-zig")
    if actual_engine != expected_engine or git("status", "--porcelain", "--untracked-files=no",
                                               cwd=ROOT / "deps/stwo-zig"):
        raise ValueError("engine checkout must equal the clean committed gitlink")


def require_historical_evidence() -> None:
    """Old failed gates are disclosures, never V8r1 training data."""
    require_committed(v8r1_design.DESIGN)
    require_committed(v8r1_design.V7R1_PROTOCOL)
    require_committed(v8r1_design.V7R1_AUDIT)
    require_committed(v8r1_design.V8_PROTOCOL)
    require_committed(v8r1_design.V8_FAILURE)
    v8r1_design.v7.require_superseded_attempt()
    if v8r1_design.read_design() != DESIGN:
        raise ValueError("V8r1 prospective design changed")


def require_fingerprinted_zig_sources_committed() -> None:
    """Require every byte scanned by compiler_fingerprint to exist in HEAD."""
    # The package compiler fingerprint scans every Zig/Zon file under src,
    # including ignored and otherwise untracked files. The freeze must be
    # reproducible from its source-base commit, not just this local checkout.
    excluded = {".zig-cache", "zig-out", "target"}
    for path in (ROOT / "src").rglob("*"):
        if (path.is_file() and path.suffix in {".zig", ".zon"} and
                not excluded.intersection(path.parts)):
            require_committed(path)


def check_case_cost_geometry(case: dict, cost: dict, label: str) -> None:
    """Bind model features to the package's sealed native cost report."""
    fields_match = all(case.get(key) == cost.get(key)
                       for key in ("raw", "padded", "preprocessed_cells", "profile"))
    fri_matches = case.get("visible_fri") == s31.visible_fri(cost, case["lowering"])
    if not fields_match or not fri_matches:
        raise ValueError(f"{label}: corpus geometry differs from sealed package cost report")


def check_corpus_cost_geometry(corpus_path: Path, corpus: dict, protocol: dict) -> None:
    """Reject poisoned features before fitting or evaluating a frozen model."""
    split = corpus.get("split")
    if split not in ("train", "validation") or \
            corpus.get("cases", {}).keys() != protocol["inventory"][split].keys():
        raise ValueError("V8r1 corpus program roster differs from frozen inventory")
    for name, case in corpus["cases"].items():
        if re.fullmatch(r"[A-Za-z0-9_]+", name) is None:
            raise ValueError("unsafe V8r1 corpus program name")
        package = corpus_path.parent / name / "package"
        s31.verify_package(package)
        cost = json.loads((package / "cost-report.json").read_bytes())
        check_case_cost_geometry(case, cost, f"{split}/{name}")


def workloads(split: str, output: Path, samples: int, spec: dict) -> list[dict]:
    if split not in SPLITS or samples != SAMPLES or spec != SPLITS[split]:
        raise ValueError("V8r1 requires the committed prospective split and assignment count")
    return v8r1_design.workloads(split, output, DESIGN)


def inventory(output: Path, protocol: dict) -> dict:
    if protocol["samples_per_program"] != SAMPLES or protocol["splits"] != SPLITS:
        raise ValueError("V8r1 inventory settings differ from prospective design")
    return v8r1_design.inventory(output, DESIGN)


def protocol_template() -> dict:
    old = json.loads((ROOT / "design/s31/measurements/whole-prover-cost-v6.json").read_bytes())
    return {
        "schema": SCHEMA, "revision": "8r1",
        "status": "frozen-before-native-measurement-under-this-revision",
        "prospective_design_sha256": s31.file_hash(v8r1_design.DESIGN),
        "v7r1_protocol_sha256": s31.file_hash(v8r1_design.V7R1_PROTOCOL),
        "v7r1_audit_sha256": s31.file_hash(v8r1_design.V7R1_AUDIT),
        "v7r1_diagnostic_disclosure": DESIGN["v7r1_diagnostic_disclosure"],
        "v8_protocol_sha256": s31.file_hash(v8r1_design.V8_PROTOCOL),
        "v8_fit_failure_sha256": s31.file_hash(v8r1_design.V8_FAILURE),
        "v8_fit_failure_disclosure": DESIGN["v8_fit_failure_disclosure"],
        "source_base_commit": git("rev-parse", "HEAD"),
        "engine_gitlink_commit": git("rev-parse", "HEAD:deps/stwo-zig"),
        "compiler_sha256": s31.compiler_fingerprint(),
        "v6_audit_sha256": s31.file_hash(V6_AUDIT),
        "transfer_protocol_sha256": s31.file_hash(TRANSFER_PROTOCOL),
        "measurement_tool_paths": [relative(path) for path in tool_paths()],
        "measurement_tool_sha256": tool_digest(tool_paths()),
        "host": host_identity(), "samples_per_program": SAMPLES,
        "minimum_available_disk_bytes_before_native_phase": MIN_FREE_BYTES,
        "pow_bits_required": 26, "profiles": old["profiles"],
        "profile_by_family": PROFILE_BY_FAMILY,
        "visible_fri": VISIBLE_FRI,
        "stage_features": old["stage_features"],
        "chip_stage_features": old["chip_stage_features"],
        "accuracy_gate": GATES, "splits": SPLITS,
        "rss_uncertainty": RSS_UNCERTAINTY,
        "paired_mixed_vs_generic": {"status": "excluded-until-general-profile-admitted-and-packaged",
                                    "prospective_design": DESIGN["paired_mixed_vs_generic"]},
        "selection_policy": "Automatic lowering disabled; local pinned-stack prediction only",
        "automatic_lowering_selection_enabled": False,
        "process_wrapper": "fresh prover and native verifier OS processes per trial; Python perf_counter; native runtime timers recorded separately",
        "native_build_mode": "zig build install -Doptimize=ReleaseFast -Ds31-version=1 -Ds31-fri-fold-step=1; fresh package paths and native prover/verifier processes",
        "shape_reuse_disclosure": "Finite direct-chip powers of two and fixed-width division forms repeat earlier shapes. Source and assignment bytes are disjoint; shape novelty is not claimed.",
    }


def draft(output: Path) -> str:
    if PROTOCOL.exists():
        raise ValueError("V8r1 protocol already exists; never refreeze it in place")
    require_clean_sources()
    require_historical_evidence()
    protocol = protocol_template()
    protocol["inventory"] = inventory(output, protocol)
    s31.write_json(PROTOCOL, protocol)
    return s31.file_hash(PROTOCOL)


def committed_anchor(path: Path, commit: str, schema: str) -> dict:
    if HEX40.fullmatch(commit or "") is None:
        raise ValueError("anchor requires externally recorded full commit SHA")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       commit, "HEAD"], check=False).returncode:
        raise ValueError("anchor commit is not an ancestor")
    require_committed(path, commit)
    anchor = json.loads(path.read_bytes())
    if anchor.get("schema") != schema:
        raise ValueError("wrong freeze anchor schema")
    try:
        recorded = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError("anchor needs a timezone-aware UTC timestamp") from error
    if recorded.utcoffset() is None or recorded.utcoffset().total_seconds() != 0 or recorded > datetime.now(timezone.utc):
        raise ValueError("anchor timestamp must be UTC and not future")
    return anchor


def require_protocol(expected_sha: str, anchor_commit: str, output: Path | None = None,
                     *, enforce_host: bool = True) -> dict:
    if HEX64.fullmatch(expected_sha or "") is None or not PROTOCOL.is_file():
        raise ValueError("full externally recorded protocol SHA is required")
    require_committed(PROTOCOL)
    if s31.file_hash(PROTOCOL) != expected_sha:
        raise ValueError("protocol differs from recorded SHA")
    protocol = json.loads(PROTOCOL.read_bytes())
    if (protocol.get("schema") != SCHEMA or
        protocol.get("status") != "frozen-before-native-measurement-under-this-revision" or
        protocol.get("revision") != "8r1" or
        protocol.get("prospective_design_sha256") != s31.file_hash(v8r1_design.DESIGN) or
        protocol.get("v7r1_protocol_sha256") != s31.file_hash(v8r1_design.V7R1_PROTOCOL) or
        protocol.get("v7r1_audit_sha256") != s31.file_hash(v8r1_design.V7R1_AUDIT) or
        protocol.get("v7r1_diagnostic_disclosure") != DESIGN["v7r1_diagnostic_disclosure"] or
        protocol.get("v8_protocol_sha256") != s31.file_hash(v8r1_design.V8_PROTOCOL) or
        protocol.get("v8_fit_failure_sha256") != s31.file_hash(v8r1_design.V8_FAILURE) or
        protocol.get("v8_fit_failure_disclosure") != DESIGN["v8_fit_failure_disclosure"] or
        protocol.get("rss_uncertainty") != RSS_UNCERTAINTY or
        protocol.get("paired_mixed_vs_generic") != {
            "status": "excluded-until-general-profile-admitted-and-packaged",
            "prospective_design": DESIGN["paired_mixed_vs_generic"]} or
        protocol.get("automatic_lowering_selection_enabled") is not False):
        raise ValueError("wrong or unfrozen V8r1 protocol")
    baseline = json.loads((ROOT / "design/s31/measurements/whole-prover-cost-v6.json").read_bytes())
    for key, expected in {
        "profiles": baseline["profiles"],
        "stage_features": baseline["stage_features"],
        "chip_stage_features": baseline["chip_stage_features"],
        "minimum_available_disk_bytes_before_native_phase": MIN_FREE_BYTES,
        "pow_bits_required": 26,
        "selection_policy": "Automatic lowering disabled; local pinned-stack prediction only",
        "process_wrapper": "fresh prover and native verifier OS processes per trial; Python perf_counter; native runtime timers recorded separately",
        "native_build_mode": "zig build install -Doptimize=ReleaseFast -Ds31-version=1 -Ds31-fri-fold-step=1; fresh package paths and native prover/verifier processes",
    }.items():
        if protocol.get(key) != expected:
            raise ValueError(f"V8r1 frozen protocol changed {key}")
    anchor = committed_anchor(PROTOCOL_ANCHOR, anchor_commit,
                              "s31-whole-prover-v8r1-protocol-freeze")
    require_committed(PROTOCOL, anchor_commit)
    for key, value in {
        "protocol_sha256": expected_sha,
        "source_base_commit": protocol["source_base_commit"],
        "engine_gitlink_commit": protocol["engine_gitlink_commit"],
        "compiler_sha256": protocol["compiler_sha256"],
        "measurement_tool_sha256": protocol["measurement_tool_sha256"],
    }.items():
        if anchor.get(key) != value:
            raise ValueError(f"protocol anchor changed {key}")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       protocol["source_base_commit"], "HEAD"], check=False).returncode:
        raise ValueError("source base is not an ancestor")
    require_clean_sources()
    require_historical_evidence()
    if (protocol["measurement_tool_paths"] != [relative(path) for path in tool_paths()] or
        protocol["measurement_tool_sha256"] != tool_digest(tool_paths()) or
        protocol["prospective_design_sha256"] != s31.file_hash(v8r1_design.DESIGN) or
        protocol["v7r1_protocol_sha256"] != s31.file_hash(v8r1_design.V7R1_PROTOCOL) or
        protocol["v7r1_audit_sha256"] != s31.file_hash(v8r1_design.V7R1_AUDIT) or
        protocol["v8_protocol_sha256"] != s31.file_hash(v8r1_design.V8_PROTOCOL) or
        protocol["v8_fit_failure_sha256"] != s31.file_hash(v8r1_design.V8_FAILURE) or
        protocol["v6_audit_sha256"] != s31.file_hash(V6_AUDIT) or
        protocol["transfer_protocol_sha256"] != s31.file_hash(TRANSFER_PROTOCOL) or
        protocol["compiler_sha256"] != s31.compiler_fingerprint() or
        protocol["engine_gitlink_commit"] != git("rev-parse", "HEAD:deps/stwo-zig") or
        (enforce_host and protocol["host"] != host_identity()) or
        protocol["samples_per_program"] != SAMPLES or
        protocol["accuracy_gate"] != GATES or protocol["splits"] != SPLITS or
        protocol["profile_by_family"] != PROFILE_BY_FAMILY or
        protocol["visible_fri"] != VISIBLE_FRI):
        raise ValueError("frozen V8r1 source, host, workload, or gate pin differs")
    if output is not None and inventory(output, protocol) != protocol["inventory"]:
        raise ValueError("generated V8r1 source or assignment bytes differ from freeze")
    return protocol


def require_model(model_path: Path, expected_sha: str, model_anchor_commit: str,
                  protocol_sha: str, protocol_anchor_commit: str) -> dict:
    if model_path.resolve() != MODEL.resolve():
        raise ValueError("V8r1 model must be the committed canonical model artifact")
    if HEX64.fullmatch(expected_sha or "") is None or s31.file_hash(model_path) != expected_sha:
        raise ValueError("full externally recorded model SHA is required")
    if (model_anchor_commit == protocol_anchor_commit or
        subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                        protocol_anchor_commit, model_anchor_commit], check=False).returncode):
        raise ValueError("model anchor must descend the protocol anchor")
    anchor = committed_anchor(MODEL_ANCHOR, model_anchor_commit,
                              "s31-whole-prover-v8r1-model-freeze")
    require_committed(MODEL, model_anchor_commit)
    model = json.loads(model_path.read_bytes())
    for key, value in {"protocol_sha256": protocol_sha,
                       "frozen_model_sha256": expected_sha,
                       "training_corpus_sha256": model.get("training_corpus_sha256")}.items():
        if anchor.get(key) != value:
            raise ValueError(f"model anchor changed {key}")
    if (model.get("schema") != "s31-whole-prover-cost-model-v8r1" or
        model.get("rss_uncertainty") != RSS_UNCERTAINTY or
        model.get("automatic_lowering_selection_enabled") is not False or
        set(model.get("families", {})) != set(PROFILE_BY_FAMILY) or
        any(policy.get("prover_peak_rss_bytes", {}).get("fixed_absolute_floor_bytes") !=
            RSS_UNCERTAINTY["fixed_absolute_floor_bytes"] or
            policy.get("prover_peak_rss_bytes", {}).get("interval_kind") !=
            "v8r1_max_absolute_relative_training_loo_with_fixed_floor"
            for policy in model["families"].values())):
        raise ValueError("wrong V8r1 model")
    return model


def write_anchor(kind: str, model: Path | None = None) -> str:
    """Prepare an anchor file; it is effective only after commit and external record."""
    path = PROTOCOL_ANCHOR if kind == "protocol" else MODEL_ANCHOR
    if path.exists():
        raise ValueError("anchor already exists")
    require_committed(PROTOCOL)
    protocol = json.loads(PROTOCOL.read_bytes())
    anchor = {"schema": f"s31-whole-prover-v8r1-{kind}-freeze",
              "recorded_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
              "protocol_sha256": s31.file_hash(PROTOCOL)}
    if kind == "protocol":
        anchor.update({key: protocol[key] for key in
                       ("source_base_commit", "engine_gitlink_commit", "compiler_sha256",
                        "measurement_tool_sha256")})
    else:
        if model is None or model.resolve() != MODEL.resolve() or not model.is_file():
            raise ValueError("model anchor needs the canonical serialized model")
        require_committed(MODEL)
        frozen = json.loads(model.read_bytes())
        anchor.update({"frozen_model_sha256": s31.file_hash(model),
                       "training_corpus_sha256": frozen["training_corpus_sha256"]})
    s31.write_json(path, anchor)
    return s31.file_hash(path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    command = parser.add_subparsers(dest="command", required=True)
    prepare = command.add_parser("draft")
    prepare.add_argument("--out", type=Path, required=True)
    anchor = command.add_parser("anchor")
    anchor.add_argument("kind", choices=("protocol", "model"))
    anchor.add_argument("--model", type=Path)
    args = parser.parse_args()
    if args.command == "draft":
        print(f"V8r1 draft protocol SHA-256: {draft(args.out.resolve())}")
    else:
        print(f"V8r1 {args.kind} anchor SHA-256: {write_anchor(args.kind, args.model)}")


if __name__ == "__main__":
    main()
