#!/usr/bin/env python3
"""Extract source-bound PCS/FRI geometry from one locally trusted leaf package.

This is a P01 diagnostic, never a soundness certificate. Package verification
checks internal artifact consistency; it does not authenticate executable
provenance. The tool executes the package's native verifier for check-key when
supported, so use only a locally trusted package binary. It does not modify
package artifacts. Missing theorem parameters remain null and
--require-complete always fails while they are open.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))
import s31  # noqa: E402


# Current v0.1 leaf schemas. A readable legacy key is not automatically a
# reviewed v0.1 geometry source.
SCHEMAS = {
    "gate": {("s31-verification-key-gate-roster-v1", "circuit-v1")},
    "chip": {("s31-verification-key-v2", "hybrid-step-v2")},
    "sparse-gate": {("s31-verification-key-sparse-roster-v1", "sparse-v3")},
    "sparse-chip": {("s31-verification-key-v3", "sparse-v3")},
    "sparse-wide-gate": {("s31-verification-key-v5", "sparse-wide-v5")},
    "direct-gate": {
        ("s31-verification-key-direct-manifest-v2", "direct-m31-v4"),
        ("s31-verification-key-direct-record-v2", "direct-m31-v4"),
    },
    "direct-chip": {
        ("s31-verification-key-direct-chip-manifest-v2", "direct-m31-v4"),
        ("s31-verification-key-direct-record-chip-v2", "direct-m31-v4"),
    },
    "sha-joint": {("s31-verification-key-sha-joint-v1", "sha-joint-v1")},
    "sha-shift": {("s31-verification-key-sha-shift-v3", "sha-shift-v3")},
    "sha-fused": {("s31-verification-key-sha-fused-v4", "sha-fused-v4")},
}
SOURCE_FILES = (
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/sha/package/sha_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_shift_package_runtime.zig",
    "src/frontends/s31/sha/package/sha_fused_package_runtime.zig",
    "deps/stwo-zig/src/core/pcs/config_v2.zig",
)


def uint(value: object, label: str, *, maximum: int = 30, minimum: int = 0) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f"invalid {label}")
    return value


def object_field(value: object, label: str) -> dict:
    if not isinstance(value, dict):
        raise ValueError(f"missing {label}")
    return value


def check_source_texts(sources: dict[str, str]) -> None:
    generic = sources[SOURCE_FILES[0]]
    config = sources[SOURCE_FILES[-1]]
    if any(text.count(token) != 1 for text, token in (
            (generic, "FriConfigV2.init(26, 0, 1, 70, fri_fold_step), trace_log_size)"),
            (generic, "if (key.trace_log_size != expected_trace_log or"),
            (config, "return fromFriAndLiftingSize(config, trace_log_size + config.log_blowup_factor);"),
            (config, "self.trace_lifting_log_size,"),
            (config, "split_composition_log_degree_bound + self.fri_config.log_blowup_factor,"))):
        raise ValueError("generic PCS geometry source changed")
    for name, minimum in zip(SOURCE_FILES[1:4], (18, 16, 16), strict=True):
        text = sources[name]
        if any(text.count(token) != 1 for token in (
                "FriConfigV2.init(26, 0, 1, 70, 1)",
                f"PcsConfigV2.fromFriAndTraceSize(fri, @max(trace_log, {minimum}))",
                f"key.trace_log_size != @max(topo.pp.traceLogSize(), {minimum})")):
            raise ValueError(f"SHA PCS geometry source changed: {name}")


def source_binding(root: Path = ROOT) -> dict[str, object]:
    engine_commit = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()
    engine = root / "deps/stwo-zig"
    checked_out = subprocess.check_output(
        ["git", "-C", str(engine), "rev-parse", "HEAD"], text=True
    ).strip()
    if checked_out != engine_commit:
        raise ValueError("engine checkout differs from the S31 gitlink")
    sources = {name: (root / name).read_text() for name in SOURCE_FILES}
    check_source_texts(sources)
    return {
        "engine_gitlink": engine_commit,
        "source_sha256": {name: hashlib.sha256(text.encode()).hexdigest()
                          for name, text in sources.items()},
    }


def component_rows(rows: object, blowup_log: int, max_log: int) -> list[dict[str, object]]:
    if not isinstance(rows, list) or not rows:
        raise ValueError("component roster is empty")
    result = []
    names: set[str] = set()
    for index, row in enumerate(rows):
        item = object_field(row, f"component {index}")
        name = item.get("name")
        if not isinstance(name, str) or not name or name in names:
            raise ValueError("invalid or duplicate component name")
        names.add(name)
        log = uint(item.get("trace_log_size"), f"{name} trace log")
        if log > max_log:
            raise ValueError("component exceeds key's maximum trace log")
        extended_log = log + blowup_log
        if extended_log > 31:
            raise ValueError("component extended domain is too large")
        declared = item.get("evaluation_log_size")
        if declared is not None and uint(declared, f"{name} evaluation log", maximum=31) != extended_log:
            raise ValueError("component evaluation log differs from trace log and blowup")
        proof_index = uint(item.get("proof_index"), f"{name} proof index", maximum=100000)
        if proof_index != index:
            raise ValueError("component proof order is incomplete")
        result.append({"name": name, "proof_index": index,
                       "trace_log_size": log, "trace_rows": 1 << log,
                       "configured_extended_log_size": extended_log,
                       "configured_extended_rows": 1 << extended_log})
    return result


def fixed_column_rows(rows: object, max_log: int) -> list[dict[str, object]]:
    if not isinstance(rows, list) or not rows:
        raise ValueError("preprocessed column roster is empty")
    result = []
    names: set[str] = set()
    for index, row in enumerate(rows):
        item = object_field(row, f"preprocessed column {index}")
        name = item.get("id")
        if not isinstance(name, str) or not name or name in names:
            raise ValueError("invalid or duplicate preprocessed column ID")
        names.add(name)
        log = uint(item.get("log_size"), f"{name} fixed-column log")
        row_count = uint(item.get("rows"), f"{name} fixed-column rows",
                         maximum=1 << 30, minimum=1)
        if (log > max_log or row_count != 1 << log or
                uint(item.get("commitment_index"), f"{name} commitment index", maximum=100000) != index):
            raise ValueError("preprocessed column domain or order differs")
        result.append({"id": name, "commitment_index": index,
                       "log_size": log, "rows": 1 << log})
    return result


def extract_fields(manifest: dict, key: dict, roster: dict | None = None) -> dict[str, object]:
    """Pure shape extractor. The CLI calls this only after package and key checks."""
    if manifest.get("schema") != "s31-package-v1":
        raise ValueError("unsupported package schema")
    lowering = manifest.get("lowering")
    if lowering not in SCHEMAS or (key.get("schema"), key.get("profile")) not in SCHEMAS[lowering]:
        raise ValueError("unreviewed lowering, key schema, or profile")
    step = uint(manifest.get("fri_fold_step"), "manifest fold step", maximum=4, minimum=1)
    if step not in (1, 4) or (step == 4 and lowering not in {"gate", "sparse-wide-gate"}):
        raise ValueError("unreviewed FRI fold step")
    trace_log = uint(key.get("trace_log_size"), "key trace log")
    fri = object_field(key.get("fri"), "FRI key")
    if set(fri) != {"pow_bits", "log_blowup_factor", "last_layer_degree_bound", "queries", "fold_step"}:
        raise ValueError("FRI key fields changed")
    pow_bits = uint(fri["pow_bits"], "PoW bits", maximum=31)
    blowup_log = uint(fri["log_blowup_factor"], "blowup log", maximum=30, minimum=1)
    last_degree = uint(fri["last_layer_degree_bound"], "last layer degree", maximum=1, minimum=1)
    queries = uint(fri["queries"], "query count", maximum=100000, minimum=1)
    fri_step = uint(fri["fold_step"], "FRI key fold step", maximum=4, minimum=1)
    if ((pow_bits, blowup_log, last_degree, queries, fri_step) !=
            (26, 1, 1, 70, step)):
        raise ValueError("FRI key differs from the pinned native tuple")
    lifting_log = trace_log + blowup_log
    if lifting_log > 31:
        raise ValueError("configured lifting domain is too large")

    components: list[dict[str, object]] = []
    fixed_columns: list[dict[str, object]] = []
    missing_geometry: list[str] = []
    partial: dict[str, object] = {}
    if lowering in {"gate", "sparse-gate"}:
        parsed = object_field(roster, "component roster")
        expected = "s31-component-roster-gate-v1" if lowering == "gate" else "s31-component-roster-sparse-gate-v1"
        if parsed.get("schema") != expected:
            raise ValueError("component roster schema changed")
        components = component_rows(parsed.get("components"), blowup_log, trace_log)
        fixed_columns = fixed_column_rows(parsed.get("preprocessed_columns"), trace_log)
        count = 11 if lowering == "gate" else 3
        if len(components) != count:
            raise ValueError("component roster count changed")
    elif lowering in {"direct-gate", "direct-chip"}:
        parsed = object_field(key.get("component_manifest"), "direct component manifest")
        if roster is not None and roster != parsed:
            raise ValueError("direct manifest artifact differs from key")
        components = component_rows(parsed.get("components"), blowup_log, trace_log)
        fixed_columns = fixed_column_rows(parsed.get("preprocessed_columns"), trace_log)
        if len(components) != (1 if lowering == "direct-gate" else 2):
            raise ValueError("direct component count changed")
    elif lowering.startswith("sha-"):
        metadata = object_field(key.get(lowering.replace("-", "_")), "SHA metadata")
        logs = metadata.get("circuit_logs")
        if not isinstance(logs, list) or len(logs) != 4:
            raise ValueError("SHA circuit logs changed")
        partial["sha_circuit_logs"] = [uint(v, "SHA circuit log") for v in logs]
        if any(log > trace_log for log in partial["sha_circuit_logs"]):
            raise ValueError("SHA circuit component exceeds key trace log")
        missing_geometry.append("full SHA component-name-to-domain roster")
        missing_geometry.append("preprocessed column domain roster")
    else:
        missing_geometry.append("per-component trace-domain roster")
        missing_geometry.append("preprocessed column domain roster")

    missing_theorem = [
        "split composition log-degree bound and resulting final FRI input domain D",
        "per-component constraint degree and theorem C/d/L/m/rate/list-bound identification",
        "finite-domain and small-table precondition discharge",
        "verified-oracle equality and native-to-published-IOP refinement",
    ]
    return {
        "schema": "s31-pcs-fri-package-geometry-v1", "status": "incomplete",
        "proven_release_admissible": False, "native_proven_security_bits": None,
        "lowering": lowering, "key_schema": key["schema"], "profile": key["profile"],
        "candidate_N_trace_rows": 1 << trace_log, "max_trace_log_size": trace_log,
        "blowup_factor": 1 << blowup_log, "configured_trace_lifting_log_size": lifting_log,
        "configured_trace_lifting_rows": 1 << lifting_log,
        "fri": {"pow_bits": pow_bits, "log_blowup_factor": blowup_log,
                "last_layer_degree_bound": last_degree, "raw_queries": queries,
                "fold_step": step},
        "components": components, "preprocessed_columns": fixed_columns,
        "partial_component_metadata": partial,
        "component_roster_complete": not missing_geometry,
        "theorem_inputs": {"D_final_fri_domain": None, "C": None, "d": None,
                           "L": None, "m": None, "rate": None, "list_bound": None},
        "missing_package_geometry": missing_geometry,
        "missing_theorem_inputs": missing_theorem,
    }


def extract_package(package: Path, root: Path = ROOT) -> dict[str, object]:
    binding = source_binding(root)
    manifest = s31.verify_package(package)
    key_path = package / "verification-key.json"
    key = json.loads(key_path.read_text())
    lowering = manifest["lowering"]
    native_key_check = "no-standalone-SHA-check-key"
    if not lowering.startswith("sha-"):
        verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        result = subprocess.run([str(verifier), "check-key", str(key_path)],
                                capture_output=True, text=True, timeout=20, check=False)
        if result.returncode == 0:
            native_key_check = "accepted"
        elif "error: InvalidArguments" in result.stderr:
            # Older sealed binaries can be readable by the current package
            # verifier without implementing this later diagnostic command.
            native_key_check = "unsupported-by-installed-verifier"
        else:
            raise ValueError(f"package's native verifier rejected its key: {result.stderr.strip()[:200]}")
    roster_name = ({"gate": "gate-component-roster.json",
                    "sparse-gate": "sparse-component-roster.json",
                    "direct-gate": "component-manifest.json",
                    "direct-chip": "component-manifest.json"}.get(lowering))
    roster = json.loads((package / roster_name).read_text()) if roster_name else None
    report = extract_fields(manifest, key, roster)
    report["package_checks"] = {"manifest_artifacts": "verified",
                                "native_check_key": native_key_check,
                                "package_manifest_sha256": hashlib.sha256((package / "manifest.json").read_bytes()).hexdigest(),
                                "verification_key_sha256": hashlib.sha256(key_path.read_bytes()).hexdigest()}
    report["missing_native_binding"] = ([] if native_key_check == "accepted" else
                                         ["installed verifier lacks a standalone sealed-key reconstruction check"])
    report["source_binding"] = binding
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path, help="sealed leaf package directory")
    parser.add_argument("--require-complete", action="store_true",
                        help="exit 2 while any P01 theorem input remains open")
    args = parser.parse_args(argv)
    try:
        report = extract_package(args.package.resolve())
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as exc:
        print(f"PCS/FRI package geometry rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_complete else 0


if __name__ == "__main__":
    raise SystemExit(main())
