"""Prospective, source-identical paired lowering roster (no native execution)."""

from __future__ import annotations

import json
import platform
import random
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

import design  # noqa: E402
from abi.binding_v2 import statement_from_assignment  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import compiler_fingerprint  # noqa: E402

PROTOCOL = ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-protocol.json"
CASES = tuple(design.SPECS)
SCORED = 12
PIN_PATHS = (
    "src/frontends/s31/build.zig",
    "src/frontends/s31/language/relation.zig",
    "src/frontends/s31/language/relation_compiler.zig",
    "src/frontends/s31/language/bounded_call_admission.zig",
    "src/frontends/s31/runtime/mvp_runtime.zig",
    "src/frontends/s31/runtime/mvp_verifier_main.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_package.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_verifier_main.zig",
    "src/frontends/s31/runtime/bounded_compiled_binding.zig",
    "src/frontends/s31/runtime/mixed_boundary/inspection.zig",
    "src/frontends/s31/python/abi/binding_v2.py",
    "src/frontends/s31/python/oracle.py",
    "src/frontends/s31/examples/boundary/record_mixed1.s31.json",
    "src/frontends/s31/benchmarks/paired_mixed_vs_direct/design.py",
    "src/frontends/s31/benchmarks/paired_mixed_vs_direct/protocol.py",
    "src/frontends/s31/benchmarks/paired_mixed_vs_direct/study.py",
    "src/frontends/s31/benchmarks/paired_mixed_vs_direct/audit.py",
)


def source_and_claims(case: str) -> dict:
    raw = design.source(case)
    source = json.loads(raw)
    semantic = {**source, "version": 1}
    semantic.pop("public_abi")
    claims = []
    for index in range(SCORED + 1):
        assignment = design.assignment(case, index)
        parsed = json.loads(assignment)
        if evaluate_relation(semantic, parsed) != parsed["public_outputs"]:
            raise ValueError("independent evaluator differs from arithmetic oracle")
        statement = statement_from_assignment(source, parsed)
        claims.append({"index": index, "assignment_sha256": design.digest(assignment),
                       "statement_sha256": design.digest(statement)})
    _, calls, rounds = design.spec(case)
    return {"source_sha256": design.digest(raw), "calls": calls,
            "rounds": rounds, "claims": claims}


def schedule() -> list[dict]:
    rng = random.Random(2026101209)
    result = []
    for case in CASES:
        order = [["direct", "mixed"]] * (SCORED // 2) + [
            ["mixed", "direct"]] * (SCORED // 2)
        rng.shuffle(order)
        result.extend({"case": case, "index": index, "order": order[index - 1]}
                      for index in range(1, SCORED + 1))
    rng.shuffle(result)
    return result


def current() -> dict:
    return {
        "schema": "s31-paired-mixed-vs-direct-v1-protocol",
        "status": "pre-native-frozen",
        "source_version": 2,
        "source_shape": "public four-lane M31 input; 16- or 1024-round square/add calls; derived public four-lane output",
        "profiles": {"direct": "direct-gate", "mixed": "direct-mixed-general"},
        "direct_prover_command": "prove-for-external-verification",
        "mixed_prover_command": "source-pinned v2 assignment/proof/emitted/supplied-statement",
        "external_verifier_required": True,
        "build_mode": "ReleaseFast",
        "native_process_timeout_seconds": 120,
        "native_build_timeout_seconds": 600,
        "mixed_native_phase_timing_enabled": True,
        "build_processes_are_not_scored": True,
        "warmup_index_per_source_and_profile": 0,
        "scored_pairs_per_source": SCORED,
        "measurements": ["fresh prover process wall", "fresh external verifier process wall",
                         "proof bytes", "prover peak RSS", "verifier peak RSS",
                         "diagnostic wall minus native-reported interaction and FRI PoW"],
        "negative_control": "increment first result M31 word; require native verifier rejection",
        "proof_order": schedule(),
        "roster": {case: source_and_claims(case) for case in CASES},
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(),
                 "zig": subprocess.check_output(("zig", "version"), text=True).strip()},
        "compiler_sha256": compiler_fingerprint(),
        "engine_gitlink_commit": subprocess.check_output(
            ("git", "rev-parse", "HEAD:deps/stwo-zig"), cwd=ROOT, text=True).strip(),
        "pin_sha256": {path: design.digest((ROOT / path).read_bytes()) for path in PIN_PATHS},
    }


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    expected = design.canonical(current())
    if raw != expected:
        raise ValueError("paired protocol or source/compiler/host pins differ from committed freeze")
    return json.loads(raw), design.digest(raw)


def main() -> None:
    if PROTOCOL.exists():
        raise FileExistsError("prospective protocol already exists")
    PROTOCOL.parent.mkdir(parents=True, exist_ok=True)
    raw = design.canonical(current())
    PROTOCOL.write_bytes(raw)
    print(PROTOCOL, design.digest(raw))


if __name__ == "__main__":
    main()
