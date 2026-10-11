"""Declare S31 commands and their typed command-line arguments."""

from __future__ import annotations

import argparse
from pathlib import Path


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="s31", description="S31 circuit relation compiler")
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("check", "inspect", "explain", "equations", "run"):
        help_text = {
            "explain": "show canonical nodes, source positions, and builder gate counts",
            "equations": "show source-level field equations (not expanded AIR terms)",
        }.get(command)
        sub = commands.add_parser(command, help=help_text)
        sub.add_argument("source_or_package", type=Path)
        if command == "run":
            sub.add_argument("assignment", type=Path)
    sub = commands.add_parser("build")
    sub.add_argument("source", type=Path)
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"), default="gate")
    sub.add_argument("--fri-fold-step", type=int, choices=(1, 4), default=1,
                     help="FRI folds per commitment for gate or sparse-wide-gate proofs; 4 can shrink recursive verifier circuits")
    sub = commands.add_parser("trial", help="build, prove, verify, and record one trial")
    sub.add_argument("source_or_package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"))
    sub.add_argument("--fri-fold-step", type=int, choices=(1, 4),
                     help="select a gate or sparse-wide-gate package's FRI schedule, or check a supplied package")
    sub = commands.add_parser("tune", help="compare verified proof profiles on one source and assignment corpus")
    sub.add_argument("source", type=Path)
    sub.add_argument("assignments", type=Path, nargs="+")
    sub.add_argument("--warmup", type=Path, help="valid assignment proved once per profile before measurement")
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", action="append", required=True,
                     choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"))
    sub = commands.add_parser("oracle", help="check normalized relation values without building a proof")
    sub.add_argument("source_or_package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub = commands.add_parser("lower", help="lower .s31 text to normalized relation JSON")
    sub.add_argument("source", type=Path)
    sub.add_argument("--out", type=Path)
    sub = commands.add_parser("source-layout", help="show nominal records, flat leaves, and source erasure digest")
    sub.add_argument("source", type=Path)
    sub = commands.add_parser("prove")
    sub.add_argument("package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub.add_argument("proof", type=Path)
    sub = commands.add_parser("wrap", help="prove verification of a saved gate or sparse-wide S31 proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--low-memory", action="store_true",
                     help="retain committed evaluations only; lower peak RAM with some extra proving time")
    sub = commands.add_parser("wrap-next", help="prove verification of an already recursive S31 proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--low-memory", action="store_true")
    for command, description in (
        ("fold-base", "start a fixed-key fold from a first-level recursive proof"),
        ("fold-next", "extend a fixed-key fold under the same verification key"),
        ("state-fold-base", "start a state-transition fold from a first-level recursive proof"),
        ("state-fold-next", "prove one more source recurrence step under the same key"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("child_proof", type=Path)
        sub.add_argument("outer_proof", type=Path)
        sub.add_argument("--statement", type=Path)
        sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("fold-advance", help="prove several fixed-key folds while reusing the sealed AIR")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--steps", type=int, required=True)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--checkpoint-dir", type=Path, help="keep intermediate proofs for resume")
    sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("state-fold-advance", help="prove several source steps, with optional resumable checkpoints")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--steps", type=int, required=True,
                     help="number of new fold proofs; the first starts at step zero for a recursive base proof")
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--checkpoint-dir", type=Path,
                     help="keep each intermediate proof and statement for resume")
    sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("audit-recursive", help="audit a saved child proof's in-circuit verifier inputs")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("audit-recursive-next", help="audit the in-circuit verifier for a recursive child proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    for command, description in (
        ("audit-fold-base", "challenge a fixed-key fold's base circuit inputs"),
        ("audit-fold-next", "challenge a fixed-key fold's recursive circuit inputs"),
        ("audit-state-fold-base", "challenge a state fold's base circuit and counter"),
        ("audit-state-fold-next", "challenge a state fold's transition and recursive verifier"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("child_proof", type=Path)
        sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("inspect-record-proof",
                              help="verify a v2 proof against the supplied package and display its named claim")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("inspect-record-proof-pinned",
                              help="verify and display a v2 public record claim under externally supplied package digests")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    for kind in ("source", "key", "prover", "verifier"):
        sub.add_argument(f"--{kind}-sha256", required=True)
    sub.add_argument("--text-sha256", help="required when the package contains source.s31")
    sub = commands.add_parser("verify-pinned", help="verify a proof only after external package digest admission")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    for kind in ("source", "key", "prover", "verifier"):
        sub.add_argument(f"--{kind}-sha256", required=True)
    sub.add_argument("--text-sha256", help="required when the package contains source.s31")
    sub = commands.add_parser("verify-recursive", help="verify an outer proof against its embedded child key")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify-recursive-next", help="verify a two-level recursive chain")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify-fold", help="verify a fixed-key fold using only its top proof and statement")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--max-step", type=int, help="reject a top fold statement above this locally trusted recursion depth")
    sub = commands.add_parser("verify-state-fold", help="verify a recursive state-transition proof from its top proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--max-step", type=int, help="reject a top fold statement above this locally trusted recursion depth")
    for command, description in (
        ("audit-fold-chain", "verify every fixed-fold checkpoint and its public claim continuity"),
        ("audit-state-fold-chain", "verify every state-fold checkpoint and replay its source transition"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("proofs", type=Path, nargs="+", help="fold proofs from step zero through the top step")
        sub.add_argument("--max-step", type=int)
    sub = commands.add_parser("inspect-fold", help="rebuild and report a sealed fold AIR's raw rows and padding headroom")
    sub.add_argument("package", type=Path)
    sub.add_argument("--step", type=int, default=0, help="rebuild the witness-free AIR at this u32 counter value")
    sub = commands.add_parser("inspect-state-fold", help="rebuild and report a state-fold AIR's raw rows and padding headroom")
    sub.add_argument("package", type=Path)
    sub.add_argument("--step", type=int, default=0, help="rebuild the witness-free AIR at this u32 counter value")
    return parser
