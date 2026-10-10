#!/usr/bin/env python3
"""S31 v0.1 command-line frontend and stable Python API."""

import sys
from pathlib import Path
S31_SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

import argparse
import json
import tempfile

from package.build import build, build_json, build_text, package_for
from package.context import (
    AIR_BUNDLE_SHA256, BUILD_FILE, ENGINE_ROOT, LIBRARY_SOURCE_FILES,
    PINNED_ASSETS, PROJECTION_SHA256, ROOT, S31_DIR, TEXT_FRONTEND_SOURCES,
    abi, compiler_fingerprint, file_hash, invoke, load_source, lower_text,
    sha256, standard_library_lock, text_interface, write_json,
)
from package.verify import verify_package
from runtime.folds import audit_fold_chain, replay_state_step
from runtime.trials import (
    assignment_digest, independent_value_check, oracle_provenance,
    prover_stages, trial, tune, visible_fri,
)


def explain(package: Path) -> dict:
    from inspection.reports import explain as inspect_explain

    return inspect_explain(package, verify_package)


def equations(package: Path) -> dict:
    from inspection.reports import equations as inspect_equations

    return inspect_equations(package, verify_package)


def main() -> None:
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
    args = parser.parse_args()

    if args.command == "lower":
        if args.source.suffix != ".s31":
            raise ValueError("lower expects a .s31 text file")
        _, normalized, _ = lower_text(args.source)
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_bytes(normalized)
            print(args.out)
        else:
            sys.stdout.buffer.write(normalized)
        return
    if args.command == "build":
        print(build(args.source, args.out, args.lowering, args.fri_fold_step))
        return
    if args.command == "trial":
        print(json.dumps(trial(args.source_or_package, args.assignment, args.out,
                               args.lowering, args.fri_fold_step),
                         indent=2, sort_keys=True))
        return
    if args.command == "tune":
        print(json.dumps(tune(args.source, args.assignments, args.out, args.lowering,
                              args.warmup),
                         indent=2, sort_keys=True))
        return
    if args.command == "oracle":
        if args.source_or_package.is_dir():
            package = args.source_or_package.resolve()
            verify_package(package)
            relation = json.loads((package / "source.s31.json").read_text())
        elif args.source_or_package.suffix == ".s31":
            relation, _, _ = lower_text(args.source_or_package.resolve())
        else:
            relation, _ = load_source(args.source_or_package.resolve())
        result = independent_value_check(relation, json.loads(args.assignment.read_text()))
        if result["status"] != "passed":
            raise ValueError(result["reason"])
        print(json.dumps({"schema": "s31-oracle-v1", "program": relation["name"], **result},
                         indent=2, sort_keys=True))
        return
    if args.command == "explain":
        print(json.dumps(explain(package_for(args.source_or_package)), indent=2, sort_keys=True))
        return
    if args.command == "equations":
        print(json.dumps(equations(package_for(args.source_or_package)), indent=2, sort_keys=True))
        return
    if args.command in ("check", "inspect", "run"):
        package = package_for(args.source_or_package)
        manifest = verify_package(package)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        extra = (str(args.assignment.resolve()),) if args.command == "run" else ()
        print(invoke(str(executable), args.command, *extra), end="")
        return

    package = args.package.resolve()
    manifest = verify_package(package)
    if args.command == "prove":
        assignment = json.loads(args.assignment.read_text())
        statement = {
            "public_inputs": assignment["public_inputs"],
            "public_outputs": assignment["public_outputs"],
        }
        proof = args.proof.resolve()
        proof.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "prove", str(args.assignment.resolve()), str(proof)), end="")
        statement_path = Path(str(proof) + ".statement.json")
        write_json(statement_path, statement)
        print(f"public statement: {statement_path}")
    elif args.command == "wrap":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("wrap requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = "recurse-wide-wrap" if manifest["lowering"] == "sparse-wide-gate" else "recurse-wrap"
        print(invoke(str(executable), command, str(child), str(statement),
                     str(outer), str(package / "verification-key.json"),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"recursive statement: {outer}.statement.json")
    elif args.command == "wrap-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("wrap-next requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "recurse-wrap-next", str(child), str(statement),
                     str(outer), str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     str(package / "recursive-verification-key-level2.json"),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"recursive chain statement: {outer}.statement.json")
    elif args.command in ("fold-base", "fold-next", "state-fold-base", "state-fold-next"):
        wide_fold = manifest["lowering"] == "sparse-wide-gate" and args.command in ("fold-base", "fold-next")
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError(f"{args.command} requires a gate or supported sparse-wide package")
        if args.command.startswith("state-fold-") and "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("source does not expose a supported typed recurrence step")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = {
            "fold-base": "fold-wrap-base",
            "fold-next": "fold-wrap-next",
            "state-fold-base": "state-fold-wrap-base",
            "state-fold-next": "state-fold-wrap-next",
        }[args.command]
        if wide_fold:
            command = "wide-" + command
        key_name = ("state-fold-verification-key.json" if args.command.startswith("state-fold-")
                    else "fixed-fold-verification-key.json")
        print(invoke(str(executable), command, str(child), str(statement), str(outer),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / key_name),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"fold statement: {outer}.statement.json")
    elif args.command == "fold-advance":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"} or "s31-fixed-fold-batch-v1" not in manifest.get("capabilities", []):
            raise ValueError("fold-advance requires a package with the fixed-fold batch capability")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        if child == outer or args.steps < 1 or args.steps > 65536:
            raise ValueError("fold-advance needs a distinct output and 1..65536 steps")
        wide_fold = manifest["lowering"] == "sparse-wide-gate"
        initial = json.loads(statement.read_text())
        base_schema = "s31-recursive-chain-statement-v1" if wide_fold else "s31-recursive-gate-statement-v2"
        fold_schema = "s31-fixed-fold-statement-v4" if wide_fold else "s31-fixed-fold-statement-v3"
        if initial.get("schema") == base_schema:
            first_step = 0
            base_case = True
        elif initial.get("schema") == fold_schema:
            prior_step = initial.get("step")
            if type(prior_step) is not int or prior_step < 0 or prior_step > 0xffffffff:
                raise ValueError("input fixed-fold statement has an invalid step counter")
            first_step = prior_step + 1
            base_case = False
        else:
            raise ValueError("input must be a recursive base or fixed-fold proof")
        if first_step + args.steps - 1 > 0xffffffff:
            raise ValueError("fixed-fold step counter would overflow")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        outer.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="s31-fixed-fold-advance-") as temporary:
            checkpoints = args.checkpoint_dir.resolve() if args.checkpoint_dir else Path(temporary)
            checkpoints.mkdir(parents=True, exist_ok=True)
            planned_paths: set[Path] = set()
            for index in range(args.steps):
                step = first_step + index
                target = outer if index == args.steps - 1 else checkpoints / f"fold-{step:05d}.proof"
                target_statement = Path(str(target) + ".statement.json")
                if target in planned_paths or target_statement in planned_paths or target in {child, statement} or target_statement in {child, statement}:
                    raise ValueError(f"fold batch paths collide: {target}")
                planned_paths.update((target, target_statement))
                if target.exists() or target_statement.exists():
                    raise ValueError(f"refusing to overwrite fold proof or statement: {target}")
            print(invoke(str(executable), "wide-fold-wrap-batch" if wide_fold else "fold-wrap-batch",
                         str(child), str(statement), str(outer),
                         str(package / "verification-key.json"),
                         str(package / "recursive-verification-key.json"),
                         *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                         str(package / "fixed-fold-verification-key.json"),
                         str(args.steps), str(checkpoints), str(first_step),
                         "base" if base_case else "next",
                         *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"fold statement: {outer}.statement.json")
    elif args.command == "state-fold-advance":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("state-fold-advance requires a supported gate-profile recurrence package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        if child == outer or args.steps < 1:
            raise ValueError("state-fold-advance needs a distinct output and at least one step")
        if args.steps > 65536:
            raise ValueError("state-fold-advance accepts at most 65536 proofs per batch; resume from a checkpoint")
        state_key = json.loads((package / "state-fold-verification-key.json").read_text())
        new_counter = state_key["schema"] == "s31-state-fold-verification-key-v3"
        expected_statement = "s31-state-fold-statement-v2" if new_counter else "s31-state-fold-statement-v1"
        counter_max = (1 << 32) - 1 if new_counter else 65535
        initial = json.loads(statement.read_text())
        if initial.get("schema") == "s31-recursive-gate-statement-v2":
            first_step = 0
            base_case = True
        elif initial.get("schema") == expected_statement:
            prior_step = initial.get("step")
            if type(prior_step) is not int or prior_step < 0 or prior_step > counter_max:
                raise ValueError("input state-fold statement has an invalid step counter")
            first_step = initial["step"] + 1
            base_case = False
        else:
            raise ValueError("input must be a first-level recursive or state-fold proof")
        if first_step + args.steps - 1 > counter_max:
            raise ValueError("state-fold step counter would overflow")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        outer.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="s31-state-fold-advance-") as temporary:
            checkpoints = args.checkpoint_dir.resolve() if args.checkpoint_dir else Path(temporary)
            checkpoints.mkdir(parents=True, exist_ok=True)
            planned_paths = set()
            for index in range(args.steps):
                step = first_step + index
                target = (outer if index == args.steps - 1 else
                          checkpoints / f"state-{step:05d}.proof")
                target_statement = Path(str(target) + ".statement.json")
                if target in planned_paths or target_statement in planned_paths:
                    raise ValueError(f"state-fold batch outputs collide: {target}")
                planned_paths.update((target, target_statement))
                if target.exists() or target_statement.exists():
                    raise ValueError(f"refusing to overwrite fold proof or statement: {target}")
            batch_capability = ("s31-state-fold-batch-v2" if new_counter else "s31-state-fold-batch-v1")
            if batch_capability in manifest.get("capabilities", []):
                print(invoke(str(executable), "state-fold-wrap-batch", str(child), str(statement),
                             str(outer), str(package / "verification-key.json"),
                             str(package / "recursive-verification-key.json"),
                             str(package / "state-fold-verification-key.json"),
                             str(args.steps), str(checkpoints), str(first_step),
                             "base" if base_case else "next",
                             *(("--low-memory",) if args.low_memory else ())), end="")
                statement = Path(str(outer) + ".statement.json")
            else:
                # Old packages carry their own v1 binary, which only has the
                # one-step command. Preserve their installed proof format.
                for index in range(args.steps):
                    step = first_step + index
                    target = (outer if index == args.steps - 1 else
                              checkpoints / f"state-{step:05d}.proof")
                    target_statement = Path(str(target) + ".statement.json")
                    command = "state-fold-wrap-base" if base_case and index == 0 else "state-fold-wrap-next"
                    print(invoke(str(executable), command, str(child), str(statement), str(target),
                                 str(package / "verification-key.json"),
                                 str(package / "recursive-verification-key.json"),
                                 str(package / "state-fold-verification-key.json"),
                                 *(("--low-memory",) if args.low_memory else ())), end="")
                    child, statement = target, target_statement
            print(invoke(str(verifier), "state-fold-verify", str(outer), str(statement)), end="")
        print(f"state-fold top proof: {outer}")
    elif args.command == "audit-recursive":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("audit-recursive requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = "recurse-wide-audit" if manifest["lowering"] == "sparse-wide-gate" else "recurse-audit"
        print(invoke(str(executable), command, str(child), str(statement),
                     str(package / "verification-key.json")), end="")
    elif args.command == "audit-recursive-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("audit-recursive-next requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "recurse-audit-next", str(child), str(statement),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json")), end="")
    elif args.command in ("audit-fold-base", "audit-fold-next", "audit-state-fold-base", "audit-state-fold-next"):
        wide_fold = manifest["lowering"] == "sparse-wide-gate" and args.command in ("audit-fold-base", "audit-fold-next")
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError(f"{args.command} requires a gate or supported sparse-wide package")
        if args.command.startswith("audit-state-fold-") and "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("source does not expose a supported typed recurrence step")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = {
            "audit-fold-base": "fold-audit",
            "audit-fold-next": "fold-audit-next",
            "audit-state-fold-base": "state-fold-audit-base",
            "audit-state-fold-next": "state-fold-audit-next",
        }[args.command]
        if wide_fold:
            command = "wide-fold-audit-base" if args.command == "audit-fold-base" else "wide-fold-audit-next"
        key_name = ("state-fold-verification-key.json" if args.command.startswith("audit-state-fold-")
                    else "fixed-fold-verification-key.json")
        print(invoke(str(executable), command, str(child), str(statement),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / key_name)), end="")
    elif args.command == "verify":
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), str(proof), str(statement), str(package / "verification-key.json")), end="")
    elif args.command == "verify-recursive":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-recursive requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), "recurse-verify", str(proof), str(statement)), end="")
    elif args.command == "verify-recursive-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-recursive-next requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), "recurse-verify-next", str(proof), str(statement)), end="")
    elif args.command == "verify-fold":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-fold requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        if args.max_step is not None and not (0 <= args.max_step <= 0xffffffff):
            raise ValueError("--max-step must fit u32")
        max_step = ("--max-step", str(args.max_step)) if args.max_step is not None else ()
        print(invoke(str(executable), "fold-verify", str(proof), str(statement), *max_step), end="")
    elif args.command == "verify-state-fold":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("verify-state-fold requires a supported gate-profile recurrence package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        if args.max_step is not None and not (0 <= args.max_step <= 0xffffffff):
            raise ValueError("--max-step must fit u32")
        max_step = ("--max-step", str(args.max_step)) if args.max_step is not None else ()
        print(invoke(str(executable), "state-fold-verify", str(proof), str(statement), *max_step), end="")
    elif args.command in {"audit-fold-chain", "audit-state-fold-chain"}:
        result = audit_fold_chain(package, manifest, args.proofs,
                                  args.command == "audit-state-fold-chain", args.max_step)
        print(json.dumps(result, sort_keys=True))
    elif args.command == "inspect-fold":
        wide_fold = manifest["lowering"] == "sparse-wide-gate"
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError("inspect-fold requires a gate or sparse-wide package")
        if not 0 <= args.step <= 0xffffffff:
            raise ValueError("--step must fit u32")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "wide-fold-inspect" if wide_fold else "fold-inspect",
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / "fixed-fold-verification-key.json"), "--step", str(args.step)), end="")
    elif args.command == "inspect-state-fold":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("inspect-state-fold requires a supported gate-profile recurrence package")
        if not 0 <= args.step <= 0xffffffff:
            raise ValueError("--step must fit u32")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "state-fold-inspect",
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     str(package / "state-fold-verification-key.json"), "--step", str(args.step)), end="")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, UnicodeError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"s31: {exc}", file=sys.stderr)
        raise SystemExit(1)
