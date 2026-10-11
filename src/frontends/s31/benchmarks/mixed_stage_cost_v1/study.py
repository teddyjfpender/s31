#!/usr/bin/env python3
"""Freeze-gated mixed stage cost collector, native audit, fit, and evaluation.

No command in this file should be run on design-only evidence. The protocol
and timestamped anchor are separate committed inputs. Held-out commands also
require the committed model freeze produced from anchored training evidence.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from anchors import evaluate_heldout, fit_train, train_model_admission
from cohort import design
from evidence import audit_split, build_split, prove_split
from protocol import check


def add_freeze(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)


def add_train_model(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--train-out", required=True, type=Path)
    parser.add_argument("--expected-train-phase-root-sha256", required=True)
    parser.add_argument("--train-phase-anchor-commit", required=True)
    parser.add_argument("--expected-model-sha256", required=True)
    parser.add_argument("--model-anchor-commit", required=True)


def admission(args: argparse.Namespace) -> tuple[dict, dict] | tuple[None, None]:
    if getattr(args, "split", "train") != "heldout" and args.command != "evaluate":
        return None, None
    return train_model_admission(
        args.train_out, args.expected_protocol_sha256,
        args.expected_train_phase_root_sha256, args.train_phase_anchor_commit,
        args.expected_model_sha256, args.model_anchor_commit)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("build", "prove", "audit"):
        command = commands.add_parser(name)
        add_freeze(command)
        command.add_argument("--split", choices=("train", "heldout"), required=True)
        command.add_argument("--out", required=True, type=Path)
        if name == "audit":
            command.add_argument("--expected-phase-root-sha256", required=True)
            command.add_argument("--phase-anchor-commit", required=True)
        # Optional in parser for train, required at runtime for heldout.
        command.add_argument("--train-out", type=Path)
        command.add_argument("--expected-train-phase-root-sha256")
        command.add_argument("--train-phase-anchor-commit")
        command.add_argument("--expected-model-sha256")
        command.add_argument("--model-anchor-commit")
    fit = commands.add_parser("fit")
    add_freeze(fit)
    fit.add_argument("--train-out", required=True, type=Path)
    fit.add_argument("--expected-train-phase-root-sha256", required=True)
    fit.add_argument("--train-phase-anchor-commit", required=True)
    evaluate = commands.add_parser("evaluate")
    add_freeze(evaluate)
    evaluate.add_argument("--heldout-out", required=True, type=Path)
    add_train_model(evaluate)
    args = parser.parse_args()
    check(args.expected_protocol_sha256, args.protocol_anchor_commit)
    if args.command == "fit":
        result = {"model_sha256": fit_train(args.train_out,
                                            args.expected_protocol_sha256,
                                            args.expected_train_phase_root_sha256,
                                            args.train_phase_anchor_commit)}
    else:
        if args.command == "evaluate":
            _, model = admission(args)
            result = evaluate_heldout(args.heldout_out, model,
                                      args.expected_protocol_sha256)
        else:
            if args.split == "heldout" and not all((args.train_out,
                    args.expected_train_phase_root_sha256, args.train_phase_anchor_commit,
                    args.expected_model_sha256, args.model_anchor_commit)):
                raise ValueError("held-out phase requires every frozen train model argument")
            bound, _ = admission(args)
            if args.command == "build":
                result = build_split(args.split, args.out, args.expected_protocol_sha256,
                                     args.protocol_anchor_commit, bound)
            elif args.command == "prove":
                result = prove_split(args.split, args.out, args.expected_protocol_sha256,
                                     args.protocol_anchor_commit, bound)
            else:
                result = audit_split(args.out, args.split, args.expected_protocol_sha256,
                                     args.protocol_anchor_commit,
                                     args.expected_phase_root_sha256,
                                     args.phase_anchor_commit, bound)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
