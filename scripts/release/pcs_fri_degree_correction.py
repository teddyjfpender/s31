#!/usr/bin/env python3
"""Source-bound P05 theorem-applicability audit for the pinned native PCS.

This is a negative diagnostic. It checks one reviewed native control-flow
shape; it does not prove that source text is the installed verifier binary,
that the quotient is low degree, or that a different theorem applies.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINE_GITLINK = "59e1f115250b8af01712b9bf3d71616e53094964"

# Exact reviewed source versions. Any engine edit requires a fresh semantic
# review before this diagnostic may classify its native batch protocol.
SOURCE_SHA256 = {
    "deps/stwo-zig/src/prover/pcs/scheme.zig": "88ab21970d32dda383a191ce5f12c329ce127f2829712a99068dd369d147e93f",
    "deps/stwo-zig/src/prover/pcs/quotient_ops.zig": "f4684c25d35e15fc57a6d6283df241402004253c6719a1237f3f8e01ebba2115",
    "deps/stwo-zig/src/prover/pcs/quotients/lazy_provider.zig": "7d8c02ad443bba0941f10a8d22ecb1ef81e77b9837c3e1f561445fe31d0e728e",
    "deps/stwo-zig/src/core/pcs/verifier.zig": "e119335172e17db5fd1345f476c7f6ad7fdf67e394a5b18d5c2085e892ffe3d5",
    "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig": "5280b74c1762860fad733066a40d96dada813908532e3b8854e0a3f02f182181",
    "deps/stwo-zig/src/core/fri.zig": "5f84501d1ffbaf5d33d6f7063bea7e6fd88a4cb65140ff360b75cb11f812121f",
    "deps/stwo-zig/src/prover/fri.zig": "22acc5c7af16cc06fa646e5eedfe9a9a5bee95a273b53dbac83a599576f3e609",
}

PROVER = "deps/stwo-zig/src/prover/pcs/scheme.zig"
VERIFIER = "deps/stwo-zig/src/core/pcs/verifier.zig"
ANSWERS = "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig"


def _once_between(source: str, first: str, second: str, label: str) -> None:
    if source.count(first) != 1 or source.count(second) != 1 or source.index(first) >= source.index(second):
        raise ValueError(f"reviewed {label} path changed")


def classify(sources: dict[str, bytes], gitlink: str) -> dict[str, object]:
    """Classify only the exact source shape that was manually reviewed."""
    if gitlink != ENGINE_GITLINK:
        raise ValueError("native engine gitlink changed; P05 needs a new review")
    if set(sources) != set(SOURCE_SHA256):
        raise ValueError("native P05 source roster changed")
    observed = {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}
    if observed != SOURCE_SHA256:
        changed = sorted(name for name in sources if observed[name] != SOURCE_SHA256[name])
        raise ValueError(f"native P05 source changed; review required: {', '.join(changed)}")

    prover = sources[PROVER].decode()
    verifier = sources[VERIFIER].decode()
    answers = sources[ANSWERS].decode()
    _once_between(prover,
                  "LazyQuotientProvider.initForBackendWithWorkRecorder(",
                  "FriProver(B, H, MC).commitLazyWithWorkRecorderAndRootMixCapture(",
                  "prover quotient-to-FRI")
    _once_between(verifier, "FriVerifier.commit(", "quotients.friAnswers(",
                  "verifier FRI-to-quotient")
    _once_between(verifier, "quotients.friAnswers(",
                  "fri_verifier.decommitWithQueryCapture(",
                  "verifier quotient-to-FRI")
    if verifier.count("fri_verifier.decommit(allocator, fri_answers)") != 1:
        raise ValueError("reviewed uncaptured verifier FRI answer path changed")
    if "&provider," not in prover or "fri_answers," not in verifier:
        raise ValueError("reviewed prover or verifier FRI input changed")
    if "pub fn friAnswers(" not in answers or ") ![]QM31 {" not in answers:
        raise ValueError("reviewed quotient answer type changed")

    return {
        "schema": "s31-pcs-fri-p05-degree-correction-v1",
        "status": "published_degree_corrected_theorem_not_applicable",
        "engine_gitlink_commit": gitlink,
        "source_sha256": observed,
        "native_batch_fri_input": "one_accumulated_deep_quotient_word",
        "native_nonquotient_degree_test_identified": False,
        "published_degree_corrected_nonquotient_premise_met": False,
        "p05_discharged": False,
        "native_proven_security_bits": None,
        "reason": "The reviewed prover commits one lazy quotient provider to FRI; the reviewed verifier supplies one accumulated friAnswers quotient word to its one FRI verifier. Merkle authentication of original query rows is not a low-degree test of their polynomials.",
        "remaining_discharge": [
            "implement and prove the paper's quotient plus nonquotient degree-corrected ensemble, including exact bounds and multi-domain ownership; or prove a sound alternative theorem for this quotient-only protocol",
            "prove native Zig control-flow and installed-binary correspondence to the reviewed source",
            "bind original and sampled columns to committed oracles and instantiate all OODS/FRI parameters and error terms",
        ],
    }


def audit(root: Path = ROOT) -> dict[str, object]:
    gitlink = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True
    ).strip()
    sources = {name: (root / name).read_bytes() for name in SOURCE_SHA256}
    return classify(sources, gitlink)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-p05", action="store_true",
                        help="exit 2 until a reviewed theorem applies to the native protocol")
    args = parser.parse_args(argv)
    try:
        report = audit()
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError, ValueError) as exc:
        print(f"P05 source audit rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_p05 and not report["p05_discharged"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
