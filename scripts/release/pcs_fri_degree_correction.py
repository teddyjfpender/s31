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
    "deps/stwo-zig/src/core/verifier.zig": "85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381",
    # Sparse-only post-admission H3 inspection now exports the first
    # authenticated query/source row. The traced direct Gate event region,
    # accepted proof path, and legacy degree test are unchanged.
    "src/frontends/s31/runtime/native_verifier.zig": "e41b5577fc144b9a065036ccdc8c3b701e38b09404282be216605894c08f38a4",
}

PROVER = "deps/stwo-zig/src/prover/pcs/scheme.zig"
VERIFIER = "deps/stwo-zig/src/core/pcs/verifier.zig"
ANSWERS = "deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig"
STARK_VERIFIER = "deps/stwo-zig/src/core/verifier.zig"
S31_GATE_VERIFIER = "src/frontends/s31/runtime/native_verifier.zig"

# A future profile must preserve these rooted epochs. Each marker is unique
# inside the named function and is reported with its physical source line.
# This traces the accepted Gate proof-capture path, not all S31 profiles.
GATE_EVENTS = (
    ("legacy_wire", "try pcs_mode_binding.requireLegacyPostcard(raw[header_len..]);"),
    ("fixed_root", "try scheme.commit(allocator, roots[0], component_logs.items[0], &channel);"),
    ("public_statement", "channel.mixFelts(&outputs);"),
    ("main_root", "try scheme.commit(allocator, roots[1], component_logs.items[1], &channel);"),
    ("lookup_challenge", "const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);"),
    ("interaction_claim", "core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..sum_count]);"),
    ("interaction_root", "try scheme.commit(allocator, roots[2], component_logs.items[2], &channel);"),
    ("stark_verification", "try core.verifier.verifyBorrowedExWithProofCapture("),
)
STARK_EVENTS = (
    ("composition_challenge", "const composition_randomness = channel.drawSecureFelt();"),
    ("composition_root", "try commitment_scheme.commit("),
    ("oods_seed", "const oods_seed = channel.drawSecureFelt();"),
    ("oods_mask", "var sample_points = try components.maskPoints("),
    ("composition_oods_identity", "if (!composition_oods_eval.eql(try components.evalCompositionPolynomialAtPoint("),
    ("pcs_opening", "try commitment_scheme.verifyValuesWithBorrowedProofCapture("),
)
PCS_EVENTS = (
    ("sampled_values_mixed", "channel.mixFelts(sampled_values_flat);"),
    ("deep_challenge", "const deep_randomness = channel.drawSecureFelt();"),
    ("fri_commit", "var fri_verifier = try FriVerifier.commit("),
    ("query_draw", "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw("),
    ("original_row_authentication", "tree.verifyWithPathCapture("),
    ("quotient_answer", "const fri_answers = try quotients.friAnswers("),
    ("fri_quotient_check", "fri_verifier.decommitWithQueryCapture("),
)


def _ordered_source_events(source: str, path: str, start: str, end: str,
                           markers: tuple[tuple[str, str], ...]) -> list[dict[str, object]]:
    """Fail if a reviewed function loses, duplicates, or reorders an event."""
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError(f"P05 function boundary changed: {path}")
    lo = source.index(start)
    hi = source.index(end, lo)
    body = source[lo:hi]
    events: list[dict[str, object]] = []
    previous = -1
    for name, marker in markers:
        if body.count(marker) != 1:
            raise ValueError(f"P05 event missing or duplicated: {name}")
        offset = body.index(marker)
        if offset <= previous:
            raise ValueError(f"P05 event reordered: {name}")
        previous = offset
        events.append({"event": name, "source": path,
                       "line": source.count("\n", 0, lo + offset) + 1})
    return events


def native_gate_epoch_trace(sources: dict[str, bytes]) -> list[dict[str, object]]:
    gate = sources[S31_GATE_VERIFIER].decode()
    stark = sources[STARK_VERIFIER].decode()
    pcs = sources[VERIFIER].decode()
    return (
        _ordered_source_events(gate, S31_GATE_VERIFIER, "fn verifyDirectProfile(",
                               "\nfn sparseLogs(", GATE_EVENTS)
        + _ordered_source_events(stark, STARK_VERIFIER, "fn verifyImpl(",
                                 "\n/// A transcript seed", STARK_EVENTS)
        + _ordered_source_events(pcs, VERIFIER, "        fn verifyValuesImpl(",
                                 "        /// The leaf count queries", PCS_EVENTS)
    )


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

    epoch_trace = native_gate_epoch_trace(sources)
    if [item["event"] for item in epoch_trace] != [
        name for name, _ in GATE_EVENTS + STARK_EVENTS + PCS_EVENTS
    ]:
        raise ValueError("P05 reviewed Gate epoch trace changed")

    # This is a proposed *new* selector, not a claim about legacy postcard
    # proofs. The source trace above is only a necessary, syntax-level check.
    proposed_profile = {
        "schema": "s31-gate-degree-corrected-pcs-v2-spec",
        "selector_installed": False,
        "required_commitment_order": ["fixed", "main", "interaction", "composition"],
        "required_batch_ensemble": "each_original_word_and_its_own_two_point_quotient_at_its_native_height",
        "requirements": {
            "four_existing_root_epochs_preserved": "source_order_observed_only",
            "composition_columns_in_ensemble": "not_evidenced",
            "authenticated_original_oracle_ownership": "not_evidenced",
            "original_word_degree_test": "absent_from_native_fri_input",
            "own_quotient_degree_test_per_source_word": "absent_from_native_fri_input",
            "two_point_oods_claim_and_divisor_refinement": "not_evidenced",
            "cross_domain_correlated_agreement_and_small_height_bound": "not_evidenced",
            "query_and_adaptive_bcs_error_join": "not_evidenced",
            "prover_verifier_installed_binary_refinement": "not_evidenced",
        },
        "proof_admissible": False,
    }

    return {
        "schema": "s31-pcs-fri-p05-degree-correction-v1",
        "status": "published_degree_corrected_theorem_not_applicable",
        "engine_gitlink_commit": gitlink,
        "source_sha256": observed,
        "native_gate_epoch_trace": epoch_trace,
        "native_gate_epoch_trace_scope": "legacy_direct_profile_only",
        "raw_gate_epoch_trace_evidenced": False,
        "proposed_degree_corrected_profile": proposed_profile,
        "native_batch_fri_input": "one_accumulated_deep_quotient_word",
        "native_nonquotient_degree_test_identified": False,
        "published_degree_corrected_nonquotient_premise_met": False,
        "p05_discharged": False,
        "native_proven_security_bits": None,
        "reason": "The reviewed prover commits one lazy quotient provider to FRI; the reviewed verifier supplies one accumulated friAnswers quotient word to its one FRI verifier. Merkle authentication of original query rows is not a low-degree test of their polynomials.",
        "remaining_discharge": [
            "introduce a versioned PCS selector whose prover and verifier pair each authenticated original with its own two-point OOD quotient at native source height, including composition columns, while preserving four existing root epochs; or prove a sound alternative theorem for this quotient-only protocol",
            "prove original and own-quotient degree bounds, the exact two-point OOD identity, correlated cross-domain agreement, and the small-height condition for every source column",
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
