"""Fail closed if reviewed S31 prover/verifier transcript stages reorder.

This is a source contract, not a cryptographic proof: it checks the fixed
main-commitment/draw/interaction-commitment order used by Lean's fixed-witness
challenge bound. Source digests in ``source-bindings.json`` still require
review when any bound implementation changes.
"""
from __future__ import annotations

from pathlib import Path


def check_windows(
    source: str,
    *,
    main_commit: str,
    draw: str,
    interaction_commit: str,
    windows: int,
    draws_per_window: int,
    label: str,
) -> None:
    starts = [i for i in range(len(source)) if source.startswith(main_commit, i)]
    ends = [i for i in range(len(source)) if source.startswith(interaction_commit, i)]
    draws = [i for i in range(len(source)) if source.startswith(draw, i)]
    if len(starts) != windows or len(ends) != windows or len(draws) != windows * draws_per_window:
        raise ValueError(f"{label}: transcript stage count changed")
    for index, (start, end) in enumerate(zip(starts, ends)):
        if start >= end or (index + 1 < windows and end >= starts[index + 1]):
            raise ValueError(f"{label}: main/draw/interaction stage order changed")
        inside = sum(start < position < end for position in draws)
        if inside != draws_per_window:
            raise ValueError(f"{label}: lookup draw moved outside its committed-main window")


def check_stage_after(source: str, *, before: str, after: str,
                      count: int, label: str) -> None:
    starts = [i for i in range(len(source)) if source.startswith(before, i)]
    ends = [i for i in range(len(source)) if source.startswith(after, i)]
    if len(starts) != count or len(ends) != count or any(
        start >= end or (index + 1 < count and end >= starts[index + 1])
        for index, (start, end) in enumerate(zip(starts, ends))
    ):
        raise ValueError(f"{label}: composition coefficient path moved before interaction commitment")


def check_protocol_order(root: Path) -> None:
    contracts = [
        (
            "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig",
            "step(observer, .commit_base_trace, &channel);",
            "lookup_transcript.drawLookupElements(allocator, &channel)",
            "step(observer, .commit_interaction_trace, &channel);",
            1, 1,
        ),
        (
            "src/frontends/s31/runtime/native_verifier.zig",
            "try scheme.commit(allocator, roots[1]",
            "lookup_transcript.drawLookupElements(allocator, &channel)",
            "try scheme.commit(allocator, roots[2]",
            4, 1,
        ),
        (
            "src/frontends/s31/sha/proving/sha_direct_circuit_prover.zig",
            "try commit(&scheme, allocator, main, &channel);",
            "lookup_transcript.drawLookupElements(allocator, &channel)",
            "try commit(&scheme, allocator, interaction, &channel);",
            1, 2,
        ),
        (
            "src/frontends/s31/sha/verification/sha_direct_circuit_native_verifier.zig",
            "try verifier.commit(allocator, roots[1]",
            "lookup_transcript.drawLookupElements(allocator, &channel)",
            "try verifier.commit(allocator, roots[2]",
            1, 2,
        ),
    ]
    for path, main, draw, interaction, windows, draws_per_window in contracts:
        check_windows(
            (root / path).read_text(), main_commit=main, draw=draw,
            interaction_commit=interaction, windows=windows,
            draws_per_window=draws_per_window, label=path,
        )
    composition_contracts = [
        ("deps/stwo-zig/src/integrations/circuit_cpu/prove.zig",
         "step(observer, .commit_interaction_trace, &channel);",
         "var stark_proof = try Engine.prove(", 1),
        ("src/frontends/s31/runtime/native_verifier.zig",
         "try scheme.commit(allocator, roots[2]",
         "try core.verifier.verifyBorrowedExWithProofCapture(", 4),
        ("deps/stwo-zig/src/frontends/circuit/stark_verifier/verify.zig",
         "try channel.mixCommitment(V, ctx, proof.interaction_root);",
         "const composition_polynomial_coeff = try channel.drawQm31(V, ctx);", 1),
    ]
    for path, before, after, count in composition_contracts:
        check_stage_after((root / path).read_text(), before=before,
                          after=after, count=count, label=path)
    core_prover = (root / "deps/stwo-zig/src/prover/prove.zig").read_text()
    core_verifier = (root / "deps/stwo-zig/src/core/verifier.zig").read_text()
    if core_prover.count("const random_coeff = blk: {") != 1 or \
            "break :blk channel.drawSecureFelt();" not in core_prover or \
            core_verifier.count("const composition_randomness = channel.drawSecureFelt();") != 1:
        raise ValueError("core STARK composition coefficient draw changed")
