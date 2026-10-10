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
