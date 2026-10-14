#!/usr/bin/env python3
"""Zig child-input custody and installed export-source pin controls."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

FORMAL = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FORMAL / "tests/audit"))
sys.path.insert(0, str(FORMAL))

from general_structural_native_witness import CASES, case_bytes  # noqa: E402
from scripts.general_structural_native_witness import checked_words, native_check  # noqa: E402
from scripts.native_export_custody import (  # noqa: E402
    PINNED_EXPORT_SOURCES, ROOT, check_corpus_file,
    check_export_entry_sources,
)
from scripts.native_graph_certificate import check_graph  # noqa: E402


def expect_rejection(call, reason: str) -> None:
    try:
        call()
    except ValueError as exc:
        if reason not in str(exc):
            raise AssertionError(f"wrong rejection boundary: {exc}") from exc
    else:
        raise AssertionError("forged export custody was accepted")


def main() -> None:
    _, source, assignment = next(case for case in CASES if case[0] == "three_inputs")
    raw = case_bytes(source, assignment)
    inputs, nodes = checked_words(raw)
    with tempfile.TemporaryDirectory(prefix="s31-native-export-custody-") as directory:
        work = Path(directory)
        graph, exact_bytes = native_check(raw, inputs, nodes, work, export_graph=True)
        check_graph(graph, raw, inputs, nodes)
        assert json.loads(exact_bytes) == graph

        # A same-user writer appends whitespace immediately before Zig reads
        # the corpus. The JSON and emitted graph are unchanged. The old
        # semantic graph audit accepts it when only the new byte check is
        # disabled; the new custody check rejects this changed child input.
        real_run = subprocess.run

        def tampering_run(args, **kwargs):
            with Path(args[-1]).open("ab") as out:
                out.write(b" ")
            return real_run(args, **kwargs)

        with patch("scripts.general_structural_native_witness.subprocess.run",
                   side_effect=tampering_run), patch(
                       "scripts.general_structural_native_witness.check_corpus_file",
                       lambda *_: None):
            prior_graph, _ = native_check(raw, inputs, nodes, work, export_graph=True)
            check_graph(prior_graph, raw, inputs, nodes)
        with patch("scripts.general_structural_native_witness.subprocess.run",
                   side_effect=tampering_run):
            expect_rejection(lambda: native_check(
                raw, inputs, nodes, work, export_graph=True),
                "child corpus changed during export")

        planned = (work / "native-corpus.json").read_bytes()[:-1]
        expect_rejection(lambda: check_corpus_file(work / "native-corpus.json", planned),
                         "child corpus changed during export")

        shadow = work / "source-shadow"
        for path in PINNED_EXPORT_SOURCES:
            target = shadow / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / path).read_bytes())
        check_export_entry_sources(shadow)
        exporter = next(iter(PINNED_EXPORT_SOURCES))
        with (shadow / exporter).open("ab") as out:
            out.write(b"\n")
        expect_rejection(lambda: check_export_entry_sources(shadow),
                         "source changed; review export path")
    print(json.dumps({"honest_export": True, "semantically_inert_corpus_swap_rejected": True,
                      "unreviewed_exporter_change_rejected": True}, sort_keys=True))


if __name__ == "__main__":
    main()
