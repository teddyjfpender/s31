"""Source contract for S31's raw DEEP answer recomputation gate.

The guard pins call order and data inputs, but does not prove Zig execution,
the quotient formula, Merkle binding, or transcript challenge derivation.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(native: str, admission: str, pcs: str) -> None:
    gate = (
        "try core.verifier.verifyBorrowedExWithProofCapture(",
        "defer capture.deinit(allocator);",
        "try deep_capture_admission.validate(allocator, pcs.trace_lifting_log_size,\n"
        "        capture.queries.raw, capture.column_log_sizes, capture.sampled_points,",
        "capture.sampled_values, capture.queried_values, capture.deep_answers,",
        "capture.deep_randomness);",
        "try fri_capture_admission.validate(",
    )
    regions = (
        region(native, "fn verifyProfile(", "fn logsFor("),
        region(native, "pub fn verifySparse(", "const SPARSE_WIDE_MAGIC ="),
        region(native, "fn verifySparseWideInternal(", "const DIRECT_GATE_MAGIC ="),
        region(native, "fn verifyDirectProfile(", "fn sparseLogs("),
    )
    if native.count(gate[2]) != len(regions):
        raise ValueError("S31 DEEP capture admission call count changed")
    for index, verify in enumerate(regions):
        ordered_once(verify, f"S31 raw DEEP admission path {index}", *gate)

    replay = region(admission, "pub fn validate(", "\n}")
    ordered_once(
        replay, "S31 raw DEEP captured-row replay",
        "raw.len != deep_answers.len or",
        "column_log_sizes.len != sampled_points.len or",
        "column_count == 0 or sample_count != sampled_values.len or",
        "queried_count != queried_values.len",
        "sample_views[tree][column] = sampled_values[sample_at..sample_end];",
        "query_views[tree][column] = queried_values[query_at..query_end];",
        "const recomputed = try core.pcs.quotients.friAnswers(",
        "deep_randomness,",
        "raw,",
        "if (!expected.eql(recorded)) return error.InvalidDeepCapture;",
    )

    core_flow = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    ordered_once(
        core_flow, "core unique-to-raw DEEP answer custody",
        "const fri_answers = try quotients.friAnswers(",
        "deep_randomness,\n                query_positions,\n"
        "                proof.queried_values,",
        "fri_verifier.decommitWithQueryCapture(",
        "const deep_answers = try expandQueryValues(\n"
        "                    allocator,\n                    fri_answers,\n"
        "                    query_capture.raw,\n"
        "                    query_capture.unique,",
        ".deep_answers = deep_answers,",
    )


def check_pcs_fri_deep_custody(root: Path) -> None:
    check_sources(
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (root / "src/frontends/s31/runtime/deep_capture_admission.zig").read_text(),
        (root / "deps/stwo-zig/src/core/pcs/verifier.zig").read_text(),
    )
