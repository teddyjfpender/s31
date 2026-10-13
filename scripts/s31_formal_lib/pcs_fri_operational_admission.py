"""Source contract for the S31 post-verification FRI capture admission gate.

This pins the gate and its key checks to reviewed Zig source. It does not
prove Zig execution refines Lean `OperationalExtraction.operationalAccepts`.
"""
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(native: str, admission: str) -> None:
    gate = (
        "try core.verifier.verifyBorrowedExWithProofCapture(",
        "defer capture.deinit(allocator);",
        "try fri_capture_admission.validate(",
        "pcs.fri_config.folding(),",
        "capture.queries.raw,",
        "capture.deep_answers,",
        "capture.fri,",
        "capture.last_layer_coefficients,",
    )
    regions = (
        region(native, "fn verifyProfile(", "fn logsFor("),
        region(native, "pub fn verifySparse(", "const SPARSE_WIDE_MAGIC ="),
        region(native, "fn verifySparseWideInternal(", "const DIRECT_GATE_MAGIC ="),
        region(native, "fn verifyDirectProfile(", "fn sparseLogs("),
    )
    if (native.count(gate[0]) != len(regions) or
            native.count(gate[2]) != len(regions)):
        raise ValueError("S31 core FRI capture or admission call count changed")
    for index, verify in enumerate(regions):
        ordered_once(verify, f"S31 FRI capture admission path {index}", *gate)
    for index in (0, 2):
        ordered_once(regions[index], f"S31 FRI capture publication path {index}",
                     gate[2], "if (converted_out) |out| {",
                     "out.* = try cpu.verifier_proof.fromVerifiedCapture(")
    replay = region(admission, "pub fn validate(", "fn foldLineAtSubset(")
    ordered_once(
        replay, "S31 FRI raw-slot replay",
        "raw.len != config.n_queries or",
        "coefficients.len > (@as(usize, 1) << @intCast(config.log_last_layer_degree_bound))",
        "captured.layers.len != 1 + core.fri.nFoldSteps(remaining, config.fold_step)",
        "layer.fold_step != expected_step or layer.fold_width != width or",
        "if (!left.eql(right)) return error.InvalidFriCapture;",
        "if (position != layer.positions[slot]) return error.InvalidFriCapture;",
        "if (!current.eql(subset[position % width])) return error.InvalidFriCapture;",
        "try foldCircle(",
        "try foldLineAtSubset(",
        "if (!current.eql(expected)) return error.InvalidFriCapture;",
    )
    pair = region(admission, "fn pair(", "pub fn validate(")
    ordered_once(
        pair, "independent FRI pair fold",
        "const inverse = try coordinate.inv();",
        "return left.add(right).add(alpha.mul(left.sub(right).mulM31(inverse)));",
        "scratch[i] = try pair(",
        "out.* = try pair(alpha, y, values[2 * i], values[2 * i + 1]);",
    )


def check_pcs_fri_operational_admission(root: Path) -> None:
    check_sources(
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (root / "src/frontends/s31/runtime/fri_capture_admission.zig").read_text(),
    )
