//! Post-verification raw PCS/FRI capture checks for release SHA profiles.
//!
//! These replay the recorded DEEP answers and every raw FRI fold before a
//! SHA package verifier reports success. They are consistency checks on the
//! verified capture; they do not prove Merkle binding or proximity soundness.
const std = @import("std");
const core = @import("stwo_core");
const deep = @import("../../runtime/deep_capture_admission.zig");
const fri = @import("../../runtime/fri_capture_admission.zig");

pub fn validate(
    comptime H: type,
    allocator: std.mem.Allocator,
    pcs: core.pcs.config_v2.PcsConfigV2,
    capture: core.verifier.ProofCapture(H),
) !void {
    try deep.validate(allocator, pcs.trace_lifting_log_size,
        capture.queries.raw, capture.column_log_sizes, capture.sampled_points,
        capture.sampled_values, capture.queried_values, capture.deep_answers,
        capture.deep_randomness);
    try fri.validate(H, allocator, pcs.fri_config.folding(),
        capture.queries.raw, capture.deep_answers, capture.fri,
        capture.last_layer_coefficients);
}
