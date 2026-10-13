//! Recompute each raw DEEP answer from the captured PCS columns and samples.
//!
//! The core verifier computes quotient answers on sorted unique queries and
//! expands them to raw transcript order for `VerifiedProofCapture`. This gate
//! evaluates the same quotient law directly on the raw rows before the S31
//! verifier can publish a capture or report success. It does not authenticate
//! captured columns against Merkle roots or independently derive challenges.
const std = @import("std");
const core = @import("stwo_core");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const CirclePointQM31 = core.circle.CirclePointQM31;
const TreeVec = core.pcs.TreeVec;

pub fn validate(
    allocator: std.mem.Allocator,
    lifting_log_size: u32,
    raw: []const usize,
    column_log_sizes: [][]u32,
    sampled_points: [][][]CirclePointQM31,
    sampled_values: []QM31,
    queried_values: []M31,
    deep_answers: []QM31,
    deep_randomness: QM31,
) !void {
    if (raw.len == 0 or raw.len != deep_answers.len or
        column_log_sizes.len == 0 or
        column_log_sizes.len != sampled_points.len or
        lifting_log_size > core.circle.M31_CIRCLE_LOG_ORDER)
        return error.InvalidDeepCapture;

    var sample_count: usize = 0;
    var column_count: usize = 0;
    for (column_log_sizes, sampled_points) |logs, points| {
        if (logs.len != points.len) return error.InvalidDeepCapture;
        column_count = std.math.add(usize, column_count, logs.len) catch
            return error.InvalidDeepCapture;
        for (points) |column_points| {
            sample_count = std.math.add(usize, sample_count, column_points.len) catch
                return error.InvalidDeepCapture;
        }
    }
    const queried_count = std.math.mul(usize, column_count, raw.len) catch
        return error.InvalidDeepCapture;
    if (column_count == 0 or sample_count != sampled_values.len or
        queried_count != queried_values.len)
        return error.InvalidDeepCapture;

    const sample_views = try allocator.alloc([][]QM31, column_log_sizes.len);
    defer allocator.free(sample_views);
    const query_views = try allocator.alloc([][]M31, column_log_sizes.len);
    defer allocator.free(query_views);
    var samples_initialized: usize = 0;
    var queries_initialized: usize = 0;
    defer {
        for (sample_views[0..samples_initialized]) |columns| allocator.free(columns);
        for (query_views[0..queries_initialized]) |columns| allocator.free(columns);
    }
    var sample_at: usize = 0;
    var query_at: usize = 0;
    for (column_log_sizes, sampled_points, 0..) |logs, points, tree| {
        sample_views[tree] = try allocator.alloc([]QM31, logs.len);
        samples_initialized += 1;
        query_views[tree] = try allocator.alloc([]M31, logs.len);
        queries_initialized += 1;
        for (points, 0..) |column_points, column| {
            const sample_end = sample_at + column_points.len;
            const query_end = query_at + raw.len;
            sample_views[tree][column] = sampled_values[sample_at..sample_end];
            query_views[tree][column] = queried_values[query_at..query_end];
            sample_at = sample_end;
            query_at = query_end;
        }
    }

    const recomputed = try core.pcs.quotients.friAnswers(
        allocator,
        TreeVec([]u32).initOwned(column_log_sizes),
        TreeVec([][]CirclePointQM31).initOwned(sampled_points),
        TreeVec([][]QM31).initOwned(sample_views),
        deep_randomness,
        raw,
        TreeVec([][]M31).initOwned(query_views),
        lifting_log_size,
    );
    defer allocator.free(recomputed);
    if (recomputed.len != deep_answers.len) return error.InvalidDeepCapture;
    for (recomputed, deep_answers) |expected, recorded| {
        if (!expected.eql(recorded)) return error.InvalidDeepCapture;
    }
}
