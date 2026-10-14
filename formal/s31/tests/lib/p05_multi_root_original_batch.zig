//! Experimental P05 first-layer original-word adapter over the four existing
//! Gate commitment roots. This is an authenticated sampled-row construction,
//! not a degree test or a versioned proof verifier.
const std = @import("std");
const core = @import("stwo_core");
const lifted = @import("s31_lifted_capture");

const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Capture = core.verifier.ProofCapture(H);
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;

pub const HeightBatch = struct {
    /// Verifier-owned FRI-extended log size of the original source columns.
    column_log_size: u32,
    /// Projection of each raw lifted query, including repeated positions.
    projected_positions: []usize,
    /// Sum of authenticated original words at each projected position.
    original_values: []QM31,
    column_count: usize,
};

pub const OriginalBatches = struct {
    by_height: []HeightBatch,

    pub fn deinit(self: *OriginalBatches, allocator: std.mem.Allocator) void {
        for (self.by_height) |batch| {
            allocator.free(batch.projected_positions);
            allocator.free(batch.original_values);
        }
        allocator.free(self.by_height);
        self.* = undefined;
    }
};

/// Reconstruct a per-height original-only first-layer batch. The caller must
/// supply the exact four roots from the already verified Gate proof. We rehash
/// every captured row/path and check its projection before reading any value.
///
/// Powers of the captured post-OOD DEEP challenge restart at 1 for each
/// height and follow tree/column source order. A future P05 selector must
/// prove that this coefficient schedule is the one in its multi-domain FRI
/// theorem; this function only fixes an executable candidate schedule.
pub fn reconstruct(
    allocator: std.mem.Allocator,
    pcs: PcsConfigV2,
    proof_roots: []const H.Hash,
    capture: *const Capture,
) !OriginalBatches {
    try lifted.validate(allocator, pcs, proof_roots, capture);

    const raw = capture.queries.raw;
    var total_columns: usize = 0;
    for (capture.column_log_sizes) |logs| {
        total_columns = std.math.add(usize, total_columns, logs.len) catch
            return error.InvalidP05OriginalBatch;
    }
    const heights = try allocator.alloc(u32, total_columns);
    defer allocator.free(heights);
    var height_count: usize = 0;
    for (capture.column_log_sizes) |logs| for (logs) |log| {
        var exists = false;
        for (heights[0..height_count]) |known| {
            if (known == log) {
                exists = true;
                break;
            }
        }
        if (!exists) {
            heights[height_count] = log;
            height_count += 1;
        }
    };
    // Descending native-height order is the intended multi-domain insertion
    // order. Tree/column order remains the coefficient order within a height.
    for (0..height_count) |i| {
        for (i + 1..height_count) |j| {
            if (heights[j] > heights[i]) std.mem.swap(u32, &heights[i], &heights[j]);
        }
    }

    const batches = try allocator.alloc(HeightBatch, height_count);
    var initialized: usize = 0;
    errdefer {
        for (batches[0..initialized]) |batch| {
            allocator.free(batch.projected_positions);
            allocator.free(batch.original_values);
        }
        allocator.free(batches);
    }
    for (heights[0..height_count], batches) |log, *batch| {
        const positions = try core.pcs.utils.prepareTreeQueryPositions(
            allocator, raw, pcs.trace_lifting_log_size, log,
        );
        errdefer allocator.free(positions);
        const values = try allocator.alloc(QM31, raw.len);
        @memset(values, QM31.zero());
        batch.* = .{
            .column_log_size = log,
            .projected_positions = positions,
            .original_values = values,
            .column_count = 0,
        };
        initialized += 1;
    }

    const powers = try allocator.alloc(QM31, height_count);
    defer allocator.free(powers);
    @memset(powers, QM31.one());
    var at: usize = 0;
    for (capture.column_log_sizes) |logs| {
        for (logs) |log| {
            const end = std.math.add(usize, at, raw.len) catch
                return error.InvalidP05OriginalBatch;
            if (end > capture.queried_values.len) return error.InvalidP05OriginalBatch;
            var index: usize = 0;
            while (index < height_count and batches[index].column_log_size != log) : (index += 1) {}
            if (index == height_count) return error.InvalidP05OriginalBatch;
            const weight = powers[index];
            for (capture.queried_values[at..end], batches[index].original_values) |value, *sum| {
                sum.* = sum.add(QM31.fromBase(value).mul(weight));
            }
            powers[index] = weight.mul(capture.deep_randomness);
            batches[index].column_count += 1;
            at = end;
        }
    }
    if (at != capture.queried_values.len) return error.InvalidP05OriginalBatch;
    return .{ .by_height = batches };
}
