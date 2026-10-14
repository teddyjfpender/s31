//! Reusable XDM04 certificate controls across admitted small profile shapes.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const cert = @import("pcs_xdm04_mixed_certificate");

const M31 = core.fields.m31.M31;
const xdm = core.pcs.transposed_merkle_sparse;
const Commitment = prover.pcs.transposed_cascade_experimental.Commitment;

fn exercise(k: u32, height_count: usize, raw: []const usize) !void {
    const allocator = std.testing.allocator;
    var words: [8][2][]M31 = undefined;
    var columns: [8][2][]const M31 = undefined;
    var source: [8][]const []const M31 = undefined;
    var counts = [_]usize{0} ** 8;
    defer for (0..height_count) |height| {
        for (0..counts[height]) |col| allocator.free(words[height][col]);
    };
    for (0..height_count) |height| {
        const width = if (height % 2 == 0) @as(usize, 2) else 1;
        for (0..width) |col| {
            const len = @as(usize, 1) << @intCast(k - @as(u32, @intCast(height)));
            words[height][col] = try allocator.alloc(M31, len);
            counts[height] += 1;
            for (words[height][col], 0..) |*value, index|
                value.* = M31.fromCanonical(@intCast(1000 + 100 * height + 20 * col + index));
            columns[height][col] = words[height][col];
        }
        source[height] = columns[height][0..width];
    }
    var commitment = try Commitment.commitSparse(allocator, source[0..height_count], raw.len);
    defer commitment.deinit();
    try cert.auditCommitment(commitment);
    const encoded = try commitment.encodeSparseOpenings(allocator, raw);
    defer allocator.free(encoded);
    var profile = xdm.Profile{
        .largest_log_size = k,
        .height_count = height_count,
        .columns = [_]u16{0} ** 8,
        .query_count = raw.len,
    };
    for (0..height_count) |height| profile.columns[height] = @intCast(source[height].len);
    var capture = try cert.verifyAndCapture(allocator, encoded, profile, commitment.root(), raw);
    defer capture.deinit();
    try capture.auditAll();
    for (raw, 0..) |position, query| {
        for (0..height_count) |height| {
            for (0..2) |j| {
                const index = xdm.pairBase(position, height) + j;
                var opening = try capture.openingAt(height, query, j);
                defer opening.deinit(allocator);
                try std.testing.expect(opening.check());
                for (opening.row, 0..) |value, col|
                    try std.testing.expect(value.eql(source[height][col][index]));
            }
        }
    }

    var changed = try capture.openingAt(0, 0, 0);
    defer changed.deinit(allocator);
    changed.steps[0].sibling[0] ^= 1;
    try std.testing.expect(!changed.check());
    changed.steps[0].sibling[0] ^= 1;
    const inserted_row = changed.steps[0].inserted_row;
    changed.steps[0].inserted_row = null;
    try std.testing.expect(!changed.check());
    changed.steps[0].inserted_row = inserted_row;
    changed.path_position ^= 1;
    try std.testing.expect(!changed.check());

    const original = capture.opened.values[0][0];
    capture.opened.values[0][0] = M31.fromCanonical(original.v + 1);
    try std.testing.expectError(error.InvalidXdm04Certificate, capture.auditAt(0, 0, 0));
    capture.opened.values[0][0] = original;
    try capture.auditAll();

    const duplicate_cols = profile.columns[0];
    const duplicate_offset = (raw.len - 1) * 2 * duplicate_cols;
    const duplicate_word = capture.opened.values[0][duplicate_offset];
    capture.opened.values[0][duplicate_offset] = M31.fromCanonical(duplicate_word.v + 1);
    try std.testing.expectError(error.InvalidXdm04Certificate,
        capture.auditAt(0, raw.len - 1, 0));
    capture.opened.values[0][duplicate_offset] = duplicate_word;
    try capture.auditAll();

    const leaf = commitment.layers[k][0];
    commitment.layers[k][0][0] ^= 1;
    try std.testing.expectError(error.InvalidXdm04Certificate, cert.auditCommitment(commitment));
    commitment.layers[k][0] = leaf;
    try cert.auditCommitment(commitment);

    const inserted = commitment.layers[k - 1][0];
    commitment.layers[k - 1][0][0] ^= 1;
    try std.testing.expectError(error.InvalidXdm04Certificate, cert.auditCommitment(commitment));
    commitment.layers[k - 1][0] = inserted;
    try cert.auditCommitment(commitment);

    const upper_root = commitment.layers[0][0];
    commitment.layers[0][0][0] ^= 1;
    try std.testing.expectError(error.InvalidXdm04Certificate, cert.auditCommitment(commitment));
    commitment.layers[0][0] = upper_root;
    try cert.auditCommitment(commitment);

    const source_word = words[0][0][0];
    words[0][0][0] = M31.fromCanonical(source_word.v + 1);
    try std.testing.expectError(error.InvalidXdm04Certificate, cert.auditCommitment(commitment));
    words[0][0][0] = source_word;
    try cert.auditCommitment(commitment);
}

test "XDM04 independent certificates cover duplicate, overlapping and varied-height profiles" {
    try exercise(5, 2, &.{ 5, 4, 5 });
    try exercise(5, 3, &.{ 5, 12, 5 });
    try exercise(6, 4, &.{ 5, 47, 24, 47 });
}
