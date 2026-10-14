//! Four independent roots and raw query slots exercise the experimental P05
//! original-word adapter. No STARK proof bytes or acceptance claim are made.
const std = @import("std");
const core = @import("stwo_core");
const adapter = @import("s31_adapter");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Path = core.vcs_lifted.verifier.MerklePathCapture(H);

fn leaf(value: u32) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(&[_]M31{M31.fromCanonical(value)});
    return hasher.finalize();
}

test "P05 original batch reconstructs four independently rooted trees at two heights" {
    const alloc = std.testing.allocator;
    // Tree order is the existing Gate order: fixed, main, interaction,
    // composition. Both high-height values include the composition word.
    const rows = [4][4]u32{
        .{ 2, 3, 2, 3 },
        .{ 4, 5, 6, 7 },
        .{ 8, 9, 8, 9 },
        .{ 10, 11, 12, 13 },
    };
    var raw = [_]usize{ 0, 1, 2, 0 };
    var unique = [_]usize{ 0, 1, 2 };
    var roots: [4]H.Hash = undefined;
    var positions: [4][4]usize = undefined;
    var siblings: [4][8]H.Hash = undefined;
    var paths: [4]Path = undefined;
    var values: [16]M31 = undefined;
    for (rows, 0..) |row, tree| {
        var leaves: [4]H.Hash = undefined;
        for (row, 0..) |value, i| leaves[i] = leaf(value);
        const left = H.hashChildren(.{ .left = leaves[0], .right = leaves[1] });
        const right = H.hashChildren(.{ .left = leaves[2], .right = leaves[3] });
        roots[tree] = H.hashChildren(.{ .left = left, .right = right });
        for (raw, 0..) |position, slot| {
            positions[tree][slot] = position;
            siblings[tree][2 * slot] = leaves[position ^ 1];
            siblings[tree][2 * slot + 1] = if (position < 2) right else left;
            values[tree * raw.len + slot] = M31.fromCanonical(row[position]);
        }
        paths[tree] = .{
            .positions = positions[tree][0..],
            .path_depth = 2,
            .siblings = siblings[tree][0..],
        };
    }
    var log_arrays = [4][1]u32{ .{1}, .{2}, .{1}, .{2} };
    var logs: [4][]u32 = undefined;
    for (&log_arrays, &logs) |*one, *slice| slice.* = one[0..];
    var capture: core.verifier.ProofCapture(H) = undefined;
    capture.queries = .{ .raw = raw[0..], .unique = unique[0..] };
    capture.commitments = roots[0..];
    capture.column_log_sizes = logs[0..];
    capture.queried_values = values[0..];
    capture.trace_paths = paths[0..];
    capture.deep_randomness = QM31.fromU32Unchecked(7, 0, 0, 0);
    const fri = try core.pcs.config_v2.FriConfigV2.init(0, 0, 1, 4, 1);
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndLiftingSize(fri, 2);

    var batches = try adapter.reconstruct(alloc, pcs, &roots, &capture);
    defer batches.deinit(alloc);
    try std.testing.expectEqual(@as(usize, 2), batches.by_height.len);
    try std.testing.expectEqual(@as(u32, 2), batches.by_height[0].column_log_size);
    try std.testing.expectEqual(@as(u32, 1), batches.by_height[1].column_log_size);
    for (batches.by_height) |batch| {
        try std.testing.expectEqual(@as(usize, 2), batch.column_count);
    }
    try std.testing.expectEqualSlices(usize, &raw, batches.by_height[0].projected_positions);
    try std.testing.expectEqualSlices(usize, &[_]usize{ 0, 1, 0, 0 },
                                      batches.by_height[1].projected_positions);
    const expected_high = [_]QM31{
        QM31.fromU32Unchecked(74, 0, 0, 0),
        QM31.fromU32Unchecked(82, 0, 0, 0),
        QM31.fromU32Unchecked(90, 0, 0, 0),
        QM31.fromU32Unchecked(74, 0, 0, 0),
    };
    const expected_low = [_]QM31{
        QM31.fromU32Unchecked(58, 0, 0, 0),
        QM31.fromU32Unchecked(66, 0, 0, 0),
        QM31.fromU32Unchecked(58, 0, 0, 0),
        QM31.fromU32Unchecked(58, 0, 0, 0),
    };
    for (expected_high, batches.by_height[0].original_values) |want, got|
        try std.testing.expect(want.eql(got));
    for (expected_low, batches.by_height[1].original_values) |want, got|
        try std.testing.expect(want.eql(got));

    // The adapter reauthenticates every independent root before batching.
    values[0] = M31.fromCanonical(20);
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        adapter.reconstruct(alloc, pcs, &roots, &capture));
    values[0] = M31.fromCanonical(2);
    siblings[3][0][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        adapter.reconstruct(alloc, pcs, &roots, &capture));
    siblings[3][0][0] ^= 1;
    positions[2][2] = 3;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        adapter.reconstruct(alloc, pcs, &roots, &capture));
    positions[2][2] = 2;
    roots[3][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture,
        adapter.reconstruct(alloc, pcs, &roots, &capture));
}
