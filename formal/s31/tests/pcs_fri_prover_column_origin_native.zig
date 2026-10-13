//! Source-bound finite bridge from the actual pinned lifted prover to the
//! projected-row complete-tree model. This is not a proof of arbitrary Zig
//! executions or of BLAKE2s collision resistance.
const std = @import("std");
const core = @import("stwo_core");
const prover_engine = @import("stwo_prover_engine");
const CpuBackend = @import("stwo_cpu_backend").configured(.{ .wide_preparation = true });

const M31 = core.fields.m31.M31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Prover = prover_engine.vcs_lifted.prover.MerkleProverLifted(H);
const Verifier = core.vcs_lifted.verifier.MerkleVerifierLifted(H);
const Capture = core.vcs_lifted.verifier.MerklePathCapture(H);

comptime {
    if (CpuBackend.MerkleTree(H) != Prover)
        @compileError("S31 CPU Merkle backend no longer uses the reviewed lifted prover");
}

fn projectedIndex(height: u32, column_log: u32, position: usize) usize {
    const shift: std.math.Log2Int(usize) = @intCast(height - column_log + 1);
    return 2 * (position >> shift) + position % 2;
}

fn leaf(row: []const M31) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(row);
    return hasher.finalize();
}

fn parent(left: H.Hash, right: H.Hash) H.Hash {
    return H.hashChildren(.{ .left = left, .right = right });
}

fn checkActualCommitment(height: u32, constant_columns: bool) !void {
    const allocator = std.testing.allocator;
    var long_a: [16]M31 = undefined;
    var short: [4]M31 = undefined;
    var long_b: [16]M31 = undefined;
    for (&long_a, 0..) |*value, i| value.* = M31.fromCanonical(
        @intCast(if (constant_columns) 17 else 100 + i),
    );
    for (&short, 0..) |*value, i| value.* = M31.fromCanonical(
        @intCast(if (constant_columns) 23 else 300 + i),
    );
    for (&long_b, 0..) |*value, i| value.* = M31.fromCanonical(
        @intCast(if (constant_columns) 29 else 500 + i),
    );
    // Caller order differs from Merkle row order. Equal-log columns retain
    // their original relative order: [short, long_a, long_b].
    const columns = [_][]const M31{ &long_a, &short, &long_b };
    const logs = [_]u32{ 4, 2, 4 };
    const count: usize = @as(usize, 1) << @intCast(height);

    var committed = try Prover.commitLifted(allocator, &columns, height);
    defer committed.deinit(allocator);
    try std.testing.expectEqual(height, committed.maxLogSize());
    var lifted_after_commit = try Prover.commit(allocator, &columns);
    defer lifted_after_commit.deinit(allocator);
    try lifted_after_commit.liftTo(allocator, height);
    try std.testing.expectEqualDeep(committed.root(), lifted_after_commit.root());
    var backend_tree = try CpuBackend.commitMerkle(H, allocator, &columns);
    defer backend_tree.deinit(allocator);
    try backend_tree.liftTo(allocator, height);
    try std.testing.expectEqualDeep(committed.root(), backend_tree.root());

    // Build all leaves and parents independently from projected source
    // columns. Inspect every retained prover node, not only the public root.
    var oracle: [64]H.Hash = undefined;
    for (0..count) |position| {
        const row = [_]M31{
            short[projectedIndex(height, 2, position)],
            long_a[projectedIndex(height, 4, position)],
            long_b[projectedIndex(height, 4, position)],
        };
        oracle[count + position] = leaf(&row);
        try std.testing.expectEqualDeep(oracle[count + position],
            committed.layers[height][position]);
        try std.testing.expectEqualDeep(oracle[count + position],
            lifted_after_commit.layers[height][position]);
        try std.testing.expectEqualDeep(oracle[count + position],
            backend_tree.layers[height][position]);
    }
    var node = count - 1;
    while (node != 0) : (node -= 1)
        oracle[node] = parent(oracle[2 * node], oracle[2 * node + 1]);
    for (0..height + 1) |level| {
        const level_count = @as(usize, 1) << @intCast(level);
        for (0..level_count) |j|
            try std.testing.expectEqualDeep(oracle[level_count + j],
                committed.layers[level][j]);
        for (0..level_count) |j|
            try std.testing.expectEqualDeep(oracle[level_count + j],
                lifted_after_commit.layers[level][j]);
    }
    try std.testing.expectEqualDeep(oracle[1], committed.root());

    // A row with the same values in caller column order authenticates a
    // different root for these fixtures. This controls the sorting premise.
    if (!constant_columns) {
        const wrong_row = [_]M31{
            long_a[projectedIndex(height, 4, 1)],
            short[projectedIndex(height, 2, 1)],
            long_b[projectedIndex(height, 4, 1)],
        };
        try std.testing.expect(!std.mem.eql(u8, &leaf(&wrong_row),
            &oracle[count + 1]));
    }

    const positions: []const usize = if (height == 5)
        &.{ 31, 23, 10, 5, 23 }
    else
        &.{ 15, 9, 4, 1, 9 };
    var opened = try committed.decommit(allocator, positions, &columns);
    defer opened.deinit(allocator);
    for (columns, opened.queried_values, logs) |column, values, log_size| {
        for (positions, values) |position, value|
            try std.testing.expectEqualDeep(
                column[projectedIndex(height, log_size, position)], value);
    }

    var verifier = try Verifier.initWithHeight(allocator, committed.root(), &logs, height);
    defer verifier.deinit(allocator);
    const queried: []const []const M31 = @ptrCast(opened.queried_values);
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(allocator, positions, queried,
        opened.decommitment.decommitment, &capture);
    defer capture.deinit(allocator);
    try std.testing.expectEqualSlices(usize, positions, capture.positions);
    for (positions, 0..) |position, slot| {
        var at = count + position;
        for (capture.path(slot)) |sibling| {
            try std.testing.expectEqualDeep(oracle[at ^ 1], sibling);
            at /= 2;
        }
        try std.testing.expectEqual(@as(usize, 1), at);
    }

    const sentinel = Capture{
        .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{},
    };
    var failed = sentinel;
    var wrong_root = committed.root();
    wrong_root[0] ^= 1;
    var wrong_root_verifier = try Verifier.initWithHeight(
        allocator, wrong_root, &logs, height,
    );
    defer wrong_root_verifier.deinit(allocator);
    try std.testing.expectError(error.RootMismatch,
        wrong_root_verifier.verifyWithPathCapture(allocator, positions, queried,
            opened.decommitment.decommitment, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);

    if (!constant_columns) {
        // A wrong projection at a unique query changes the authenticated
        // leaf while leaving the compressed witness and public root fixed.
        const original = opened.queried_values[1][0];
        opened.queried_values[1][0] = short[0];
        try std.testing.expect(!original.eql(opened.queried_values[1][0]));
        try std.testing.expectError(error.RootMismatch,
            verifier.verifyWithPathCapture(allocator, positions, queried,
                opened.decommitment.decommitment, &failed));
        try std.testing.expectEqualDeep(sentinel, failed);
        opened.queried_values[1][0] = original;

        // The verifier must use the same log-size sort as the prover. This
        // mutant changes only the sort metadata, not the proof or values.
        var wrong_logs_verifier = try Verifier.initWithHeight(
            allocator, committed.root(), &.{ 4, 4, 2 }, height,
        );
        defer wrong_logs_verifier.deinit(allocator);
        try std.testing.expectError(error.RootMismatch,
            wrong_logs_verifier.verifyWithPathCapture(allocator, positions, queried,
                opened.decommitment.decommitment, &failed));
        try std.testing.expectEqualDeep(sentinel, failed);
    }
}

test "actual lifted prover leaves and root equal the projected-column model" {
    try checkActualCommitment(4, false); // natural height
    try checkActualCommitment(5, false); // explicit lift above max column
    try checkActualCommitment(5, true); // constant-column fast path
}
