//! Finite source-bound bridge for S31's compact CPU commitment routes.
//! The expected extended values come from barycentric evaluation of the
//! original source columns, independently of either committer's FFT/tile code.
//! This is not a proof of arbitrary Zig execution or hash collision resistance.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const Cpu = @import("stwo_cpu_backend").configured(.{ .wide_preparation = true });

const M31 = core.fields.m31.M31;
const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
const H = Profile.MerkleHasher;
const Channel = Profile.Channel;
const Scheme = prover.pcs.CommitmentSchemeProver(Cpu, H, Profile);
const Column = prover.pcs.ColumnEvaluation;
const CircleEvaluation = prover.poly.circle.CircleEvaluation;
const CircleCoefficients = prover.poly.circle.CircleCoefficients;
const CanonicCoset = prover.poly.circle.CanonicCoset;
const Verifier = core.vcs_lifted.verifier.MerkleVerifierLifted(H);
const Capture = core.vcs_lifted.verifier.MerklePathCapture(H);

comptime {
    if (H != core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher or
        Channel != core.channel.blake2s.Blake2sM31Channel)
        @compileError("compact origin fixture must use S31's native profile");
}

fn leaf(row: []const M31) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(row);
    return hasher.finalize();
}

fn project(height: u32, log: u32, position: usize) usize {
    return 2 * (position >> @intCast(height - log + 1)) + (position & 1);
}

fn sourceColumn(allocator: std.mem.Allocator, log: u32, salt: usize) !Column {
    const values = try allocator.alloc(M31, @as(usize, 1) << @intCast(log));
    for (values, 0..) |*value, i|
        value.* = M31.fromU64(101 + salt * 1_000_003 + i * i * 7919 + i * 31);
    return .{ .log_size = log, .values = values };
}

fn ownedCopy(allocator: std.mem.Allocator, sources: []const Column) ![]Column {
    const copy = try allocator.alloc(Column, sources.len);
    var filled: usize = 0;
    errdefer {
        for (copy[0..filled]) |column| allocator.free(column.values);
        allocator.free(copy);
    }
    for (sources, copy) |source, *destination| {
        destination.* = .{ .log_size = source.log_size, .values = try allocator.dupe(M31, source.values) };
        filled += 1;
    }
    return copy;
}

fn expectedExtension(allocator: std.mem.Allocator, source: Column, blowup: u32) ![]M31 {
    const source_domain = CanonicCoset.new(source.log_size).circleDomain();
    const evaluation = try CircleEvaluation.init(source_domain, source.values);
    const log = source.log_size + blowup;
    const extended_domain = CanonicCoset.new(log).circleDomain();
    const result = try allocator.alloc(M31, extended_domain.size());
    errdefer allocator.free(result);
    for (result, 0..) |*value, index| {
        const point = extended_domain.at(core.utils.bitReverseIndex(index, log));
        const answer = try evaluation.evalAtPoint(allocator, .{
            .x = core.fields.qm31.QM31.fromBase(point.x),
            .y = core.fields.qm31.QM31.fromBase(point.y),
        });
        const coords = answer.toM31Array();
        try std.testing.expect(coords[1].eql(M31.zero()) and
            coords[2].eql(M31.zero()) and coords[3].eql(M31.zero()));
        value.* = coords[0];
    }
    return result;
}

fn checkRetention(allocator: std.mem.Allocator, tree: anytype, sources: []const Column, extensions: []const []M31, compact_min_log: u32) !void {
    try std.testing.expect(tree.compact_polynomials);
    try std.testing.expectEqual(sources.len, tree.columns.len);
    const coefficients = tree.coefficients orelse return error.MissingCoefficients;
    try std.testing.expectEqual(sources.len, coefficients.len);
    for (sources, tree.columns, coefficients, extensions) |source, retained, coefficient, expected| {
        const log = source.log_size + 1;
        try std.testing.expectEqual(log, retained.log_size);
        try std.testing.expectEqual(source.log_size, coefficient.logSize());
        const polynomial = try CircleCoefficients.initBorrowed(coefficient.coefficients());
        const evaluated = try polynomial.evaluate(allocator, CanonicCoset.new(log).circleDomain());
        defer allocator.free(@constCast(evaluated.values));
        try std.testing.expectEqualSlices(M31, expected, evaluated.values);
        if (log >= compact_min_log) {
            try std.testing.expectEqual(@as(usize, 0), retained.values.len);
            try std.testing.expectEqualSlices(M31, coefficient.coefficients(), retained.coefficient_values orelse return error.MissingCoefficientView);
            try std.testing.expect(retained.coefficient_values.?.ptr == coefficient.coefficients().ptr);
            try std.testing.expect(retained.coefficient_values.?.ptr != source.values.ptr);
        } else {
            try std.testing.expectEqualSlices(M31, expected, retained.values);
            try std.testing.expect(retained.coefficient_values == null);
            try std.testing.expect(retained.values.ptr != source.values.ptr);
        }
    }
}

fn checkCommitment(allocator: std.mem.Allocator, tree: anytype, extensions: []const []M31, logs: []const u32, height: u32) !void {
    const count = @as(usize, 1) << @intCast(height);
    const nodes = try allocator.alloc(H.Hash, 2 * count);
    defer allocator.free(nodes);
    const row = try allocator.alloc(M31, extensions.len);
    defer allocator.free(row);
    // The fixture's ascending height order is [1, 3, 4, 5, 0, 2].
    // Equal-height columns 0 and 2 retain caller order.
    const order = [_]usize{ 1, 3, 4, 5, 0, 2 };
    for (0..count) |position| {
        for (order, 0..) |original, slot|
            row[slot] = extensions[original][project(height, logs[original], position)];
        nodes[count + position] = leaf(row);
    }
    // Equal-height columns use caller order. Swapping them must change a leaf.
    try std.testing.expect(!row[4].eql(row[5]));
    std.mem.swap(M31, &row[4], &row[5]);
    try std.testing.expect(!std.mem.eql(u8, &leaf(row), &nodes[2 * count - 1]));
    var i = count - 1;
    while (i > 0) : (i -= 1)
        nodes[i] = H.hashChildren(.{ .left = nodes[2 * i], .right = nodes[2 * i + 1] });
    try std.testing.expectEqualDeep(nodes[1], tree.root());
    try std.testing.expectEqual(height, tree.commitment.maxLogSize());
    for (0..height + 1) |level| {
        const width = @as(usize, 1) << @intCast(level);
        try std.testing.expectEqualSlices(u8, std.mem.sliceAsBytes(nodes[width .. 2 * width]), std.mem.sliceAsBytes(tree.commitment.layers[level]));
    }

    const positions = [_]usize{ count - 1, 3, count / 2 + 1, 0, 3 };
    var opening = try tree.decommit(allocator, &positions);
    defer opening.deinit(allocator);
    for (opening.queried_values, extensions, logs) |values, extension, log| {
        for (&positions, values) |position, got|
            try std.testing.expectEqualDeep(extension[project(height, log, position)], got);
    }
    const queried: []const []const M31 = @ptrCast(opening.queried_values);
    var verifier = try Verifier.initWithHeight(allocator, tree.root(), logs, height);
    defer verifier.deinit(allocator);
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(allocator, &positions, queried, opening.decommitment.decommitment, &capture);
    defer capture.deinit(allocator);
    for (&positions, 0..) |position, slot| {
        var node = count + position;
        for (capture.path(slot)) |sibling| {
            try std.testing.expectEqualDeep(nodes[node ^ 1], sibling);
            node /= 2;
        }
        try std.testing.expectEqual(@as(usize, 1), node);
    }

    var wrong_root = tree.root();
    wrong_root[0] ^= 1;
    var wrong_verifier = try Verifier.initWithHeight(allocator, wrong_root, logs, height);
    defer wrong_verifier.deinit(allocator);
    var failed: Capture = undefined;
    try std.testing.expectError(error.RootMismatch, wrong_verifier.verifyWithPathCapture(allocator, &positions, queried, opening.decommitment.decommitment, &failed));
    const original = opening.queried_values[1][2];
    opening.queried_values[1][2] = extensions[1][project(height, logs[1], positions[2] ^ 1)];
    try std.testing.expect(!original.eql(opening.queried_values[1][2]));
    try std.testing.expectError(error.RootMismatch, verifier.verifyWithPathCapture(allocator, &positions, queried, opening.decommitment.decommitment, &failed));
    opening.queried_values[1][2] = original;
    const duplicate_original = opening.queried_values[1][4];
    opening.queried_values[1][4] = M31.fromCanonical(123456);
    try std.testing.expect(!duplicate_original.eql(opening.queried_values[1][4]));
    try std.testing.expectError(error.DuplicateQueryMismatch, verifier.verifyWithPathCapture(allocator, &positions, queried, opening.decommitment.decommitment, &failed));
    opening.queried_values[1][4] = duplicate_original;
    const wrong_logs = [_]u32{ logs[0], logs[2], logs[1], logs[3], logs[4], logs[5] };
    var wrong_order_verifier = try Verifier.initWithHeight(allocator, tree.root(), &wrong_logs, height);
    defer wrong_order_verifier.deinit(allocator);
    try std.testing.expectError(error.RootMismatch, wrong_order_verifier.verifyWithPathCapture(allocator, &positions, queried, opening.decommitment.decommitment, &failed));
}

test "S31 compact tiled and streaming retained columns originate in source evaluations" {
    const allocator = std.testing.allocator;
    const source_logs = [_]u32{ 9, 3, 9, 5, 7, 8 };
    const blowup: u32 = 1;
    const compact_min_log: u32 = 6;
    const height: u32 = 11;
    const config = core.pcs.config_v2.PcsConfigV2.fromFriAndLiftingSize(try core.pcs.config_v2.FriConfigV2.init(0, 0, blowup, 8, 1), height);
    var sources: [source_logs.len]Column = undefined;
    var extensions: [source_logs.len][]M31 = undefined;
    var extended_logs: [source_logs.len]u32 = undefined;
    var filled: usize = 0;
    defer {
        for (sources[0..filled], extensions[0..filled]) |source, extension| {
            allocator.free(source.values);
            allocator.free(extension);
        }
    }
    for (&sources, &extensions, &extended_logs, source_logs, 0..) |*source, *extension, *extended_log, log, slot| {
        source.* = try sourceColumn(allocator, log, slot);
        extension.* = try expectedExtension(allocator, source.*, blowup);
        extended_log.* = log + blowup;
        filled += 1;
    }
    try std.testing.expect(prover.pcs.tiled_commit.applies(&sources, blowup, compact_min_log));

    var tiled = try Scheme.initRevision(allocator, config);
    defer tiled.deinit(allocator);
    tiled.setCompactPolynomialStorage(compact_min_log);
    var tiled_channel = Channel{};
    try prover.pcs.tiled_commit.commit(Cpu, H, &tiled, allocator, &sources, .borrowed, .{ .tile_bytes = 1 << 10, .group_bytes = 1 << 12 }, &tiled_channel);
    var streaming = try Scheme.initRevision(allocator, config);
    defer streaming.deinit(allocator);
    streaming.setCompactPolynomialStorage(compact_min_log);
    var streaming_channel = Channel{};
    try streaming.commitBorrowedStreamingWithRecorder(allocator, &sources, 0, null, &streaming_channel);
    try std.testing.expectEqualSlices(u8, &tiled_channel.digestBytes(), &streaming_channel.digestBytes());
    var owned_tiled = try Scheme.initRevision(allocator, config);
    defer owned_tiled.deinit(allocator);
    owned_tiled.setCompactPolynomialStorage(compact_min_log);
    var owned_tiled_channel = Channel{};
    // This is the owned path selected by S31's `prove.zig` for its
    // interaction and composition trees. The committer consumes the copy.
    try prover.pcs.tiled_commit.commit(Cpu, H, &owned_tiled, allocator, try ownedCopy(allocator, &sources), .owned, .{ .tile_bytes = 1 << 10, .group_bytes = 1 << 12 }, &owned_tiled_channel);
    try std.testing.expectEqualSlices(u8, &tiled_channel.digestBytes(), &owned_tiled_channel.digestBytes());
    const tiled_tree = tiled.trees.items[0];
    const streaming_tree = streaming.trees.items[0];
    const owned_tiled_tree = owned_tiled.trees.items[0];
    try checkRetention(allocator, tiled_tree, &sources, &extensions, compact_min_log);
    try checkRetention(allocator, streaming_tree, &sources, &extensions, compact_min_log);
    try checkRetention(allocator, owned_tiled_tree, &sources, &extensions, compact_min_log);
    try checkCommitment(allocator, tiled_tree, &extensions, &extended_logs, height);
    try checkCommitment(allocator, streaming_tree, &extensions, &extended_logs, height);
    try checkCommitment(allocator, owned_tiled_tree, &extensions, &extended_logs, height);
}
