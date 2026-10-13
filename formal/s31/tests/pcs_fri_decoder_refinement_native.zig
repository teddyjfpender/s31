//! Independent finite-domain refinement check for the pinned lifted Merkle
//! decoder. The expected paths come from a complete tree, never from the
//! verifier's capture or its compressed-witness decoding loop.
const std = @import("std");
const core = @import("stwo_core");
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Verifier = core.vcs_lifted.verifier.MerkleVerifierLifted(H);
const Capture = core.vcs_lifted.verifier.MerklePathCapture(H);
const M31 = core.fields.m31.M31;

const height = 3;
const leaves = 1 << height;

fn leaf(value: M31) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(&.{value});
    return hasher.finalize();
}

fn makeTree() [2 * leaves]H.Hash {
    var tree: [2 * leaves]H.Hash = undefined;
    for (0..leaves) |i| tree[leaves + i] = leaf(M31.fromCanonical(@intCast(17 + i)));
    var i: usize = leaves - 1;
    while (i != 0) : (i -= 1) {
        tree[i] = H.hashChildren(.{ .left = tree[2 * i], .right = tree[2 * i + 1] });
    }
    return tree;
}

// This oracle starts from a full, independently built tree. It emits a hash
// only when the queried frontier does not contain that node's sibling.
// Crucially, it does not use the native decoder's chunk or capture state.
fn encodeWitness(allocator: std.mem.Allocator, tree: *const [2 * leaves]H.Hash, mask: u8) ![]H.Hash {
    var result = std.ArrayList(H.Hash).empty;
    errdefer result.deinit(allocator);
    var active: [leaves]bool = undefined;
    for (0..leaves) |i| active[i] = (mask & (@as(u8, 1) << @intCast(i))) != 0;
    var width: usize = leaves;
    var base: usize = leaves;
    while (width > 1) {
        for (0..width) |i| {
            if (active[i] and !active[i ^ 1]) try result.append(allocator, tree[base + (i ^ 1)]);
        }
        for (0..width / 2) |i| active[i] = active[2 * i] or active[2 * i + 1];
        width /= 2;
        base /= 2;
    }
    return result.toOwnedSlice(allocator);
}

fn expectTreePath(tree: *const [2 * leaves]H.Hash, position: usize, path: []const H.Hash) !void {
    try std.testing.expectEqual(@as(usize, height), path.len);
    var index = leaves + position;
    for (path) |sibling| {
        try std.testing.expectEqualSlices(u8, &tree[index ^ 1], &sibling);
        index /= 2;
    }
    try std.testing.expectEqual(@as(usize, 1), index);
}

test "every nonempty eight-leaf query subset decodes to independent complete-tree paths" {
    const allocator = std.testing.allocator;
    const tree = makeTree();
    var verifier = try Verifier.init(allocator, tree[1], &.{height});
    defer verifier.deinit(allocator);

    for (1..256) |raw_mask| {
        const mask: u8 = @intCast(raw_mask);
        const witness = try encodeWitness(allocator, &tree, mask);
        defer allocator.free(witness);

        // Reverse the input order and duplicate the first query. The
        // compressed witness is independent of both choices.
        var positions: [leaves + 1]usize = undefined;
        var values: [leaves + 1]M31 = undefined;
        var count: usize = 0;
        var i: usize = leaves;
        while (i > 0) {
            i -= 1;
            if (mask & (@as(u8, 1) << @intCast(i)) == 0) continue;
            positions[count] = i;
            values[count] = M31.fromCanonical(@intCast(17 + i));
            count += 1;
        }
        positions[count] = positions[0];
        values[count] = values[0];
        count += 1;

        const columns = [_][]const M31{values[0..count]};
        var capture: Capture = undefined;
        try verifier.verifyWithPathCapture(
            allocator,
            positions[0..count],
            &columns,
            .{ .hash_witness = witness },
            &capture,
        );
        defer capture.deinit(allocator);
        try std.testing.expectEqual(@as(u32, height), capture.path_depth);
        try std.testing.expectEqualSlices(usize, positions[0..count], capture.positions);
        for (positions[0..count], 0..) |position, j| {
            try expectTreePath(&tree, position, capture.path(j));
        }
    }
}

test "native decoder hashes rows in log-size column order" {
    const allocator = std.testing.allocator;
    var tree: [2 * leaves]H.Hash = undefined;
    for (0..leaves) |i| {
        var hasher = H.defaultWithInitialState();
        // The caller supplies the high-log column first. The native decoder
        // sorts by log size, so the committed leaf is [low, high].
        hasher.updateLeaf(&.{
            M31.fromCanonical(@intCast(101 + 2 * (i / 4) + i % 2)),
            M31.fromCanonical(@intCast(17 + i)),
        });
        tree[leaves + i] = hasher.finalize();
    }
    var i: usize = leaves - 1;
    while (i != 0) : (i -= 1) {
        tree[i] = H.hashChildren(.{ .left = tree[2 * i], .right = tree[2 * i + 1] });
    }
    var verifier = try Verifier.init(allocator, tree[1], &.{ 3, 2 });
    defer verifier.deinit(allocator);
    const witness = try encodeWitness(allocator, &tree, 0b1000_1010);
    defer allocator.free(witness);
    const positions = [_]usize{ 7, 3, 1, 7 };
    const high = [_]M31{
        M31.fromCanonical(24), M31.fromCanonical(20), M31.fromCanonical(18), M31.fromCanonical(24),
    };
    const low = [_]M31{
        M31.fromCanonical(104), M31.fromCanonical(102), M31.fromCanonical(102), M31.fromCanonical(104),
    };
    const columns = [_][]const M31{ &high, &low };
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(
        allocator, &positions, &columns, .{ .hash_witness = witness }, &capture,
    );
    defer capture.deinit(allocator);
    for (positions, 0..) |position, j| try expectTreePath(&tree, position, capture.path(j));
}

test "malformed compressed witnesses and aliasing never publish a capture" {
    const allocator = std.testing.allocator;
    const tree = makeTree();
    var verifier = try Verifier.init(allocator, tree[1], &.{height});
    defer verifier.deinit(allocator);
    const witness = try encodeWitness(allocator, &tree, 0b1000_1010);
    defer allocator.free(witness);
    try std.testing.expect(witness.len > 1);

    const positions = [_]usize{ 7, 3, 1, 7 };
    const values = [_]M31{
        M31.fromCanonical(24), M31.fromCanonical(20), M31.fromCanonical(18), M31.fromCanonical(24),
    };
    const columns = [_][]const M31{&values};
    const sentinel = Capture{
        .positions = &.{},
        .path_depth = std.math.maxInt(u32),
        .siblings = &.{},
    };
    var capture = sentinel;

    try std.testing.expectError(error.WitnessTooShort, verifier.verifyWithPathCapture(
        allocator, &positions, &columns, .{ .hash_witness = witness[0 .. witness.len - 1] }, &capture,
    ));
    try std.testing.expectEqualDeep(sentinel, capture);

    var extra = try allocator.dupe(H.Hash, witness);
    defer allocator.free(extra);
    var extra_list = try allocator.alloc(H.Hash, extra.len + 1);
    defer allocator.free(extra_list);
    @memcpy(extra_list[0..extra.len], extra);
    extra_list[extra.len] = tree[2];
    try std.testing.expectError(error.WitnessTooLong, verifier.verifyWithPathCapture(
        allocator, &positions, &columns, .{ .hash_witness = extra_list }, &capture,
    ));
    try std.testing.expectEqualDeep(sentinel, capture);

    extra[0] = tree[1];
    try std.testing.expectError(error.RootMismatch, verifier.verifyWithPathCapture(
        allocator, &positions, &columns, .{ .hash_witness = extra }, &capture,
    ));
    try std.testing.expectEqualDeep(sentinel, capture);

    const inconsistent = [_]M31{
        M31.fromCanonical(24), M31.fromCanonical(20), M31.fromCanonical(18), M31.fromCanonical(25),
    };
    const inconsistent_columns = [_][]const M31{&inconsistent};
    try std.testing.expectError(error.DuplicateQueryMismatch, verifier.verifyWithPathCapture(
        allocator, &positions, &inconsistent_columns, .{ .hash_witness = witness }, &capture,
    ));
    try std.testing.expectEqualDeep(sentinel, capture);

    const out_of_range = [_]usize{ 7 + leaves, 3, 1, 7 + leaves };
    try std.testing.expectError(error.InvalidQueryShape, verifier.verifyWithPathCapture(
        allocator, &out_of_range, &columns, .{ .hash_witness = witness }, &capture,
    ));
    try std.testing.expectEqualDeep(sentinel, capture);
}
