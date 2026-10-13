//! General-height, complete-tree oracle checks for the pinned lifted Merkle
//! decoder. These are native differential tests, not a Zig-to-Lean proof.
const std = @import("std");
const core = @import("stwo_core");
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Verifier = core.vcs_lifted.verifier.MerkleVerifierLifted(H);
const Capture = core.vcs_lifted.verifier.MerklePathCapture(H);
const M31 = core.fields.m31.M31;

fn leaf(value: M31) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(&.{value});
    return hasher.finalize();
}

fn hashChildren(left: H.Hash, right: H.Hash) H.Hash {
    return H.hashChildren(.{ .left = left, .right = right });
}

fn valueAt(i: usize) M31 {
    return M31.fromCanonical(@intCast(1000 + i));
}

fn selected(i: usize, count: usize, mode: u8) bool {
    return switch (mode) {
        0 => i == count - 1,
        1 => i % 2 == 1 or count == 1,
        2 => true,
        3 => i % 7 == 0 or i == count - 1,
        else => unreachable,
    };
}

fn checkCase(comptime depth: usize, mode: u8) !void {
    const allocator = std.testing.allocator;
    const count: usize = 1 << depth;
    var tree: [2 * count]H.Hash = undefined;
    for (0..count) |i| tree[count + i] = leaf(valueAt(i));
    var parent: usize = count - 1;
    while (parent != 0) : (parent -= 1) {
        tree[parent] = hashChildren(tree[2 * parent], tree[2 * parent + 1]);
    }

    // Derive the compressed witness from the full tree's active set, without
    // reading the verifier's private frontier or its path capture.
    var active: [count]bool = undefined;
    for (0..count) |i| active[i] = selected(i, count, mode);
    var witness = std.ArrayList(H.Hash).empty;
    defer witness.deinit(allocator);
    var width: usize = count;
    var base: usize = count;
    while (width > 1) {
        for (0..width) |i| {
            if (active[i] and !active[i ^ 1]) {
                try witness.append(allocator, tree[base + (i ^ 1)]);
            }
        }
        for (0..width / 2) |i| active[i] = active[2 * i] or active[2 * i + 1];
        width /= 2;
        base /= 2;
    }

    // Deliberately reverse query order, then repeat two positions. The
    // witness is independent of caller order and duplicate multiplicity.
    var positions: [count + 2]usize = undefined;
    var values: [count + 2]M31 = undefined;
    var n: usize = 0;
    var i: usize = count;
    while (i > 0) {
        i -= 1;
        if (!selected(i, count, mode)) continue;
        positions[n] = i;
        values[n] = valueAt(i);
        n += 1;
    }
    try std.testing.expect(n > 0);
    positions[n] = positions[0];
    values[n] = values[0];
    n += 1;
    positions[n] = positions[n - 2];
    values[n] = values[n - 2];
    n += 1;

    var verifier = try Verifier.init(allocator, tree[1], &.{@as(u32, depth)});
    defer verifier.deinit(allocator);
    const columns = [_][]const M31{values[0..n]};
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(
        allocator, positions[0..n], &columns,
        .{ .hash_witness = witness.items }, &capture,
    );
    defer capture.deinit(allocator);
    try std.testing.expectEqual(@as(u32, depth), capture.path_depth);
    try std.testing.expectEqualSlices(usize, positions[0..n], capture.positions);
    for (positions[0..n], 0..) |position, j| {
        const path = capture.path(j);
        try std.testing.expectEqual(@as(usize, depth), path.len);
        var node = count + position;
        for (path) |sibling| {
            try std.testing.expectEqualSlices(u8, &tree[node ^ 1], &sibling);
            node /= 2;
        }
        try std.testing.expectEqual(@as(usize, 1), node);
    }
    try std.testing.expectEqualSlices(u8, std.mem.sliceAsBytes(capture.path(0)),
        std.mem.sliceAsBytes(capture.path(n - 2)));
    try std.testing.expectEqualSlices(u8, std.mem.sliceAsBytes(capture.path(n - 3)),
        std.mem.sliceAsBytes(capture.path(n - 1)));

    // All failure branches must leave the caller's capture untouched.
    const sentinel = Capture{
        .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{},
    };
    var failed = sentinel;
    values[n - 2] = M31.fromCanonical(42);
    try std.testing.expectError(error.DuplicateQueryMismatch,
        verifier.verifyWithPathCapture(allocator, positions[0..n], &columns,
            .{ .hash_witness = witness.items }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    values[n - 2] = values[0];

    positions[0] = count; // First index beyond the declared tree domain.
    try std.testing.expectError(error.InvalidQueryShape,
        verifier.verifyWithPathCapture(allocator, positions[0..n], &columns,
            .{ .hash_witness = witness.items }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    positions[0] = positions[n - 2];

    const short_columns = [_][]const M31{values[0 .. n - 1]};
    try std.testing.expectError(error.InvalidQueryShape,
        verifier.verifyWithPathCapture(allocator, positions[0..n], &short_columns,
            .{ .hash_witness = witness.items }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);

    if (witness.items.len != 0) {
        try std.testing.expectError(error.WitnessTooShort,
            verifier.verifyWithPathCapture(allocator, positions[0..n], &columns,
                .{ .hash_witness = witness.items[0 .. witness.items.len - 1] }, &failed));
        try std.testing.expectEqualDeep(sentinel, failed);

        const original = witness.items[0];
        witness.items[0] = leaf(M31.fromCanonical(777));
        try std.testing.expectError(error.RootMismatch,
            verifier.verifyWithPathCapture(allocator, positions[0..n], &columns,
                .{ .hash_witness = witness.items }, &failed));
        try std.testing.expectEqualDeep(sentinel, failed);
        witness.items[0] = original;
    }
    try witness.append(allocator, leaf(M31.fromCanonical(778)));
    try std.testing.expectError(error.WitnessTooLong,
        verifier.verifyWithPathCapture(allocator, positions[0..n], &columns,
            .{ .hash_witness = witness.items }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
}

test "complete-tree oracle refines captures at heights zero through six" {
    inline for (.{ 0, 1, 2, 4, 6 }) |depth| {
        for (0..4) |mode| try checkCase(depth, @intCast(mode));
    }
}

test "word-width height accepts the maximal usize position without shift wrap" {
    const allocator = std.testing.allocator;
    const depth = @bitSizeOf(usize);
    const position: usize = std.math.maxInt(usize);
    const value = M31.fromCanonical(123);
    var witnesses: [depth]H.Hash = undefined;
    var root = leaf(value);
    var index: usize = position;
    for (&witnesses, 0..) |*sibling, layer| {
        sibling.* = leaf(M31.fromCanonical(@intCast(200 + layer)));
        root = if (index & 1 == 0)
            hashChildren(root, sibling.*)
        else
            hashChildren(sibling.*, root);
        index >>= 1;
    }
    try std.testing.expectEqual(@as(usize, 0), index);
    var verifier = try Verifier.initWithHeight(allocator, root, &.{0}, depth);
    defer verifier.deinit(allocator);
    const positions = [_]usize{ position, position };
    const values = [_]M31{ value, value };
    const columns = [_][]const M31{&values};
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(allocator, &positions, &columns,
        .{ .hash_witness = &witnesses }, &capture);
    defer capture.deinit(allocator);
    try std.testing.expectEqual(@as(u32, depth), capture.path_depth);
    for (0..2) |j| {
        try std.testing.expectEqualSlices(u8, std.mem.sliceAsBytes(&witnesses),
            std.mem.sliceAsBytes(capture.path(j)));
    }
}

test "empty-tree placeholder has an owned empty capture and rejects stray proof data" {
    const allocator = std.testing.allocator;
    const root = leaf(M31.fromCanonical(1));
    var verifier = try Verifier.init(allocator, root, &.{});
    defer verifier.deinit(allocator);
    const no_columns = [_][]const M31{};
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(allocator, &.{}, &no_columns,
        .{ .hash_witness = &.{} }, &capture);
    defer capture.deinit(allocator);
    try std.testing.expectEqual(@as(u32, 0), capture.path_depth);
    try std.testing.expectEqual(@as(usize, 0), capture.positions.len);
    try std.testing.expectEqual(@as(usize, 0), capture.siblings.len);

    const sentinel = Capture{
        .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{},
    };
    var failed = sentinel;
    try std.testing.expectError(error.InvalidQueryShape,
        verifier.verifyWithPathCapture(allocator, &.{0}, &no_columns,
            .{ .hash_witness = &.{} }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    var extra = [_]H.Hash{root};
    try std.testing.expectError(error.WitnessTooLong,
        verifier.verifyWithPathCapture(allocator, &.{}, &no_columns,
            .{ .hash_witness = &extra }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
}

test "three-column projected rows keep native log-size and tie order" {
    const allocator = std.testing.allocator;
    const depth = 4;
    const count = 1 << depth;
    var tree: [2 * count]H.Hash = undefined;
    for (0..count) |i| {
        // Logs are [4, 2, 4], so the native leaf order is [column 1,
        // column 0, column 2]. The short column is projected to its
        // circle-domain index before its value enters the committed row.
        const projected = 2 * (i / 8) + i % 2;
        var hasher = H.defaultWithInitialState();
        hasher.updateLeaf(&.{
            M31.fromCanonical(@intCast(300 + projected)),
            M31.fromCanonical(@intCast(100 + i)),
            M31.fromCanonical(@intCast(200 + i)),
        });
        tree[count + i] = hasher.finalize();
    }
    var parent: usize = count - 1;
    while (parent != 0) : (parent -= 1)
        tree[parent] = hashChildren(tree[2 * parent], tree[2 * parent + 1]);

    const selected_positions = [_]usize{ 1, 4, 9, 15 };
    var active: [count]bool = @splat(false);
    for (selected_positions) |position| active[position] = true;
    var witness = std.ArrayList(H.Hash).empty;
    defer witness.deinit(allocator);
    var width: usize = count;
    var base: usize = count;
    while (width > 1) {
        for (0..width) |i| {
            if (active[i] and !active[i ^ 1])
                try witness.append(allocator, tree[base + (i ^ 1)]);
        }
        for (0..width / 2) |i| active[i] = active[2 * i] or active[2 * i + 1];
        width /= 2;
        base /= 2;
    }

    const positions = [_]usize{ 15, 9, 4, 1, 9 };
    var values: [3][positions.len]M31 = undefined;
    for (positions, 0..) |position, j| {
        values[0][j] = M31.fromCanonical(@intCast(100 + position));
        values[1][j] = M31.fromCanonical(@intCast(300 + 2 * (position / 8) + position % 2));
        values[2][j] = M31.fromCanonical(@intCast(200 + position));
    }
    const columns = [_][]const M31{ &values[0], &values[1], &values[2] };
    var verifier = try Verifier.init(allocator, tree[1], &.{ 4, 2, 4 });
    defer verifier.deinit(allocator);
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(allocator, &positions, &columns,
        .{ .hash_witness = witness.items }, &capture);
    defer capture.deinit(allocator);
    for (positions, 0..) |position, j| {
        var node = count + position;
        for (capture.path(j)) |sibling| {
            try std.testing.expectEqualSlices(u8, &tree[node ^ 1], &sibling);
            node /= 2;
        }
        try std.testing.expectEqual(@as(usize, 1), node);
    }
    try std.testing.expectEqualSlices(u8, std.mem.sliceAsBytes(capture.path(1)),
        std.mem.sliceAsBytes(capture.path(4)));

    const sentinel = Capture{
        .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{},
    };
    var failed = sentinel;
    for (0..3) |column| {
        const original = values[column][4];
        values[column][4] = M31.fromCanonical(@intCast(700 + column));
        try std.testing.expectError(error.DuplicateQueryMismatch,
            verifier.verifyWithPathCapture(allocator, &positions, &columns,
                .{ .hash_witness = witness.items }, &failed));
        try std.testing.expectEqualDeep(sentinel, failed);
        values[column][4] = original;
    }
    const original = values[1][0];
    values[1][0] = M31.fromCanonical(711);
    try std.testing.expectError(error.RootMismatch,
        verifier.verifyWithPathCapture(allocator, &positions, &columns,
            .{ .hash_witness = witness.items }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    values[1][0] = original;
}

const ToyHasher = struct {
    state: u64 = 0,
    pub const Hash = u64;
    pub const Children = struct { left: Hash, right: Hash };
    const Self = @This();

    pub fn defaultWithInitialState() Self {
        return .{};
    }
    pub fn updateLeaf(self: *Self, row: []const M31) void {
        for (row) |word| self.state += word.v;
    }
    pub fn finalize(self: Self) Hash {
        return self.state;
    }
    pub fn hashChildren(children: Children) Hash {
        return 100 * children.left + children.right;
    }
};

test "native parser and caller copy agree with executable Lean toy vector" {
    // MultiproofRawQueries.lean evaluates the same leaf/parent arithmetic,
    // queries, root, compressed witness, and caller-ordered full paths.
    const allocator = std.testing.allocator;
    const ToyVerifier = core.vcs_lifted.verifier.MerkleVerifierLifted(ToyHasher);
    const ToyCapture = core.vcs_lifted.verifier.MerklePathCapture(ToyHasher);
    var verifier = try ToyVerifier.init(allocator, 1011, &.{1});
    defer verifier.deinit(allocator);
    const positions = [_]usize{ 1, 0, 1 };
    const values = [_]M31{
        M31.fromCanonical(11), M31.fromCanonical(10), M31.fromCanonical(11),
    };
    const columns = [_][]const M31{&values};
    var capture: ToyCapture = undefined;
    try verifier.verifyWithPathCapture(allocator, &positions, &columns,
        .{ .hash_witness = &.{} }, &capture);
    defer capture.deinit(allocator);
    try std.testing.expectEqualSlices(usize, &positions, capture.positions);
    try std.testing.expectEqualSlices(u64, &.{10}, capture.path(0));
    try std.testing.expectEqualSlices(u64, &.{11}, capture.path(1));
    try std.testing.expectEqualSlices(u64, &.{10}, capture.path(2));

    const sentinel = ToyCapture{
        .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{},
    };
    var failed = sentinel;
    const conflicting = [_]M31{
        M31.fromCanonical(11), M31.fromCanonical(10), M31.fromCanonical(12),
    };
    const conflicting_columns = [_][]const M31{&conflicting};
    try std.testing.expectError(error.DuplicateQueryMismatch,
        verifier.verifyWithPathCapture(allocator, &positions, &conflicting_columns,
            .{ .hash_witness = &.{} }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    const out_of_domain = [_]usize{3};
    const lone = [_]M31{M31.fromCanonical(11)};
    const lone_columns = [_][]const M31{&lone};
    try std.testing.expectError(error.InvalidQueryShape,
        verifier.verifyWithPathCapture(allocator, &out_of_domain, &lone_columns,
            .{ .hash_witness = &.{} }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
    try std.testing.expectError(error.WitnessTooShort,
        verifier.verifyWithPathCapture(allocator, &.{1}, &lone_columns,
            .{ .hash_witness = &.{} }, &failed));
    try std.testing.expectEqualDeep(sentinel, failed);
}
