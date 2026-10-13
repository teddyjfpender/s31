//! Concrete witness extraction for the symbolic MerkleOpening collision theorem.
const std = @import("std");
const core = @import("stwo_core");
const reduction = @import("pcs_merkle_collision_reduction");
const M31 = core.fields.m31.M31;

const Toy = struct {
    pub const Hash = u8;
    pub const Children = struct { left: Hash, right: Hash };
    state: u8 = 0,

    pub fn defaultWithInitialState() Toy {
        return .{};
    }
    pub fn updateLeaf(self: *Toy, row: []const M31) void {
        for (row) |value| self.state +%= @truncate(value.v);
    }
    pub fn finalize(self: Toy) Hash {
        return self.state;
    }
    pub fn hashChildren(pair: Children) Hash {
        return pair.left ^ pair.right;
    }
};

const R = reduction.Reduction(Toy);
const Real = reduction.Reduction(core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher);

test "distinct accepted leaf messages produce an explicit leaf collision" {
    const first = [_]M31{M31.fromCanonical(1)};
    const second = [_]M31{M31.fromCanonical(257)};
    const collision = try R.extract(1, 0, 0, &first, &.{}, &second, &.{});
    try std.testing.expect(R.check(collision));
    switch (collision) {
        .leaf => |leaf| {
            try std.testing.expectEqual(@as(u8, 1), leaf.digest);
            var changed = collision;
            changed.leaf.digest = 2;
            try std.testing.expect(!R.check(changed));
        },
        else => return error.WrongCollisionKind,
    }
}

test "distinct accepted child pairs produce an explicit parent collision" {
    const first = [_]M31{M31.fromCanonical(1)};
    const second = [_]M31{M31.fromCanonical(2)};
    const collision = try R.extract(4, 1, 0, &first, &.{5}, &second, &.{6});
    try std.testing.expect(R.check(collision));
    switch (collision) {
        .parent => |parent| {
            try std.testing.expectEqual(@as(usize, 0), parent.level);
            try std.testing.expectEqual(@as(u8, 1), parent.first_children.left);
            try std.testing.expectEqual(@as(u8, 5), parent.first_children.right);
            try std.testing.expectEqual(@as(u8, 2), parent.second_children.left);
            try std.testing.expectEqual(@as(u8, 6), parent.second_children.right);
            var changed = collision;
            changed.parent.second_children.right = 7;
            try std.testing.expect(!R.check(changed));
        },
        else => return error.WrongCollisionKind,
    }
}

test "malformed paths, out-of-domain aliases, noncanonical rows and equal rows reject" {
    const first = [_]M31{M31.fromCanonical(1)};
    const second = [_]M31{M31.fromCanonical(2)};
    try std.testing.expectError(error.InvalidOpening,
        R.extract(4, 1, 2, &first, &.{5}, &second, &.{6}));
    try std.testing.expectError(error.InvalidOpening,
        R.extract(4, 1, 0, &first, &.{}, &second, &.{6}));
    try std.testing.expectError(error.InvalidOpening,
        R.extract(4, 1, 0, &first, &.{5}, &second, &.{7}));
    const malformed = [_]M31{.{ .v = core.fields.m31.Modulus }};
    try std.testing.expectError(error.InvalidOpening,
        R.extract(1, 0, 0, &malformed, &.{}, &first, &.{}));
    try std.testing.expectError(error.SameRow,
        R.extract(1, 0, 0, &first, &.{}, &first, &.{}));
    const longer = [_]M31{ first[0], M31.zero() };
    try std.testing.expectError(error.InvalidOpening,
        R.extract(1, 0, 0, &first, &.{}, &longer, &.{}));
}

test "duplicate audit rejects changed rows and paths as well as malformed shapes" {
    const one = [_]M31{M31.fromCanonical(1)};
    const two = [_]M31{M31.fromCanonical(2)};
    const changed = [_]M31{M31.fromCanonical(3)};
    const positions = [_]usize{ 1, 0, 1 };
    const rows = [_][]const M31{ &two, &one, &two };
    const paths = [_][]const Toy.Hash{ &.{7}, &.{8}, &.{7} };
    try R.auditDuplicateQueries(1, &positions, &rows, &paths);
    const wrong_row = [_][]const M31{ &two, &one, &changed };
    try std.testing.expectError(error.DuplicateMismatch,
        R.auditDuplicateQueries(1, &positions, &wrong_row, &paths));
    const wrong_path = [_][]const Toy.Hash{ &.{7}, &.{8}, &.{9} };
    try std.testing.expectError(error.DuplicateMismatch,
        R.auditDuplicateQueries(1, &positions, &rows, &wrong_path));
    const alias = [_]usize{ 1, 0, 3 };
    try std.testing.expectError(error.InvalidOpening,
        R.auditDuplicateQueries(1, &alias, &rows, &paths));
    const short = [_][]const Toy.Hash{ &.{7}, &.{8}, &.{} };
    try std.testing.expectError(error.InvalidOpening,
        R.auditDuplicateQueries(1, &positions, &rows, &short));
}

test "duplicate audit accepts native copied paths then detects corruption" {
    const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
    const Verifier = core.vcs_lifted.verifier.MerkleVerifierLifted(H);
    const Capture = core.vcs_lifted.verifier.MerklePathCapture(H);
    const allocator = std.testing.allocator;
    const zero = [_]M31{M31.fromCanonical(10)};
    const one = [_]M31{M31.fromCanonical(11)};
    var left_hasher = H.defaultWithInitialState();
    left_hasher.updateLeaf(&zero);
    var right_hasher = H.defaultWithInitialState();
    right_hasher.updateLeaf(&one);
    const root = H.hashChildren(.{
        .left = left_hasher.finalize(), .right = right_hasher.finalize(),
    });
    var verifier = try Verifier.init(allocator, root, &.{1});
    defer verifier.deinit(allocator);
    const positions = [_]usize{ 1, 0, 1 };
    const values = [_]M31{ one[0], zero[0], one[0] };
    const columns = [_][]const M31{&values};
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(
        allocator, &positions, &columns, .{ .hash_witness = &.{} }, &capture,
    );
    defer capture.deinit(allocator);
    const rows = [_][]const M31{ &one, &zero, &one };
    const paths = [_][]const H.Hash{ capture.path(0), capture.path(1), capture.path(2) };
    try Real.auditDuplicateQueries(1, &positions, &rows, &paths);
    capture.siblings[2][0] ^= 1;
    try std.testing.expectError(error.DuplicateMismatch,
        Real.auditDuplicateQueries(1, &positions, &rows, &paths));
}

test "real BLAKE2s opening rejects a conflicting row without a collision" {
    const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
    const first = [_]M31{M31.fromCanonical(10)};
    const second = [_]M31{M31.fromCanonical(11)};
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(&first);
    const root = hasher.finalize();
    try std.testing.expectError(error.InvalidOpening,
        Real.extract(root, 0, 0, &first, &.{}, &second, &.{}));
    try std.testing.expectError(error.SameRow,
        Real.extract(root, 0, 0, &first, &.{}, &first, &.{}));
}
