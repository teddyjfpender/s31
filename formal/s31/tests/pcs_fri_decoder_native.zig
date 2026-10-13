//! Focused adversarial checks against the pinned native lifted decoder.
const std = @import("std");
const core = @import("stwo_core");
const verifier_mod = core.vcs_lifted.verifier;
const Hasher = core.vcs_lifted.blake2_merkle.Blake2sMerkleHasher;
const M31 = core.fields.m31.M31;

fn leaf(value: M31) Hasher.Hash {
    var hasher = Hasher.defaultWithInitialState();
    hasher.updateLeaf(&.{value});
    return hasher.finalize();
}

test "lifted decoder pairs adjacent nodes and rejects missing, extra, and changed witnesses" {
    const alloc = std.testing.allocator;
    const Verifier = verifier_mod.MerkleVerifierLifted(Hasher);
    const Capture = verifier_mod.MerklePathCapture(Hasher);

    const l0 = leaf(M31.fromCanonical(10));
    const l1 = leaf(M31.fromCanonical(11));
    const l2 = leaf(M31.fromCanonical(12));
    const l3 = leaf(M31.fromCanonical(13));
    const left = Hasher.hashChildren(.{ .left = l0, .right = l1 });
    const right = Hasher.hashChildren(.{ .left = l2, .right = l3 });
    const root = Hasher.hashChildren(.{ .left = left, .right = right });
    var verifier = try Verifier.init(alloc, root, &.{2});
    defer verifier.deinit(alloc);

    // Input order and a duplicate differ from the sorted decoder frontier.
    const positions = [_]usize{ 1, 0, 1 };
    const values = [_]M31{ M31.fromCanonical(11), M31.fromCanonical(10), M31.fromCanonical(11) };
    const columns = [_][]const M31{&values};
    var witness = [_]Hasher.Hash{right};
    var capture: Capture = undefined;
    try verifier.verifyWithPathCapture(alloc, &positions, &columns, .{ .hash_witness = &witness }, &capture);
    defer capture.deinit(alloc);
    try std.testing.expectEqualSlices(usize, &positions, capture.positions);
    try std.testing.expectEqualSlices(u8, &l0, &capture.path(0)[0]);
    try std.testing.expectEqualSlices(u8, &right, &capture.path(0)[1]);
    try std.testing.expectEqualSlices(u8, &l1, &capture.path(1)[0]);
    try std.testing.expectEqualSlices(u8, &right, &capture.path(1)[1]);
    try std.testing.expectEqualSlices(Hasher.Hash, capture.path(0), capture.path(2));

    const sentinel = Capture{ .positions = &.{}, .path_depth = std.math.maxInt(u32), .siblings = &.{} };
    var rejected = sentinel;
    var no_witness = [_]Hasher.Hash{};
    try std.testing.expectError(error.WitnessTooShort, verifier.verifyWithPathCapture(
        alloc,
        &positions,
        &columns,
        .{ .hash_witness = &no_witness },
        &rejected,
    ));
    try std.testing.expectEqualDeep(sentinel, rejected);

    rejected = sentinel;
    var extra_witness = [_]Hasher.Hash{ right, l2 };
    try std.testing.expectError(error.WitnessTooLong, verifier.verifyWithPathCapture(
        alloc,
        &positions,
        &columns,
        .{ .hash_witness = &extra_witness },
        &rejected,
    ));
    try std.testing.expectEqualDeep(sentinel, rejected);

    rejected = sentinel;
    var changed_witness = [_]Hasher.Hash{l2};
    try std.testing.expectError(error.RootMismatch, verifier.verifyWithPathCapture(
        alloc,
        &positions,
        &columns,
        .{ .hash_witness = &changed_witness },
        &rejected,
    ));
    try std.testing.expectEqualDeep(sentinel, rejected);

    rejected = sentinel;
    const inconsistent = [_]M31{ M31.fromCanonical(11), M31.fromCanonical(10), M31.fromCanonical(12) };
    const inconsistent_columns = [_][]const M31{&inconsistent};
    try std.testing.expectError(error.DuplicateQueryMismatch, verifier.verifyWithPathCapture(
        alloc,
        &positions,
        &inconsistent_columns,
        .{ .hash_witness = &witness },
        &rejected,
    ));
    try std.testing.expectEqualDeep(sentinel, rejected);
}
