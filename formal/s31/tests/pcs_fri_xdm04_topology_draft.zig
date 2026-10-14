//! Finite operational checks for the exact experimental CAS05/XDM04 draft.
//! The Lean theorem covers arbitrary upper-path depth; this test compares its
//! transposed index conversion and tagged node shape with the native prover
//! and verifier at all three source heights of one small committed tree.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");

const M31 = core.fields.m31.M31;
const xdm = core.pcs.transposed_merkle_sparse;
const tree_hash = core.pcs.transposed_merkle_cascade;
const topology = core.pcs.transposed_merkle;
const Commitment = prover.pcs.transposed_cascade_experimental.Commitment;

fn pathPosition(level: usize, index: usize) usize {
    var at_level = level;
    var at_index = index;
    var place: usize = 1;
    var result: usize = 0;
    while (at_level > 0) : (at_level -= 1) {
        const bit = if (at_level == 1) at_index & 1 else (at_index >> 1) & 1;
        result += bit * place;
        place *= 2;
        at_index = topology.parent(@intCast(at_level), at_index);
    }
    return result;
}

fn replayPath(
    commitment: Commitment,
    level: usize,
    index: usize,
    node: tree_hash.Hash,
    mixed_insertions: bool,
    old_bit_zero: bool,
) tree_hash.Hash {
    var current = node;
    var at_level = level;
    var at_index = index;
    var position = if (old_bit_zero) index else pathPosition(level, index);
    while (at_level > 0) : (at_level -= 1) {
        const sibling = commitment.layers[at_level][topology.sibling(@intCast(at_level), at_index)];
        const left = if (position & 1 == 0) current else sibling;
        const right = if (position & 1 == 0) sibling else current;
        const parent_level = at_level - 1;
        const parent_index = topology.parent(@intCast(at_level), at_index);
        const parent_height = @as(usize, commitment.profile.largest_log_size) - parent_level;
        if (mixed_insertions and parent_height > 0 and parent_height < commitment.source_columns.len) {
            var values: [tree_hash.MAX_COLUMNS]M31 = undefined;
            for (commitment.source_columns[parent_height], 0..) |column, col|
                values[col] = column[parent_index];
            current = tree_hash.hashInserted(left, right,
                values[0..commitment.source_columns[parent_height].len]);
        } else {
            current = tree_hash.hashUpper(left, right);
        }
        position >>= 1;
        at_index = parent_index;
    }
    return current;
}

test "XDM04 accepted rows replay with transposed path position at leaf and inserted heights" {
    const allocator = std.testing.allocator;
    var h0: [32]M31 = undefined;
    var h1: [16]M31 = undefined;
    var h2: [8]M31 = undefined;
    for (&h0, 0..) |*value, i| value.* = M31.fromCanonical(@intCast(100 + i));
    for (&h1, 0..) |*value, i| value.* = M31.fromCanonical(@intCast(200 + i));
    for (&h2, 0..) |*value, i| value.* = M31.fromCanonical(@intCast(300 + i));
    const columns = [_][]const []const M31{
        &[_][]const M31{&h0},
        &[_][]const M31{&h1},
        &[_][]const M31{&h2},
    };
    const raw = [_]usize{5};
    var commitment = try Commitment.commitSparse(allocator, &columns, raw.len);
    defer commitment.deinit();
    const encoded = try commitment.encodeSparseOpenings(allocator, &raw);
    defer allocator.free(encoded);
    const profile = xdm.Profile{
        .largest_log_size = 5,
        .height_count = 3,
        .columns = .{ 1, 1, 1, 0, 0, 0, 0, 0 },
        .query_count = 1,
    };
    var opened = try xdm.verifyAndCollect(allocator, encoded, profile, commitment.root(), &raw);
    defer opened.deinit();

    for (0..3) |height| {
        const level = 5 - height;
        for (0..2) |j| {
            const index = xdm.pairBase(raw[0], height) + j;
            const row = [_]M31{opened.at(height, 0, j, 0)};
            const expected_row = columns[height][0][index];
            try std.testing.expect(row[0].eql(expected_row));
            const node = if (height == 0)
                tree_hash.hashLeaf(&row)
            else blk: {
                const children = topology.children(@intCast(level), index);
                break :blk tree_hash.hashInserted(
                    commitment.layers[level + 1][children[0]],
                    commitment.layers[level + 1][children[1]], &row,
                );
            };
            try std.testing.expectEqualDeep(commitment.layers[level][index], node);
            try std.testing.expectEqualDeep(commitment.root(),
                replayPath(commitment, level, index, node, true, false));
            try std.testing.expect(pathPosition(level, index) < (@as(usize, 1) << @intCast(level)));
        }
    }

    // The old upper-only path premise is valid at the bottom inserted height.
    // It fails at the leaf and middle inserted height because a later source
    // row is hashed into each intervening inserted parent.
    const leaf_index = xdm.pairBase(raw[0], 0);
    try std.testing.expect(!std.meta.eql(commitment.root(),
        replayPath(commitment, 5, leaf_index,
            commitment.layers[5][leaf_index], false, false)));
    const middle_index = xdm.pairBase(raw[0], 1);
    try std.testing.expect(!std.meta.eql(commitment.root(),
        replayPath(commitment, 4, middle_index,
            commitment.layers[4][middle_index], false, false)));
    const bottom_index = xdm.pairBase(raw[0], 2);
    try std.testing.expectEqualDeep(commitment.root(),
        replayPath(commitment, 3, bottom_index,
            commitment.layers[3][bottom_index], false, false));

    // At the inserted source height with native index 2, bit 1 says "right"
    // while bit 0 says "left". The old low-bit interpretation fails to
    // authenticate this valid opening under the same committed root.
    const inserted_index = xdm.pairBase(raw[0], 1);
    try std.testing.expectEqual(@as(usize, 2), inserted_index);
    try std.testing.expectEqual(@as(usize, 1), pathPosition(4, inserted_index) & 1);
    try std.testing.expect(!std.meta.eql(commitment.root(),
        replayPath(commitment, 4, inserted_index,
            commitment.layers[4][inserted_index], true, true)));

    // The first compressed witness contributes a missing source child. A
    // hostile change is rejected by the actual XDM04 root reconstruction.
    const fixed_bytes: usize = 8 + 2 + 2 + 4 + 4 + 2 + 2 + 4 + 2 * 3 + 32 +
        raw.len * (4 + 2 * 3 * @sizeOf(M31));
    const first_row_byte: usize = 8 + 2 + 2 + 4 + 4 + 2 + 2 + 4 + 2 * 3 + 32 + 4;
    for ([_]usize{ first_row_byte, first_row_byte + 2 * @sizeOf(M31) }) |row_byte| {
        const changed_row = try allocator.dupe(u8, encoded);
        defer allocator.free(changed_row);
        changed_row[row_byte] ^= 1;
        try std.testing.expectError(error.RootMismatch,
            xdm.verifyAndCollect(allocator, changed_row, profile, commitment.root(), &raw));
    }
    const witness_count = std.mem.readInt(u32, encoded[fixed_bytes..][0..4], .little);
    try std.testing.expect(witness_count > 0);
    const changed = try allocator.dupe(u8, encoded);
    defer allocator.free(changed);
    changed[fixed_bytes + 4] ^= 1;
    try std.testing.expectError(error.RootMismatch,
        xdm.verifyAndCollect(allocator, changed, profile, commitment.root(), &raw));
}
