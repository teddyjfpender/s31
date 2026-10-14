//! Byte-level differential for the selected plain BLAKE2s Merkle profile.
//! Zig's standard BLAKE2s implementation supplies an independent digest of
//! the explicit canonical leaf and ordered-parent messages.
const std = @import("std");
const core = @import("stwo_core");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Blake2s = std.crypto.hash.blake2.Blake2s256;

fn digest(message: []const u8) [32]u8 {
    var output: [32]u8 = undefined;
    Blake2s.hash(message, &output, .{});
    return output;
}

fn encode(words: []const M31, bytes: []u8) void {
    std.debug.assert(bytes.len == words.len * 4);
    for (words, 0..) |word, i| {
        const encoded = word.toBytesLe();
        @memcpy(bytes[4 * i ..][0..4], &encoded);
    }
}

test "plain lifted leaf hashes exact canonical M31 LE bytes across BLAKE2s block boundary" {
    try std.testing.expectEqual(@as(u32, 0), H.domainPrefixBytes());
    const boundary = [_]u32{ 0, 1, 255, 256, 65535, 65536, 0x7ffffffe };
    var words: [33]M31 = undefined;
    for (&words, 0..) |*word, i| {
        word.* = M31.fromCanonical(boundary[i % boundary.len]);
    }
    inline for (.{ 0, 1, 7, 15, 16, 17, 31, 32, 33 }) |count| {
        var message: [count * 4]u8 = undefined;
        encode(words[0..count], &message);
        var hasher = H.defaultWithInitialState();
        hasher.updateLeaf(words[0..count]);
        const actual = hasher.finalize();
        const expected = digest(&message);
        try std.testing.expectEqualSlices(u8, &expected, &actual);

        var packed_hasher = H.defaultWithInitialState();
        packed_hasher.updateLeafPackedBytes(&message);
        try std.testing.expectEqualSlices(u8, &expected, &packed_hasher.finalize());
    }
    try std.testing.expectEqualSlices(u8, &[_]u8{ 0xfe, 0xff, 0xff, 0x7f },
        &words[6].toBytesLe());
}

test "plain lifted parent hashes exactly left then right with no tag" {
    var left: [32]u8 = undefined;
    var right: [32]u8 = undefined;
    for (&left, 0..) |*byte, i| byte.* = @intCast(3 * i + 1);
    for (&right, 0..) |*byte, i| byte.* = @intCast(255 - 2 * i);
    var message: [64]u8 = undefined;
    @memcpy(message[0..32], &left);
    @memcpy(message[32..64], &right);
    const expected = digest(&message);
    const actual = H.hashChildren(.{ .left = left, .right = right });
    try std.testing.expectEqualSlices(u8, &expected, &actual);

    // At 16 M31 words, leaf and parent preimages are both 64 bytes. The
    // protocol relies on a fixed tree shape, not an implicit type prefix.
    var words: [16]M31 = undefined;
    for (&words, 0..) |*word, i| word.* = M31.fromCanonical(@intCast(i + 1));
    var leaf_message: [64]u8 = undefined;
    encode(&words, &leaf_message);
    var leaf_hasher = H.defaultWithInitialState();
    leaf_hasher.updateLeaf(&words);
    try std.testing.expectEqualSlices(u8, &digest(&leaf_message), &leaf_hasher.finalize());

    var reversed: [64]u8 = undefined;
    @memcpy(reversed[0..32], &right);
    @memcpy(reversed[32..64], &left);
    try std.testing.expect(!std.mem.eql(u8, &expected, &digest(&reversed)));
}

test "FRI QM31 rows hash four ordered canonical coordinates per evaluation" {
    const values = [_]QM31{
        QM31.fromM31Array(.{
            M31.fromCanonical(0), M31.fromCanonical(1),
            M31.fromCanonical(256), M31.fromCanonical(0x7ffffffe),
        }),
        QM31.fromM31Array(.{
            M31.fromCanonical(255), M31.fromCanonical(65536),
            M31.fromCanonical(2), M31.fromCanonical(3),
        }),
        QM31.fromM31Array(.{
            M31.fromCanonical(4), M31.fromCanonical(5),
            M31.fromCanonical(6), M31.fromCanonical(7),
        }),
        QM31.fromM31Array(.{
            M31.fromCanonical(8), M31.fromCanonical(9),
            M31.fromCanonical(10), M31.fromCanonical(11),
        }),
    };
    inline for (.{ 1, 4 }) |count| {
        var flat: [count * 4]M31 = undefined;
        for (values[0..count], 0..) |value, offset| {
            const coords = value.toM31Array();
            for (coords, 0..) |coordinate, index| {
                flat[offset * 4 + index] = coordinate;
            }
        }
        var bytes: [count * 16]u8 = undefined;
        encode(&flat, &bytes);
        var hasher = H.defaultWithInitialState();
        hasher.updateLeaf(&flat);
        try std.testing.expectEqualSlices(u8, &digest(&bytes), &hasher.finalize());

        var changed = flat;
        changed[1] = M31.fromCanonical(2);
        var changed_bytes: [count * 16]u8 = undefined;
        encode(&changed, &changed_bytes);
        try std.testing.expect(!std.mem.eql(u8, &bytes, &changed_bytes));
    }
}
