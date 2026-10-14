//! Independent raw BLAKE2s oracle for the selected channel's PoW predicate.
//! This checks deterministic bytes for the two pinned Gate transcript states;
//! it does not assign random-oracle independence to nonce attempts.
const std = @import("std");
const core = @import("stwo_core");

const MC = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
const p: u64 = core.fields.m31.Modulus;
const Epoch = struct { stage: []const u8, digest: []const u8, counter: u32 };
const Fixture = struct { epochs: []const Epoch };

fn rawHash(bytes: []const u8) [32]u8 {
    var out: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(bytes, &out, .{});
    return out;
}

fn reduceDigestIndependently(raw: [32]u8) [32]u8 {
    var out: [32]u8 = undefined;
    for (0..8) |lane| {
        const at = lane * 4;
        const word = std.mem.readInt(u32, raw[at..][0..4], .little);
        std.mem.writeInt(u32, out[at..][0..4], @intCast(@as(u64, word) % p), .little);
    }
    return out;
}

fn independentlyAccepts(digest: [32]u8, bits: u32, nonce: u64) bool {
    var prefix_input = [_]u8{0} ** 52;
    std.mem.writeInt(u32, prefix_input[0..4], 0x12345678, .little);
    @memcpy(prefix_input[16..48], &digest);
    std.mem.writeInt(u32, prefix_input[48..52], bits, .little);
    const prefix = reduceDigestIndependently(rawHash(&prefix_input));

    var nonce_input: [40]u8 = undefined;
    @memcpy(nonce_input[0..32], &prefix);
    std.mem.writeInt(u64, nonce_input[32..40], nonce, .little);
    const raw = rawHash(&nonce_input);
    const first = std.mem.readInt(u32, raw[0..4], .little);
    const mask: u64 = (@as(u64, 1) << @intCast(bits)) - 1;
    return ((@as(u64, first) % p) & mask) == 0;
}

test "both selected Gate PoW predicates match independent raw hash and M31 model" {
    const parsed = try std.json.parseFromSlice(Fixture, std.testing.allocator, @embedFile("pcs_fri_bcs_transcript.json"), .{ .ignore_unknown_fields = true });
    defer parsed.deinit();
    const epochs = parsed.value.epochs;
    try std.testing.expect(epochs.len >= 4);
    const stages = [_]struct { index: usize, name: []const u8, production_bits: u32 }{
        .{ .index = 0, .name = "before_interaction_pow", .production_bits = 20 },
        .{ .index = 3, .name = "before_fri_pow", .production_bits = 26 },
    };
    for (stages) |stage| {
        const epoch = epochs[stage.index];
        try std.testing.expectEqualStrings(stage.name, epoch.stage);
        try std.testing.expectEqual(@as(u32, 0), epoch.counter);
        var digest: [32]u8 = undefined;
        _ = try std.fmt.hexToBytes(&digest, epoch.digest);
        var channel = MC.Channel{};
        channel.updateDigest(digest);
        for ([_]u32{ 0, 1, 8, stage.production_bits, 31 }) |bits| {
            for (0..256) |small_nonce| {
                const nonce: u64 = @intCast(small_nonce);
                try std.testing.expectEqual(
                    independentlyAccepts(digest, bits, nonce),
                    channel.verifyPowNonce(bits, nonce),
                );
            }
            for ([_]u64{ 0x0102030405060708, std.math.maxInt(u64) }) |nonce| {
                try std.testing.expectEqual(
                    independentlyAccepts(digest, bits, nonce),
                    channel.verifyPowNonce(bits, nonce),
                );
            }
        }
        try std.testing.expectEqual(digest, channel.digestBytes());
        try std.testing.expectEqual(@as(u32, 0), channel.n_draws);
    }
}

test "M31 PoW low-bit boundary words include extra favorable raw preimage" {
    const counts = [_]struct { bits: u32, expected: u64 }{
        .{ .bits = 20, .expected = 4097 },
        .{ .bits = 26, .expected = 65 },
    };
    for (counts) |case| {
        const mask = (@as(u64, 1) << @intCast(case.bits)) - 1;
        for ([_]u64{ 0, p, 2 * p, 2 * p + 1 }) |raw| {
            const digest = core.vcs.blake2_hash.digestFromU32s([_]u32{@intCast(raw)} ** 8);
            const reduced = core.vcs.blake2_hash.digestToU32s(
                core.vcs.blake2_hash.reduceToM31(digest),
            );
            try std.testing.expectEqual(@as(u32, @intCast(raw % p)), reduced[0]);
            try std.testing.expectEqual(raw != 2 * p + 1, (reduced[0] & @as(u32, @intCast(mask))) == 0);
        }
        try std.testing.expectEqual((@as(u64, 1) << @intCast(32 - case.bits)) + 1, case.expected);
    }
}

test "independent PoW oracle accepts pinned positive vectors at both production bit counts" {
    const vectors = [_]struct { seed: u64, bits: u32, nonce: u64 }{
        .{ .seed = 1, .bits = 20, .nonce = 12885632339 },
        .{ .seed = 0x1111_2222_3333_4344, .bits = 26, .nonce = 150324282603 },
    };
    for (vectors) |vector| {
        var channel = MC.Channel{};
        channel.mixU64(vector.seed);
        try std.testing.expect(independentlyAccepts(channel.digestBytes(), vector.bits, vector.nonce));
        try std.testing.expect(channel.verifyPowNonce(vector.bits, vector.nonce));
    }
}
