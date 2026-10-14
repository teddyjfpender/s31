//! Differential check of the source-bound eight-lane raw query model.
//! It exercises the actual Zig M31 reducer and drawQueries loop. Hash-word
//! independence and the real transcript's adversarial security are not tested.
const std = @import("std");
const core = @import("stwo_core");

const p: u64 = core.fields.m31.Modulus;
const raw_blocks = [_][8]u32{
    .{ 0, 1, @intCast(p - 1), @intCast(p), @intCast(p + 1), @intCast(2 * p - 1), @intCast(2 * p), @intCast(2 * p + 1) },
    .{ 0xffffffff, 0xffffffff, 0, 0, 1, 1, 0x80000000, 0x7ffffffe },
    .{ 17, 17, 19, 19, 23, 23, 29, 29 },
};

const ControlledChannel = struct {
    calls: usize = 0,

    pub fn drawU32s(self: *@This()) [8]u32 {
        const raw = raw_blocks[self.calls % raw_blocks.len];
        self.calls += 1;
        const digest = core.vcs.blake2_hash.digestFromU32s(raw);
        return core.vcs.blake2_hash.digestToU32s(
            core.vcs.blake2_hash.reduceToM31(digest),
        );
    }
};

test "native M31 masked query batch matches block-lane model at every shift boundary" {
    const lengths = [_]usize{ 0, 1, 2, 7, 8, 9, 15, 16, 17, 23, 24, 69, 70, 71 };
    for (lengths) |n| {
        for (0..32) |k| {
            var channel = ControlledChannel{};
            const actual = try core.queries.drawQueries(&channel, std.testing.allocator, @intCast(k), n);
            defer std.testing.allocator.free(actual);
            try std.testing.expectEqual(n, actual.len);
            try std.testing.expectEqual((n + 7) / 8, channel.calls);
            const mask: u64 = (@as(u64, 1) << @intCast(k)) - 1;
            for (actual, 0..) |query, slot| {
                const raw = raw_blocks[(slot / 8) % raw_blocks.len][slot % 8];
                const expected: usize = @intCast((@as(u64, raw) % p) & mask);
                try std.testing.expectEqual(expected, query);
            }
        }
    }
}

test "selected S31 M31 channel consumes nine blocks for seventy ordered queries" {
    const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
    var actual_channel = Profile.Channel{};
    actual_channel.mixU64(42);
    var manual_channel = actual_channel;
    const actual = try core.queries.drawQueries(&actual_channel, std.testing.allocator, 21, 70);
    defer std.testing.allocator.free(actual);
    try std.testing.expectEqual(@as(u32, 9), actual_channel.n_draws);
    for (0..9) |block| {
        const words = manual_channel.drawU32s();
        for (words, 0..) |word, lane| {
            const slot = block * 8 + lane;
            if (slot < 70) try std.testing.expectEqual(@as(usize, word & 0x1fffff), actual[slot]);
        }
    }
    try std.testing.expectEqual(@as(u32, 9), manual_channel.n_draws);
}

test "selected query positions match independent raw Blake2s preimages" {
    // This oracle bypasses the selected channel's drawU32s and reducer. It
    // hashes the 37-byte preimage with Zig stdlib BLAKE2s, then uses scalar
    // integer modulo and masking. It tests deterministic correspondence only.
    const Profile = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
    for ([_]u64{ 0, 42, 0xfeed_cafe_1234_5678 }) |seed| {
        for ([_]usize{ 0, 1, 7, 8, 9, 69, 70, 71 }) |n| {
            for ([_]u32{ 0, 1, 2, 21, 31 }) |k| {
                var channel = Profile.Channel{};
                channel.mixU64(seed);
                const starting_digest = channel.digest;
                const actual = try core.queries.drawQueries(&channel, std.testing.allocator, k, n);
                defer std.testing.allocator.free(actual);
                try std.testing.expectEqual((n + 7) / 8, @as(usize, channel.n_draws));
                try std.testing.expectEqualSlices(u8, &starting_digest, &channel.digest);

                const mask: u32 = (@as(u32, 1) << @intCast(k)) - 1;
                for (0..(n + 7) / 8) |block| {
                    var preimage: [37]u8 = undefined;
                    @memcpy(preimage[0..32], starting_digest[0..]);
                    std.mem.writeInt(u32, preimage[32..36], @intCast(block), .little);
                    preimage[36] = 0;
                    var raw_digest: [32]u8 = undefined;
                    std.crypto.hash.blake2.Blake2s256.hash(&preimage, &raw_digest, .{});
                    for (0..8) |lane| {
                        const slot = block * 8 + lane;
                        if (slot >= n) break;
                        const base = lane * 4;
                        const raw = std.mem.readInt(u32, raw_digest[base..][0..4], .little);
                        const expected: usize = @intCast((@as(u64, raw) % p) & mask);
                        try std.testing.expectEqual(expected, actual[slot]);
                    }
                }
            }
        }
    }
}
