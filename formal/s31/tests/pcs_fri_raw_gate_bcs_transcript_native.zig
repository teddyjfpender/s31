//! Raw Gate channel replay against an independent Python BLAKE2s-256 model.
//! This is a synthetic transcript, not a proof or a BCS security reduction.
const std = @import("std");
const core = @import("stwo_core");
const MC = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sMerkleChannel;
const QM31 = core.fields.qm31.QM31;

const Epoch = struct { stage: []const u8, digest: []const u8, counter: u32 };
const Fixture = struct {
    schema: []const u8,
    scope: []const u8,
    epochs: []const Epoch,
    interaction_nonce: u64,
    fri_nonce: u64,
    lookup_z: [4]u32,
    lookup_alpha: [4]u32,
    composition_randomness: [4]u32,
    oods_seed: [4]u32,
    deep: [4]u32,
    first_alpha: [4]u32,
    inner_alpha: [4]u32,
    query_digest: []const u8,
    queries: []const usize,
};

fn felt(limbs: [4]u32) QM31 {
    return QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
}

fn expectFelt(expected: [4]u32, actual: QM31) !void {
    const words = actual.toM31Array();
    for (words, expected) |word, value| try std.testing.expectEqual(value, word.v);
}

fn root(byte: u8) [32]u8 {
    return [_]u8{byte} ** 32;
}

fn mark(channel: MC.Channel, expected: Epoch, name: []const u8) !void {
    try std.testing.expectEqualStrings(name, expected.stage);
    const actual = std.fmt.bytesToHex(channel.digestBytes(), .lower);
    try std.testing.expectEqualStrings(expected.digest, &actual);
    try std.testing.expectEqual(expected.counter, channel.n_draws);
}

test "P07 raw Gate channel matches independent byte-level model" {
    const allocator = std.testing.allocator;
    const parsed = try std.json.parseFromSlice(Fixture, allocator,
        @embedFile("pcs_fri_raw_gate_bcs_transcript.json"), .{});
    defer parsed.deinit();
    const expected = parsed.value;
    try std.testing.expectEqualStrings("s31-raw-gate-bcs-transcript-fixture-v1", expected.schema);
    try std.testing.expectEqualStrings("synthetic_plain_gate_channel_replay_only", expected.scope);
    try std.testing.expectEqual(@as(usize, 6), expected.epochs.len);

    var c = MC.Channel{};
    core.channel.lookup_transcript.mixChannelSalt(&c, 0);
    const config = try core.pcs.config_v2.FriConfigV2.init(8, 0, 1, 70, 1);
    config.mixInto(&c);
    MC.mixRoot(&c, root(1));
    MC.mixRoot(&c, root(2));
    var outputs: [8]QM31 = undefined;
    for (&outputs, 0..) |*out, i| out.* = felt(.{ @intCast(i), 0, 0, 0 });
    c.mixFelts(&outputs);
    MC.mixRoot(&c, root(3));
    try mark(c, expected.epochs[0], "before_interaction_pow");
    try std.testing.expect(c.verifyPowNonce(8, expected.interaction_nonce));
    c.mixU64(expected.interaction_nonce);
    try mark(c, expected.epochs[1], "after_interaction_pow");
    const pair = try core.channel.lookup_transcript.drawLookupElements(allocator, &c);
    try expectFelt(expected.lookup_z, pair.z);
    try expectFelt(expected.lookup_alpha, pair.alpha);
    try mark(c, expected.epochs[2], "after_lookup_draw");

    c.mixFelts(&.{felt(.{ 9, 10, 11, 12 })});
    MC.mixRoot(&c, root(4));
    try expectFelt(expected.composition_randomness, c.drawSecureFelt());
    MC.mixRoot(&c, root(5));
    try expectFelt(expected.oods_seed, c.drawSecureFelt());
    c.mixFelts(&.{ felt(.{ 13, 14, 15, 16 }), felt(.{ 17, 18, 19, 20 }) });
    try expectFelt(expected.deep, c.drawSecureFelt());
    MC.mixRoot(&c, root(6));
    try expectFelt(expected.first_alpha, c.drawSecureFelt());
    MC.mixRoot(&c, root(7));
    try expectFelt(expected.inner_alpha, c.drawSecureFelt());
    c.mixFelts(&.{ felt(.{ 21, 22, 23, 24 }), felt(.{ 25, 26, 27, 28 }) });
    try mark(c, expected.epochs[3], "before_fri_pow");
    try std.testing.expect(c.verifyPowNonce(8, expected.fri_nonce));
    c.mixU64(expected.fri_nonce);
    try mark(c, expected.epochs[4], "after_fri_pow");
    const query_digest = c.digestBytes();
    try std.testing.expectEqualStrings(expected.query_digest,
        &std.fmt.bytesToHex(query_digest, .lower));
    const raw = try core.queries.drawQueries(&c, allocator, 21, 70);
    defer allocator.free(raw);
    try std.testing.expectEqualSlices(usize, expected.queries, raw);
    try mark(c, expected.epochs[5], "after_queries");

    // Independently assemble each exact 37-byte preimage consumed by the
    // selected channel. This ties the nine modeled query blocks to the
    // native hasher, including the six-word final block and its two unused
    // lanes. It does not model a random oracle.
    for (0..9) |block| {
        var input: [37]u8 = undefined;
        @memcpy(input[0..32], query_digest[0..]);
        std.mem.writeInt(u32, input[32..36], @intCast(block), .little);
        input[36] = 0;
        var hash: [32]u8 = undefined;
        std.crypto.hash.blake2.Blake2s256.hash(&input, &hash, .{});
        for (0..8) |lane| {
            const word = std.mem.readInt(u32, hash[lane * 4 ..][0..4], .little);
            const slot = 8 * block + lane;
            if (slot < raw.len) try std.testing.expectEqual(
                @as(usize, word & 0x1fffff), raw[slot],
            );
        }
    }
}
