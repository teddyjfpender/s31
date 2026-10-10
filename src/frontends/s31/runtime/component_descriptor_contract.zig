//! Versioned, ordered identity contract for verifier-owned AIR components.
//!
//! This is an in-process comparison format, not a proof key or a component
//! factory. A verifier must derive the expected roster from authenticated
//! source and selected AIR; equality with an untrusted roster has no authority.
const std = @import("std");
const Sha256 = std.crypto.hash.sha2.Sha256;

pub const version: u32 = 1;
pub const Digest = [32]u8;
pub const Source = union(enum(u8)) {
    bundled_air: struct {
        bundle_index: u32,
        bundle_sha256: Digest,
        program_binding_sha256: Digest,
    },
    native_air: struct {
        /// Registry IDs are profile-owned; the V4 adapter uses 1=chip,
        /// 2=bridge. IDs alone never authenticate an implementation.
        program_id: u32,
        program_version: u32,
        program_binding_sha256: Digest,
    },
};

pub const Entry = struct {
    proof_index: u32,
    claimed_sum_index: u32,
    call_id: ?u32,
    source: Source,
};

pub const Roster = struct {
    schema_version: u32 = version,
    source_sha256: Digest,
    /// The profile's existing transcript-bound typed manifest digest.
    manifest_sha256: Digest,
    entries: []const Entry,
};

pub fn validate(roster: Roster) !void {
    if (roster.schema_version != version or roster.entries.len == 0 or
        roster.entries.len > 1024)
        return error.InvalidComponentDescriptorContract;
    for (roster.entries, 0..) |entry, index| {
        if (entry.proof_index != index or entry.claimed_sum_index != index)
            return error.InvalidComponentDescriptorContract;
        switch (entry.source) {
            .bundled_air => {},
            .native_air => |source| {
                if (source.program_id == 0 or source.program_version == 0)
                    return error.InvalidComponentDescriptorContract;
            },
        }
    }
}

/// Compare typed fields after checking both versions and canonical positions.
/// This avoids treating a caller-supplied hash as its own trust root.
pub fn requireExact(expected: Roster, actual: Roster) !void {
    try validate(expected);
    try validate(actual);
    if (!std.meta.eql(expected.source_sha256, actual.source_sha256) or
        !std.meta.eql(expected.manifest_sha256, actual.manifest_sha256) or
        expected.entries.len != actual.entries.len)
        return error.InvalidComponentDescriptorContract;
    for (expected.entries, actual.entries) |left, right| {
        if (!std.meta.eql(left, right)) return error.InvalidComponentDescriptorContract;
    }
}

/// Canonical diagnostic digest, independent of JSON order and field padding.
/// The V4 proof transcript still uses its established manifest precommitment.
pub fn digest(roster: Roster) !Digest {
    try validate(roster);
    var h = Sha256.init(.{});
    h.update("S31-COMPONENT-DESCRIPTOR-CONTRACT-V1\x00");
    hashInt(&h, roster.schema_version);
    h.update(&roster.source_sha256);
    h.update(&roster.manifest_sha256);
    hashInt(&h, @as(u32, @intCast(roster.entries.len)));
    for (roster.entries) |entry| {
        hashInt(&h, entry.proof_index);
        hashInt(&h, entry.claimed_sum_index);
        if (entry.call_id) |id| {
            hashInt(&h, @as(u8, 1));
            hashInt(&h, id);
        } else hashInt(&h, @as(u8, 0));
        switch (entry.source) {
            .bundled_air => |source| {
                hashInt(&h, @as(u8, 0));
                hashInt(&h, source.bundle_index);
                h.update(&source.bundle_sha256);
                h.update(&source.program_binding_sha256);
            },
            .native_air => |source| {
                hashInt(&h, @as(u8, 1));
                hashInt(&h, source.program_id);
                hashInt(&h, source.program_version);
                h.update(&source.program_binding_sha256);
            },
        }
    }
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

test "versioned descriptor rejects substitution, reordering and version drift" {
    const a = std.testing.allocator;
    const entries = [_]Entry{
        .{ .proof_index = 0, .claimed_sum_index = 0, .call_id = null, .source = .{ .bundled_air = .{
            .bundle_index = 1,
            .bundle_sha256 = [_]u8{1} ** 32,
            .program_binding_sha256 = [_]u8{2} ** 32,
        } } },
        .{ .proof_index = 1, .claimed_sum_index = 1, .call_id = 0, .source = .{ .native_air = .{
            .program_id = 1,
            .program_version = 4,
            .program_binding_sha256 = [_]u8{3} ** 32,
        } } },
        .{ .proof_index = 2, .claimed_sum_index = 2, .call_id = 0, .source = .{ .native_air = .{
            .program_id = 2,
            .program_version = 4,
            .program_binding_sha256 = [_]u8{4} ** 32,
        } } },
    };
    const expected: Roster = .{ .source_sha256 = [_]u8{5} ** 32, .manifest_sha256 = [_]u8{6} ** 32, .entries = &entries };
    try requireExact(expected, expected);
    const original = try digest(expected);
    // Independently calculated from the specified little-endian field order.
    try std.testing.expectEqualStrings(
        "0372f9b1cb7c9c34937532902dd41b49e713dd4afacd17d3ff6ff488402dc5c9",
        &std.fmt.bytesToHex(original, .lower),
    );
    var altered = try a.dupe(Entry, &entries);
    defer a.free(altered);
    var actual = expected;
    actual.entries = altered;
    altered[0].source.bundled_air.program_binding_sha256[0] ^= 1;
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
    try std.testing.expect(!std.meta.eql(original, try digest(actual)));
    altered[0] = entries[0];
    std.mem.swap(Entry, &altered[1], &altered[2]);
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
    altered[1] = entries[1];
    altered[2] = entries[2];
    altered[1].source.native_air.program_version += 1;
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
    altered[1] = entries[1];
    altered[1].source.native_air.program_id = 2;
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
    actual = expected;
    actual.schema_version += 1;
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
    actual = expected;
    actual.manifest_sha256[0] ^= 1;
    try std.testing.expectError(error.InvalidComponentDescriptorContract, requireExact(expected, actual));
}
