//! Versioned, source-reconstructed component identity for bounded mixed plans.
//!
//! This is an inspection contract for 1..8 calls, not a proof-byte profile.
//! The only mixed proof-byte verifier currently admits exactly three calls.
const std = @import("std");
const contract = @import("../component_descriptor_contract.zig");
const admission = @import("../../language/bounded_call_admission.zig");
const mixed = @import("inspection.zig");

pub const version: u32 = 1;
pub const max_entries = 1 + 2 * admission.max_calls;

pub const Descriptor = struct {
    schema_version: u32 = version,
    source_sha256: contract.Digest,
    manifest_sha256: contract.Digest,
    call_count: u8,
    entry_count: usize,
    entries: [max_entries]contract.Entry = undefined,
    digest: contract.Digest,

    pub fn roster(self: *const Descriptor) contract.Roster {
        return .{
            .schema_version = self.schema_version,
            .source_sha256 = self.source_sha256,
            .manifest_sha256 = self.manifest_sha256,
            .entries = self.entries[0..self.entry_count],
        };
    }
};

/// Convert a source-derived, live-handle-checked mixed schedule into a typed
/// ordered roster. The caller must obtain the schedule from `inspectSource`.
pub fn fromSchedule(schedule: *const mixed.SelectedSchedule) !Descriptor {
    const count: usize = schedule.call_count;
    if (count == 0 or count > admission.max_calls or
        schedule.slot_count != 1 + 2 * count or
        schedule.native_geometry == null or
        schedule.native_geometry.?.slot_count != schedule.slot_count)
        return error.InvalidMixedDescriptor;
    var result: Descriptor = .{
        .source_sha256 = schedule.source_sha256,
        .manifest_sha256 = schedule.digest,
        .call_count = schedule.call_count,
        .entry_count = schedule.slot_count,
        .digest = undefined,
    };
    for (schedule.slots[0..schedule.slot_count], 0..) |slot, index| {
        if (slot.proof_index != index or slot.claimed_sum_index != index)
            return error.InvalidMixedDescriptor;
        const call_id: ?u32 = if (index == 0) null else @intCast((index - 1) / 2);
        const wanted_kind: mixed.SourceKind = if (index == 0) .bundled_circuit else blk: {
            const pair = call_id.? < 2;
            const chip = index % 2 == 1;
            break :blk if (pair)
                (if (chip) .pair_chip else .pair_bridge)
            else
                (if (chip) .many_chip else .many_bridge);
        };
        if (slot.call_id != call_id or slot.source_kind != wanted_kind)
            return error.InvalidMixedDescriptor;
        result.entries[index] = .{
            .proof_index = slot.proof_index,
            .claimed_sum_index = slot.claimed_sum_index,
            .call_id = call_id,
            .source = if (index == 0) .{ .bundled_air = .{
                .bundle_index = 1,
                .bundle_sha256 = slot.air_source_sha256,
                .program_binding_sha256 = slot.program_binding_sha256,
            } } else .{ .native_air = .{
                .program_id = switch (slot.source_kind) {
                    .pair_chip => 1,
                    .pair_bridge => 2,
                    .many_chip => 3,
                    .many_bridge => 4,
                    .bundled_circuit => unreachable,
                },
                .program_version = 1,
                .program_binding_sha256 = slot.program_binding_sha256,
            } },
        };
    }
    for (schedule.calls[0..count], 0..) |call, index|
        if (call.call_id != index) return error.InvalidMixedDescriptor;
    result.digest = try contract.digest(result.roster());
    return result;
}

/// Regenerate from literal source and official AIR bytes. A package may show
/// this descriptor to auditors; it cannot act as a verification key by itself.
pub fn fromSource(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) !Descriptor {
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    return fromSchedule(&schedule);
}

/// Require an externally supplied descriptor to equal the verifier's own
/// source reconstruction, including order, cardinality, source identity,
/// selected manifest, and each program binding. A resealed descriptor does
/// not acquire authority from its checksum.
pub fn requireSource(
    allocator: std.mem.Allocator,
    candidate: *const Descriptor,
    source: []const u8,
    air_bytes: []const u8,
) !void {
    if (candidate.schema_version != version or candidate.entry_count == 0 or
        candidate.entry_count > max_entries or
        candidate.entry_count != 1 + 2 * @as(usize, candidate.call_count))
        return error.InvalidMixedDescriptor;
    const expected = try fromSource(allocator, source, air_bytes);
    if (candidate.call_count != expected.call_count or
        !std.meta.eql(candidate.digest, expected.digest))
        return error.InvalidMixedDescriptor;
    contract.requireExact(expected.roster(), candidate.roster()) catch
        return error.InvalidMixedDescriptor;
}

test "mixed N4 source descriptor binds cardinality roles and public private source" {
    const a = std.testing.allocator;
    const air_bytes = @embedFile("s31_air_programs");
    const source = @embedFile("../../examples/boundary/mixed_four.s31.json");
    const schedule = try mixed.inspectSource(a, source, air_bytes);
    try std.testing.expectEqual(@as(u8, 4), schedule.call_count);
    try std.testing.expectEqual(@as(usize, 9), schedule.slot_count);
    try std.testing.expectEqual(mixed.SourceKind.pair_chip, schedule.slots[1].source_kind);
    try std.testing.expectEqual(mixed.SourceKind.pair_bridge, schedule.slots[4].source_kind);
    try std.testing.expectEqual(mixed.SourceKind.many_chip, schedule.slots[5].source_kind);
    try std.testing.expectEqual(mixed.SourceKind.many_bridge, schedule.slots[8].source_kind);
    try std.testing.expectEqual(@as(u32, 80), schedule.main_columns);
    try std.testing.expectEqual(@as(u32, 120), schedule.interaction_columns);
    const expected = try fromSchedule(&schedule);
    try requireSource(a, &expected, source, air_bytes);

    var altered = expected;
    altered.call_count = 3;
    altered.entry_count = 7;
    altered.digest = try contract.digest(altered.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &altered, source, air_bytes));

    altered = expected;
    std.mem.swap(contract.Source, &altered.entries[5].source, &altered.entries[6].source);
    altered.digest = try contract.digest(altered.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &altered, source, air_bytes));

    altered = expected;
    altered.entries[7].source.native_air.program_binding_sha256[0] ^= 1;
    altered.digest = try contract.digest(altered.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &altered, source, air_bytes));

    altered = expected;
    altered.entries[8].source.native_air.program_id = 2;
    altered.digest = try contract.digest(altered.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &altered, source, air_bytes));

    const changed_public = try std.mem.replaceOwned(u8, a, source, "\"public_outputs\": [\"sum\", \"product\"]", "\"public_outputs\": [\"product\", \"sum\"]");
    defer a.free(changed_public);
    try std.testing.expect(!std.mem.eql(u8, source, changed_public));
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &expected, changed_public, air_bytes));

    const changed_private = try a.dupe(u8, source);
    defer a.free(changed_private);
    const private_at = std.mem.indexOf(u8, changed_private, "\"constant\": 16") orelse unreachable;
    changed_private[private_at + "\"constant\": ".len + 1] = '7';
    try std.testing.expectError(error.InvalidMixedDescriptor, requireSource(a, &expected, changed_private, air_bytes));

    const public_input = try std.mem.replaceOwned(u8, a, source, "\"visibility\": \"private\"", "\"visibility\": \"public\"");
    defer a.free(public_input);
    try std.testing.expect(!std.mem.eql(u8, source, public_input));
    if (requireSource(a, &expected, public_input, air_bytes)) |_| return error.AcceptedChangedInputVisibility else |_| {}
}
