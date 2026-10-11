//! Source-derived typed mixed registry and component manifest for 1..8 calls.
//!
//! The diagnostic digest here is not a proof transcript. Existing N=3 and
//! N=4 proof profiles retain their distinct, frozen schedule digests and tags.
const std = @import("std");
const mixed = @import("inspection.zig");
const descriptor = @import("descriptor.zig");
const registry = @import("registry.zig");
const lookup_budget = @import("lookup_budget.zig");

const Digest = [32]u8;
const Sha256 = std.crypto.hash.sha2.Sha256;
pub const version: u32 = 1;

pub const Entry = struct {
    registry_key: registry.Key = .bundled_circuit,
    registry_id: u32 = 0,
    registry_version: u32 = registry.version,
    role: registry.Role = .circuit,
    call_id: ?u32 = null,
    proof_index: u32 = 0,
    claimed_sum_index: u32 = 0,
    trace_log_size: u32 = 0,
    evaluation_log_size: u32 = 0,
    main_offset: u32 = 0,
    main_columns: u32 = 0,
    interaction_offset: u32 = 0,
    interaction_columns: u32 = 0,
    constraint_offset: u32 = 0,
    n_constraints: u32 = 0,
    preprocessed_indices: [8]u32 = [_]u32{0} ** 8,
    preprocessed_count: u8 = 0,
    relation_ids: [2]u32 = .{ 0, 0 },
    relation_count: u8 = 0,
    air_source_sha256: Digest = [_]u8{0} ** 32,
    program_binding_sha256: Digest = [_]u8{0} ** 32,
};

pub const Manifest = struct {
    schema_version: u32 = version,
    registry_version: u32 = registry.version,
    source_sha256: Digest,
    canonical_ir_sha256: Digest,
    fixed_root: Digest,
    selected_manifest_sha256: Digest,
    descriptor_sha256: Digest,
    call_count: u8,
    calls: [registry.max_calls]mixed.Call = [_]mixed.Call{.{}} ** registry.max_calls,
    entry_count: usize,
    entries: [registry.max_components]Entry = [_]Entry{.{}} ** registry.max_components,
    main_columns: u32,
    interaction_columns: u32,
    total_constraints: u32,
    digest: Digest = [_]u8{0} ** 32,

    pub fn entrySlice(self: *const Manifest) []const Entry {
        return self.entries[0..self.entry_count];
    }
};

/// Project an already source-inspected, live-handle-checked selected roster.
/// This function has no authority on a caller-supplied schedule by itself.
pub fn fromSchedule(schedule: *const mixed.SelectedSchedule) !Manifest {
    const identities = try descriptor.fromSchedule(schedule);
    const admitted = schedule.lookup_envelope orelse return error.InvalidMixedLookupBudget;
    var rounds: [registry.max_calls]u32 = undefined;
    for (schedule.calls[0..schedule.call_count], rounds[0..schedule.call_count]) |call, *round_count|
        round_count.* = call.rounds;
    const rows = if (schedule.slots[0].trace_log_size <= 16)
        @as(usize, 1) << @intCast(schedule.slots[0].trace_log_size)
    else
        return error.InvalidMixedLookupBudget;
    const rebuilt = lookup_budget.evaluate(rows, admitted.output_addresses, rounds[0..schedule.call_count]) catch
        return error.InvalidMixedLookupBudget;
    if (!std.meta.eql(admitted, rebuilt)) return error.InvalidMixedLookupBudget;
    if (schedule.slot_count != 1 + 2 * @as(usize, schedule.call_count) or
        schedule.slot_count > registry.max_components)
        return error.InvalidMixedRegistryManifest;
    var result: Manifest = .{
        .source_sha256 = schedule.source_sha256,
        .canonical_ir_sha256 = schedule.canonical_ir_sha256,
        .fixed_root = schedule.fixed_root,
        .selected_manifest_sha256 = schedule.digest,
        .descriptor_sha256 = identities.digest,
        .call_count = schedule.call_count,
        .calls = schedule.calls,
        .entry_count = schedule.slot_count,
        .main_columns = schedule.main_columns,
        .interaction_columns = schedule.interaction_columns,
        .total_constraints = schedule.total_constraints,
    };
    var main_at: u32 = 0;
    var interaction_at: u32 = 0;
    var constraint_at: u32 = 0;
    var relation_domain: registry.RelationDomain = .{};
    for (schedule.slots[0..schedule.slot_count], result.entries[0..schedule.slot_count], 0..) |slot, *entry, index| {
        const choice = try registry.forSlot(index, schedule.call_count);
        const spec = choice.constructor;
        // These source-selected constructors share one interaction challenge.
        // Distinct tuple layouts must never alias under one relation ID.
        try relation_domain.admitConstructor(spec);
        const source_kind: mixed.SourceKind = switch (spec.key) {
            .bundled_circuit => .bundled_circuit,
            .pair_chip => .pair_chip,
            .pair_bridge => .pair_bridge,
            .many_chip => .many_chip,
            .many_bridge => .many_bridge,
        };
        if (slot.source_kind != source_kind or slot.call_id != choice.call_id or
            slot.proof_index != index or slot.claimed_sum_index != index or
            slot.main_offset != main_at or slot.interaction_offset != interaction_at or
            slot.constraint_offset != constraint_at or
            slot.preprocessed_count != (if (index == 0) @as(u8, 8) else @as(u8, 0)) or
            slot.relation_count != spec.relation_count or
            !std.mem.eql(u32, slot.relation_ids[0..slot.relation_count], spec.relation_ids[0..spec.relation_count]))
            return error.InvalidMixedRegistryManifest;
        if (index != 0 and (slot.main_columns != spec.main_columns or
            slot.interaction_columns != spec.interaction_columns or
            slot.n_constraints != spec.n_constraints or
            slot.evaluation_log_size != slot.trace_log_size + spec.evaluation_log_delta or
            slot.preprocessed_count != 0))
            return error.InvalidMixedRegistryManifest;
        entry.* = .{
            .registry_key = spec.key,
            .registry_id = spec.id,
            .registry_version = spec.version,
            .role = spec.role,
            .call_id = choice.call_id,
            .proof_index = slot.proof_index,
            .claimed_sum_index = slot.claimed_sum_index,
            .trace_log_size = slot.trace_log_size,
            .evaluation_log_size = slot.evaluation_log_size,
            .main_offset = slot.main_offset,
            .main_columns = slot.main_columns,
            .interaction_offset = slot.interaction_offset,
            .interaction_columns = slot.interaction_columns,
            .constraint_offset = slot.constraint_offset,
            .n_constraints = slot.n_constraints,
            .preprocessed_indices = slot.preprocessed_indices,
            .preprocessed_count = slot.preprocessed_count,
            .relation_ids = slot.relation_ids,
            .relation_count = slot.relation_count,
            .air_source_sha256 = slot.air_source_sha256,
            .program_binding_sha256 = slot.program_binding_sha256,
        };
        main_at = try std.math.add(u32, main_at, slot.main_columns);
        interaction_at = try std.math.add(u32, interaction_at, slot.interaction_columns);
        constraint_at = try std.math.add(u32, constraint_at, slot.n_constraints);
    }
    if (main_at != schedule.main_columns or interaction_at != schedule.interaction_columns or
        constraint_at != schedule.total_constraints)
        return error.InvalidMixedRegistryManifest;
    // A stale digest would let the manifest label changed live geometry with
    // the previous schedule identity. The source-pinned caller remains the
    // authority even when this check passes.
    if (!mixed.hasCurrentDigest(schedule)) return error.InvalidMixedRegistryManifest;
    result.digest = digest(&result);
    return result;
}

pub fn fromSource(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) !Manifest {
    const selected = try mixed.inspectSource(allocator, source, air_bytes);
    return fromSchedule(&selected);
}

/// Reconstruct from literal verifier-owned source; a recomputed candidate
/// digest cannot authorize changed role, relation, source, span or claim slot.
pub fn requireSource(allocator: std.mem.Allocator, candidate: *const Manifest, source: []const u8, air_bytes: []const u8) !void {
    if (candidate.schema_version != version or candidate.registry_version != registry.version or
        candidate.entry_count == 0 or candidate.entry_count > registry.max_components)
        return error.InvalidMixedRegistryManifest;
    const expected = try fromSource(allocator, source, air_bytes);
    if (!std.meta.eql(candidate.*, expected)) return error.InvalidMixedRegistryManifest;
}

fn digest(value: *const Manifest) Digest {
    var h = Sha256.init(.{});
    h.update("S31-MIXED-REGISTRY-MANIFEST-V1\x00");
    hashInt(&h, value.schema_version);
    hashInt(&h, value.registry_version);
    h.update(&value.source_sha256);
    h.update(&value.canonical_ir_sha256);
    h.update(&value.fixed_root);
    h.update(&value.selected_manifest_sha256);
    h.update(&value.descriptor_sha256);
    hashInt(&h, value.call_count);
    for (value.calls[0..value.call_count]) |call| {
        inline for (.{ call.call_id, call.source_node_id, call.input_node_id, call.rounds, call.constant }) |number| hashInt(&h, number);
        for (call.input) |address| hashInt(&h, address);
        for (call.output) |address| hashInt(&h, address);
    }
    hashInt(&h, @as(u32, @intCast(value.entry_count)));
    for (value.entrySlice()) |entry| {
        hashInt(&h, @as(u8, @intFromEnum(entry.registry_key)));
        hashInt(&h, entry.registry_id);
        hashInt(&h, entry.registry_version);
        hashInt(&h, @as(u8, @intFromEnum(entry.role)));
        hashInt(&h, @as(u8, @intFromBool(entry.call_id != null)));
        if (entry.call_id) |id| hashInt(&h, id);
        inline for (.{ entry.proof_index, entry.claimed_sum_index, entry.trace_log_size, entry.evaluation_log_size, entry.main_offset, entry.main_columns, entry.interaction_offset, entry.interaction_columns, entry.constraint_offset, entry.n_constraints }) |number| hashInt(&h, number);
        hashInt(&h, entry.preprocessed_count);
        for (entry.preprocessed_indices[0..entry.preprocessed_count]) |column| hashInt(&h, column);
        hashInt(&h, entry.relation_count);
        for (entry.relation_ids[0..entry.relation_count]) |relation| hashInt(&h, relation);
        h.update(&entry.air_source_sha256);
        h.update(&entry.program_binding_sha256);
    }
    hashInt(&h, value.main_columns);
    hashInt(&h, value.interaction_columns);
    hashInt(&h, value.total_constraints);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

test "mixed registry manifest is source-derived and ordered for all bounded counts" {
    const a = std.testing.allocator;
    const air_bytes = @embedFile("s31_air_programs");
    const family = @import("test_source.zig");
    inline for (1..registry.max_calls + 1) |n| {
        const source = family.forCount(n);
        const selected = try mixed.inspectSource(a, source, air_bytes);
        const manifest = try fromSchedule(&selected);
        try requireSource(a, &manifest, source, air_bytes);
        try std.testing.expectEqual(@as(usize, 1 + 2 * n), manifest.entry_count);
        for (manifest.entrySlice(), 0..) |entry, index| {
            try std.testing.expectEqual(@as(u32, @intCast(index)), entry.proof_index);
            try std.testing.expectEqual(@as(u32, @intCast(index)), entry.claimed_sum_index);
            try std.testing.expectEqual((try registry.forSlot(index, n)).constructor.key, entry.registry_key);
        }
        var changed = manifest;
        changed.entries[changed.entry_count - 1].registry_id ^= 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.entries[1].relation_ids[0] ^= 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.entries[changed.entry_count - 1].claimed_sum_index = 0;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.entries[1].role = .bridge;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        std.mem.swap(Entry, &changed.entries[1], &changed.entries[2]);
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.calls[0].input[0] ^= 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.descriptor_sha256[0] ^= 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        changed = manifest;
        changed.fixed_root[0] ^= 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(a, &changed, source, air_bytes));
        var altered_schedule = selected;
        altered_schedule.lookup_envelope.?.integerized_absolute_weight += 1;
        try std.testing.expectError(error.InvalidMixedLookupBudget, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.slots[0].trace_log_size += 1;
        try std.testing.expectError(error.InvalidMixedLookupBudget, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.lookup_envelope = null;
        try std.testing.expectError(error.InvalidMixedLookupBudget, fromSchedule(&altered_schedule));
        // PCS and local AIR closure are bound indirectly through the selected
        // schedule digest. Reject a mutable schedule carrying stale identity.
        altered_schedule = selected;
        altered_schedule.native_geometry.?.pcs.fri_config.n_queries += 1;
        try std.testing.expectError(error.InvalidMixedRegistryManifest, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.native_geometry.?.mask_points_sha256[0] ^= 1;
        try std.testing.expectError(error.InvalidMixedRegistryManifest, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.native_geometry.?.local_air_dependency_sha256[0] ^= 1;
        try std.testing.expectError(error.InvalidMixedRegistryManifest, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.slots[0].air_source_sha256[0] ^= 1;
        try std.testing.expectError(error.InvalidMixedRegistryManifest, fromSchedule(&altered_schedule));
        altered_schedule = selected;
        altered_schedule.native_geometry.?.tree_columns[0] =
            @intCast(altered_schedule.native_geometry.?.columns[0].len + 1);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, fromSchedule(&altered_schedule));
    }
}

test "mixed registry manifest rejects changed public and private source at N4" {
    const a = std.testing.allocator;
    const air_bytes = @embedFile("s31_air_programs");
    const source = @embedFile("../../examples/boundary/mixed_four.s31.json");
    const manifest = try fromSource(a, source, air_bytes);
    try requireSource(a, &manifest, source, air_bytes);

    const changed_public = try std.mem.replaceOwned(u8, a, source, "\"public_outputs\": [\"sum\", \"product\"]", "\"public_outputs\": [\"product\", \"sum\"]");
    defer a.free(changed_public);
    try std.testing.expect(!std.mem.eql(u8, source, changed_public));
    if (requireSource(a, &manifest, changed_public, air_bytes)) |_| return error.AcceptedChangedPublicSource else |_| {}

    const changed_private = try a.dupe(u8, source);
    defer a.free(changed_private);
    const private_at = std.mem.indexOf(u8, changed_private, "\"constant\": 16") orelse unreachable;
    changed_private[private_at + "\"constant\": ".len + 1] = '7';
    if (requireSource(a, &manifest, changed_private, air_bytes)) |_| return error.AcceptedChangedPrivateSource else |_| {}
}
