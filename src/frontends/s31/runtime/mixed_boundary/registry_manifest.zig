//! Source-derived typed mixed registry and component manifest for 1..8 calls.
//!
//! The diagnostic digest here is not a proof transcript. Existing N=3 and
//! N=4 proof profiles retain their distinct, frozen schedule digests and tags.
const std = @import("std");
const core = @import("stwo_core");
const cpu = @import("stwo_circuit_cpu_integration");
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
    try mixed.requireFreshOutputPorts(schedule.calls[0..schedule.call_count]);
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
        // A call's private circuit ports and its chip/bridge program binding
        // are one identity. Do not accept an internally resealed schedule
        // that retargets an endpoint while retaining the old native bindings.
        if (choice.call_id) |id| {
            if (id >= schedule.call_count or
                !std.meta.eql(slot.program_binding_sha256, mixed.nativeProgramBinding(source_kind, slot.air_source_sha256, schedule.calls[id])))
                return error.InvalidMixedProgramBinding;
        }
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
    try requireNativeGeometry(&result, &(schedule.native_geometry orelse return error.InvalidMixedLiveManifestBinding));
    // A stale digest would let the manifest label changed live geometry with
    // the previous schedule identity. The source-pinned caller remains the
    // authority even when this check passes.
    if (!mixed.hasCurrentDigest(schedule)) return error.InvalidMixedRegistryManifest;
    result.digest = digest(&result);
    return result;
}

/// Check ordered native components, column spans and the native AIR's
/// one-or-two-point mask arity. Exact mask widths and evaluation points are
/// authenticated through the source-rebuilt selected geometry and its digest;
/// this local check alone is not a verifier key. The engine independently
/// reconstructs handles from source at proof admission.
pub fn requireNativeGeometry(manifest: *const Manifest, geometry: *const cpu.direct_mixed_schedule.Geometry) !void {
    const composition_columns = core.verifier_types.compositionColumnCount(
        geometry.composition_split,
        core.fields.qm31.SECURE_EXTENSION_DEGREE,
    ) orelse return error.InvalidMixedLiveManifestBinding;
    const composition_width = std.math.cast(u32, composition_columns) orelse
        return error.InvalidMixedLiveManifestBinding;
    if (composition_width > cpu.direct_mixed_schedule.max_tree_width)
        return error.InvalidMixedLiveManifestBinding;
    const extended_composition_log = std.math.add(
        u32,
        geometry.composition_log_size,
        geometry.pcs.fri_config.log_blowup_factor,
    ) catch return error.InvalidMixedLiveManifestBinding;
    const extended_fixed_log = std.math.add(
        u32,
        manifest.entries[0].trace_log_size,
        geometry.pcs.fri_config.log_blowup_factor,
    ) catch return error.InvalidMixedLiveManifestBinding;
    if (manifest.call_count == 0 or manifest.call_count > registry.max_calls or
        manifest.entry_count != 1 + 2 * @as(usize, manifest.call_count) or
        geometry.version != cpu.direct_mixed_schedule.version or
        geometry.slot_count != manifest.entry_count or geometry.slot_count > geometry.slots.len or
        geometry.tree_columns[0] != 8 or geometry.tree_columns[1] != manifest.main_columns or
        geometry.tree_columns[2] != manifest.interaction_columns or
        geometry.tree_columns[3] != composition_width or
        geometry.tree_lifting_log_sizes[0] != geometry.pcs.preprocessed_lifting_log_size or
        geometry.pcs.preprocessed_lifting_log_size != extended_fixed_log or
        geometry.tree_lifting_log_sizes[1] != geometry.pcs.trace_lifting_log_size or
        geometry.tree_lifting_log_sizes[2] != geometry.pcs.trace_lifting_log_size or
        geometry.tree_lifting_log_sizes[3] != geometry.pcs.trace_lifting_log_size or
        extended_composition_log > geometry.tree_lifting_log_sizes[3] or
        geometry.tree_columns[0] > geometry.columns[0].len or
        geometry.tree_columns[1] > geometry.columns[1].len or
        geometry.tree_columns[2] > geometry.columns[2].len)
        return error.InvalidMixedLiveManifestBinding;
    var max_column_log_size = geometry.composition_log_size;
    for (geometry.columns[0][0..geometry.tree_columns[0]]) |column| {
        if (column.log_size != manifest.entries[0].trace_log_size or
            column.mask_width == 0 or column.mask_width > 2)
            return error.InvalidMixedLiveManifestBinding;
        max_column_log_size = @max(max_column_log_size, column.log_size);
    }
    for (manifest.entrySlice(), geometry.slotSlice(), 0..) |entry, live, index| {
        const kind: ?cpu.direct_mixed_admission.SourceKind = switch (entry.registry_key) {
            .bundled_circuit => null,
            .pair_chip => .pair_chip,
            .pair_bridge => .pair_bridge,
            .many_chip => .many_chip,
            .many_bridge => .many_bridge,
        };
        if (entry.proof_index != index or entry.claimed_sum_index != index or
            entry.preprocessed_count > entry.preprocessed_indices.len or
            entry.relation_count > entry.relation_ids.len or
            live.preprocessed_count > live.preprocessed_indices.len or
            live.relation_count > live.relation_ids.len or
            live.kind != kind or live.call_id != entry.call_id or
            live.trace_log_size != entry.trace_log_size or
            live.evaluation_log_size != entry.evaluation_log_size or
            live.main_offset != entry.main_offset or live.main_columns != entry.main_columns or
            live.interaction_offset != entry.interaction_offset or live.interaction_columns != entry.interaction_columns or
            live.constraint_offset != entry.constraint_offset or live.n_constraints != entry.n_constraints or
            live.preprocessed_count != entry.preprocessed_count or
            live.relation_count != entry.relation_count or
            !std.mem.eql(u32, live.preprocessed_indices[0..live.preprocessed_count], entry.preprocessed_indices[0..entry.preprocessed_count]) or
            !std.mem.eql(u32, live.relation_ids[0..live.relation_count], entry.relation_ids[0..entry.relation_count]) or
            (index != 0 and !std.meta.eql(live.air_source_sha256, entry.air_source_sha256)))
            return error.InvalidMixedLiveManifestBinding;
        const main_end = std.math.add(u32, entry.main_offset, entry.main_columns) catch
            return error.InvalidMixedLiveManifestBinding;
        const interaction_end = std.math.add(u32, entry.interaction_offset, entry.interaction_columns) catch
            return error.InvalidMixedLiveManifestBinding;
        if (main_end > geometry.tree_columns[1] or interaction_end > geometry.tree_columns[2])
            return error.InvalidMixedLiveManifestBinding;
        for (geometry.columns[1][entry.main_offset..main_end]) |column| {
            if (column.log_size != entry.trace_log_size or
                column.mask_width == 0 or column.mask_width > 2)
                return error.InvalidMixedLiveManifestBinding;
            max_column_log_size = @max(max_column_log_size, column.log_size);
        }
        for (geometry.columns[2][entry.interaction_offset..interaction_end]) |column| {
            if (column.log_size != entry.trace_log_size or
                column.mask_width == 0 or column.mask_width > 2)
                return error.InvalidMixedLiveManifestBinding;
            max_column_log_size = @max(max_column_log_size, column.log_size);
        }
    }
    if (geometry.max_column_log_size != max_column_log_size or
        geometry.pcs.trace_lifting_log_size < max_column_log_size)
        return error.InvalidMixedLiveManifestBinding;
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
        const native = selected.native_geometry.?;
        try requireNativeGeometry(&manifest, &native);
        for (manifest.entrySlice(), 0..) |entry, index| {
            try std.testing.expectEqual(@as(u32, @intCast(index)), entry.proof_index);
            try std.testing.expectEqual(@as(u32, @intCast(index)), entry.claimed_sum_index);
            try std.testing.expectEqual((try registry.forSlot(index, n)).constructor.key, entry.registry_key);
        }
        // Exercise the direct live binding without relying on a stale
        // selected-schedule digest: each candidate retains a plausible native
        // shape, but would assign a different handle or polynomial column to
        // a transcript-bound manifest entry.
        var changed_native = native;
        changed_native.slots[1].call_id = if (n == 1) 7 else 1;
        if (n > 1) changed_native.slots[3].call_id = 0;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.slots[2].relation_ids[0] ^= 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.slots[1].air_source_sha256[0] ^= 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.columns[1][manifest.entries[1].main_offset].log_size += 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.columns[2][manifest.entries[2].interaction_offset].mask_width = 0;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        // Native AIR mask construction caps every live column at two points.
        // A resealed diagnostic schedule must not normalize an impossible
        // width to merely "nonzero" in the manifest-to-native check.
        inline for (0..3) |tree| {
            changed_native = native;
            changed_native.columns[tree][0].mask_width = 3;
            try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        }
        // Composition is the fourth committed tree. It has no per-column
        // mask array, but its width and lifting height still must match the
        // native PCS split rather than an arbitrary live-geometry label.
        changed_native = native;
        changed_native.tree_columns[3] = 0;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.tree_lifting_log_sizes[3] += 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        inline for (0..3) |tree| {
            changed_native = native;
            changed_native.tree_lifting_log_sizes[tree] += 1;
            try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        }
        changed_native = native;
        changed_native.max_column_log_size += 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.pcs.preprocessed_lifting_log_size += 1;
        changed_native.tree_lifting_log_sizes[0] += 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
        changed_native = native;
        changed_native.composition_log_size = changed_native.pcs.trace_lifting_log_size + 1;
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&manifest, &changed_native));
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
        try std.testing.expectError(error.InvalidMixedLiveManifestBinding, fromSchedule(&altered_schedule));
    }
}

test "mixed registry manifest refuses aliased repeat output ports" {
    const allocator = std.testing.allocator;
    const source = @import("test_source.zig").forCount(1);
    const air_bytes = @embedFile("s31_air_programs");
    const selected = try mixed.inspectSource(allocator, source, air_bytes);
    _ = try fromSchedule(&selected);

    var changed = selected;
    changed.calls[0].output[1] = changed.calls[0].output[0];
    try std.testing.expectError(error.InvalidMixedOutputPortAlias, fromSchedule(&changed));

    changed = selected;
    changed.calls[0].output[1] = changed.calls[0].input[0];
    try std.testing.expectError(error.InvalidMixedOutputPortAlias, fromSchedule(&changed));
}

test "mixed registry manifest rejects resealed AIR and polynomial shape substitutions" {
    const allocator = std.testing.allocator;
    const source = @import("test_source.zig").forCount(3);
    const air_bytes = @embedFile("s31_air_programs");
    const selected = try mixed.inspectSource(allocator, source, air_bytes);
    const authentic = try fromSchedule(&selected);
    try requireSource(allocator, &authentic, source, air_bytes);

    // Every candidate has a fresh, internally consistent diagnostic checksum.
    // Equality with verifier-owned source, rather than that checksum, decides
    // admission. Cover fields that previously had no direct mutation case.
    inline for (.{
        "selected manifest", "canonical IR",      "circuit AIR",       "circuit program",
        "fixed index",       "chip AIR",          "chip program",      "trace log",
        "evaluation log",    "main width",        "interaction width", "constraint count",
        "main total",        "interaction total", "constraint total",
    }) |case| {
        var changed = authentic;
        if (comptime std.mem.eql(u8, case, "selected manifest")) changed.selected_manifest_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "canonical IR")) changed.canonical_ir_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "circuit AIR")) changed.entries[0].air_source_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "circuit program")) changed.entries[0].program_binding_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "fixed index")) changed.entries[0].preprocessed_indices[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "chip AIR")) changed.entries[1].air_source_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "chip program")) changed.entries[1].program_binding_sha256[0] ^= 1;
        if (comptime std.mem.eql(u8, case, "trace log")) changed.entries[1].trace_log_size += 1;
        if (comptime std.mem.eql(u8, case, "evaluation log")) changed.entries[1].evaluation_log_size += 1;
        if (comptime std.mem.eql(u8, case, "main width")) changed.entries[1].main_columns += 1;
        if (comptime std.mem.eql(u8, case, "interaction width")) changed.entries[1].interaction_columns += 1;
        if (comptime std.mem.eql(u8, case, "constraint count")) changed.entries[1].n_constraints += 1;
        if (comptime std.mem.eql(u8, case, "main total")) changed.main_columns += 1;
        if (comptime std.mem.eql(u8, case, "interaction total")) changed.interaction_columns += 1;
        if (comptime std.mem.eql(u8, case, "constraint total")) changed.total_constraints += 1;
        changed.digest = digest(&changed);
        try std.testing.expectError(error.InvalidMixedRegistryManifest, requireSource(allocator, &changed, source, air_bytes));
    }

    const live = selected.native_geometry.?;
    var changed_live = live;
    changed_live.slots[1].constraint_offset += 1;
    try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&authentic, &changed_live));
    changed_live = live;
    changed_live.slots[0].preprocessed_indices[0] ^= 1;
    try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&authentic, &changed_live));
    changed_live = live;
    changed_live.tree_columns[1] += 1;
    try std.testing.expectError(error.InvalidMixedLiveManifestBinding, requireNativeGeometry(&authentic, &changed_live));
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
