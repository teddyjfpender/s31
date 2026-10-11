//! Source-bound, witness-free inspection of the mixed pair/many AIR roster.
//!
//! This API has no proof serializer or verifier. The fixed N=3 and N=4 proof
//! packages consume their regenerated schedules before proof decoding; other
//! callers must not treat this inspection result as proof authority.
const std = @import("std");
const core = @import("stwo_core");
const cpu = @import("stwo_circuit_cpu_integration");
const circuit = @import("stwo_circuit_frontend");
const binding = @import("../bounded_compiled_binding.zig");
const v4 = @import("../bounded_component_manifest.zig");
const admission = @import("../../language/bounded_call_admission.zig");

const Digest = [32]u8;
const Sha256 = std.crypto.hash.sha2.Sha256;
const Native = cpu.direct_mixed_admission;
const Mixed = cpu.direct_mixed_schedule;
pub const profile = "direct-m31-mixed-interleaved-admission-v1";
pub const max_slots = 1 + 2 * admission.max_calls;

pub const SourceKind = enum(u8) { bundled_circuit, pair_chip, pair_bridge, many_chip, many_bridge };

pub const Call = struct {
    call_id: u32 = 0,
    source_node_id: u32 = 0,
    input_node_id: u32 = 0,
    rounds: u32 = 0,
    constant: u32 = 0,
    input: [4]u32 = [_]u32{0} ** 4,
    output: [4]u32 = [_]u32{0} ** 4,
};

pub const Slot = struct {
    source_kind: SourceKind = .bundled_circuit,
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

/// Rebuilt source-owned candidate. `digest` is an inspection manifest digest,
/// its authentication depends on a source-pinned caller such as package.zig.
pub const SelectedSchedule = struct {
    policy_version: u32 = Native.policy_version,
    source_sha256: Digest,
    canonical_ir_sha256: Digest,
    fixed_root: Digest,
    /// Rebuilt V4 manifest is an audit anchor, not this profile's transcript.
    source_manifest_sha256: Digest,
    call_count: u8,
    calls: [admission.max_calls]Call = [_]Call{.{}} ** admission.max_calls,
    slot_count: usize,
    slots: [max_slots]Slot = [_]Slot{.{}} ** max_slots,
    main_columns: u32 = 0,
    interaction_columns: u32 = 0,
    total_constraints: u32 = 0,
    native_geometry: ?Mixed.Geometry = null,
    digest: Digest = [_]u8{0} ** 32,
};

pub const Projection = SelectedSchedule;

/// Reconstruct V4 source semantics and live geometry, then project them into
/// an interleaved roster: circuit, (chip i, bridge i) for each call. The
/// source-kind policy is fixed: pair AIRs for calls 0/1, many AIRs thereafter.
pub fn inspectSource(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) !SelectedSchedule {
    var inspected = try binding.inspectMany(allocator, source, air_bytes);
    defer inspected.deinit();
    const descriptors = try binding.manyProvenance(&inspected);
    try cpu.direct_many_provenance.validate(&inspected.selected_schedule, descriptors.pin(source, air_bytes));
    const manifest = inspected.generated.value;
    const count = manifest.calls.len;
    if (count == 0 or count > admission.max_calls or manifest.components.len != 1 + 2 * count)
        return error.InvalidMixedSourceRoster;
    var result: SelectedSchedule = .{
        .source_sha256 = inspected.topology.source_sha256,
        .canonical_ir_sha256 = inspected.topology.canonical_ir_sha256,
        .fixed_root = inspected.preprocessed_root,
        .source_manifest_sha256 = inspected.manifest_precommitment,
        .call_count = @intCast(count),
        .slot_count = 1 + 2 * count,
    };
    for (manifest.calls, result.calls[0..count]) |source_call, *call| {
        const endpoints = source_call.endpoints orelse return error.InvalidMixedSourceRoster;
        call.* = .{
            .call_id = source_call.call_id,
            .source_node_id = source_call.source_node_id,
            .input_node_id = source_call.input_node_id,
            .rounds = source_call.rounds,
            .constant = source_call.constant,
            .input = endpoints.input,
            .output = endpoints.output,
        };
    }
    var main_at: u32 = 0;
    var interaction_at: u32 = 0;
    var constraint_at: u32 = 0;
    const circuit_component = manifest.components[0];
    const circuit_fact = inspected.selected_schedule.geometry.live.facts[0];
    if (circuit_component.source != .bundled_air or circuit_component.role != .circuit or
        circuit_component.call_id != null or circuit_fact.kind != .circuit or
        circuit_component.preprocessed_indices.len != 8 or circuit_component.lookup_relation_ids.len != 1)
        return error.InvalidMixedSourceRoster;
    const circuit_source = circuit_component.source.bundled_air;
    var fixed_indices: [8]u32 = undefined;
    @memcpy(&fixed_indices, circuit_component.preprocessed_indices);
    result.slots[0] = .{
        .source_kind = .bundled_circuit,
        .proof_index = 0,
        .claimed_sum_index = 0,
        .trace_log_size = circuit_component.trace_log_size,
        .evaluation_log_size = circuit_component.evaluation_log_size,
        .main_columns = try spanWidth(circuit_component.main),
        .interaction_columns = try spanWidth(circuit_component.interaction),
        .n_constraints = circuit_component.n_constraints,
        .preprocessed_indices = fixed_indices,
        .preprocessed_count = 8,
        .relation_ids = .{ circuit_component.lookup_relation_ids[0], 0 },
        .relation_count = 1,
        .air_source_sha256 = circuit_source.bundle_sha256,
        .program_binding_sha256 = circuit_source.selected_program_sha256,
    };
    try advance(&main_at, &interaction_at, &constraint_at, result.slots[0]);
    for (result.calls[0..count], 0..) |call, id| {
        if (call.call_id != id or call.constant >= core.fields.m31.Modulus)
            return error.InvalidMixedSourceRoster;
        const native_call: cpu.private_many_boundary.Call = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = core.fields.m31.M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
        inline for (.{ Native.Role.chip, Native.Role.bridge }) |role| {
            const source_index = if (role == .chip) 1 + id else 1 + count + id;
            const target_index = 1 + 2 * id + @intFromBool(role == .bridge);
            const component = manifest.components[source_index];
            const fact = try Native.inspectNative(allocator, try Native.kindForCall(call.call_id, role), native_call);
            const source_kind: SourceKind = switch (fact.kind) {
                .pair_chip => .pair_chip,
                .pair_bridge => .pair_bridge,
                .many_chip => .many_chip,
                .many_bridge => .many_bridge,
            };
            if (component.call_id == null or component.call_id.? != call.call_id or
                component.role != (if (role == .chip) v4.Role.chip else v4.Role.bridge) or
                component.source != .native_air or
                component.trace_log_size != fact.trace_log_size or
                component.evaluation_log_size != fact.evaluation_log_size or
                try spanWidth(component.main) != fact.main_columns or
                try spanWidth(component.interaction) != fact.interaction_columns or
                component.n_constraints != fact.n_constraints or
                !std.mem.eql(u32, component.lookup_relation_ids, fact.relationSlice()))
                return error.InvalidMixedSourceRoster;
            result.slots[target_index] = .{
                .source_kind = source_kind,
                .call_id = call.call_id,
                .proof_index = @intCast(target_index),
                .claimed_sum_index = @intCast(target_index),
                .trace_log_size = fact.trace_log_size,
                .evaluation_log_size = fact.evaluation_log_size,
                .main_offset = main_at,
                .main_columns = @intCast(fact.main_columns),
                .interaction_offset = interaction_at,
                .interaction_columns = @intCast(fact.interaction_columns),
                .constraint_offset = constraint_at,
                .n_constraints = @intCast(fact.n_constraints),
                .relation_ids = fact.relation_ids,
                .relation_count = @intCast(fact.relation_count),
                .air_source_sha256 = fact.source_sha256,
                .program_binding_sha256 = nativeProgramBinding(source_kind, fact.source_sha256, call),
            };
            try advance(&main_at, &interaction_at, &constraint_at, result.slots[target_index]);
        }
    }
    if (main_at != manifest.main_columns or interaction_at != manifest.interaction_columns or
        constraint_at != manifest.total_constraints or
        main_at != inspected.selected_schedule.geometry.live.tree_columns[1] or
        interaction_at != inspected.selected_schedule.geometry.live.tree_columns[2])
        return error.InvalidMixedSourceRoster;
    result.main_columns = main_at;
    result.interaction_columns = interaction_at;
    result.total_constraints = constraint_at;
    var topology_ctx = try binding.compileManyTopology(allocator, source, inspected.topology);
    defer topology_ctx.deinit();
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&topology_ctx.circuit);
    var plan: cpu.private_many_boundary.Plan = .{ .count = @intCast(count) };
    for (result.calls[0..count], plan.calls[0..count]) |call, *native_slot| {
        native_slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = core.fields.m31.M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    if (!std.meta.eql(try pp.preprocessedRoot(allocator, 1), result.fixed_root))
        return error.InvalidMixedFixedRoot;
    var template = try cpu.air.parse(allocator, air_bytes);
    defer template.deinit();
    const geometry = try Mixed.inspect(allocator, &pp, &template, plan);
    try compareLiveGeometry(&result, &geometry, &inspected.selected_schedule.geometry.live);
    result.native_geometry = geometry;
    result.digest = digestSelectedSchedule(&result);
    return result;
}

/// Compare every field against a fresh source reconstruction. A caller cannot
/// re-seal a forged slot by merely recomputing its prototype digest.
pub fn matchesSource(allocator: std.mem.Allocator, candidate: *const SelectedSchedule, source: []const u8, air_bytes: []const u8) !bool {
    const expected = try inspectSource(allocator, source, air_bytes);
    return std.meta.eql(candidate.*, expected);
}

fn spanWidth(span: v4.Span) !u32 {
    if (span.end < span.start) return error.InvalidMixedSourceRoster;
    return span.end - span.start;
}

fn compareLiveGeometry(result: *const SelectedSchedule, geometry: *const Mixed.Geometry, v4_live: *const cpu.direct_many_preflight.Inspection) !void {
    if (geometry.version != Mixed.version or geometry.slot_count != result.slot_count or
        !std.meta.eql(geometry.pcs, v4_live.pcs) or
        geometry.tree_columns[0] != v4_live.tree_columns[0] or
        geometry.tree_columns[1] != result.main_columns or
        geometry.tree_columns[2] != result.interaction_columns or
        geometry.tree_columns[3] != v4_live.tree_columns[3] or
        geometry.tree_lifting_log_sizes[0] != geometry.pcs.preprocessed_lifting_log_size or
        geometry.tree_lifting_log_sizes[1] != geometry.pcs.trace_lifting_log_size or
        geometry.tree_lifting_log_sizes[2] != geometry.pcs.trace_lifting_log_size or
        geometry.tree_lifting_log_sizes[3] != geometry.pcs.trace_lifting_log_size or
        geometry.composition_log_size != v4_live.composition_log_size or
        geometry.composition_split != v4_live.composition_split or
        geometry.max_column_log_size != v4_live.max_column_log_size)
        return error.InvalidMixedLiveGeometry;
    for (result.slots[0..result.slot_count], geometry.slotSlice(), 0..) |source, live, index| {
        if (live.kind != (if (index == 0) null else switch (source.source_kind) {
            .pair_chip => Native.SourceKind.pair_chip,
            .pair_bridge => Native.SourceKind.pair_bridge,
            .many_chip => Native.SourceKind.many_chip,
            .many_bridge => Native.SourceKind.many_bridge,
            .bundled_circuit => return error.InvalidMixedLiveGeometry,
        }) or
            live.call_id != source.call_id or
            live.trace_log_size != source.trace_log_size or
            live.evaluation_log_size != source.evaluation_log_size or
            live.main_offset != source.main_offset or live.main_columns != source.main_columns or
            live.interaction_offset != source.interaction_offset or live.interaction_columns != source.interaction_columns or
            live.constraint_offset != source.constraint_offset or live.n_constraints != source.n_constraints or
            live.preprocessed_count != source.preprocessed_count or
            live.relation_count != source.relation_count or
            !std.mem.eql(u32, live.preprocessed_indices[0..live.preprocessed_count], source.preprocessed_indices[0..source.preprocessed_count]) or
            !std.mem.eql(u32, live.relation_ids[0..live.relation_count], source.relation_ids[0..source.relation_count]) or
            (index != 0 and !std.meta.eql(live.air_source_sha256, source.air_source_sha256)))
            return error.InvalidMixedLiveGeometry;
    }
}

fn advance(main_at: *u32, interaction_at: *u32, constraint_at: *u32, slot: Slot) !void {
    main_at.* = try std.math.add(u32, main_at.*, slot.main_columns);
    interaction_at.* = try std.math.add(u32, interaction_at.*, slot.interaction_columns);
    constraint_at.* = try std.math.add(u32, constraint_at.*, slot.n_constraints);
}

fn nativeProgramBinding(kind: SourceKind, source_sha256: Digest, call: Call) Digest {
    var h = Sha256.init(.{});
    h.update("S31-MIXED-NATIVE-COMPONENT-PROTOTYPE-V1\x00");
    hashInt(&h, @as(u8, @intFromEnum(kind)));
    h.update(&source_sha256);
    hashCall(&h, call);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn digestSelectedSchedule(value: *const SelectedSchedule) Digest {
    var h = Sha256.init(.{});
    h.update("S31-MIXED-INTERLEAVED-ADMISSION-PROTOTYPE-V1\x00");
    hashInt(&h, value.policy_version);
    h.update(&value.source_sha256);
    h.update(&value.canonical_ir_sha256);
    h.update(&value.fixed_root);
    h.update(&value.source_manifest_sha256);
    hashInt(&h, value.call_count);
    for (value.calls[0..value.call_count]) |call| hashCall(&h, call);
    hashInt(&h, @as(u32, @intCast(value.slot_count)));
    for (value.slots[0..value.slot_count]) |slot| {
        hashInt(&h, @as(u8, @intFromEnum(slot.source_kind)));
        hashInt(&h, @as(u8, @intFromBool(slot.call_id != null)));
        if (slot.call_id) |id| hashInt(&h, id);
        inline for (.{ slot.proof_index, slot.claimed_sum_index, slot.trace_log_size, slot.evaluation_log_size, slot.main_offset, slot.main_columns, slot.interaction_offset, slot.interaction_columns, slot.constraint_offset, slot.n_constraints }) |number| hashInt(&h, number);
        hashInt(&h, slot.preprocessed_count);
        for (slot.preprocessed_indices[0..slot.preprocessed_count]) |index| hashInt(&h, index);
        hashInt(&h, slot.relation_count);
        for (slot.relation_ids[0..slot.relation_count]) |relation| hashInt(&h, relation);
        h.update(&slot.air_source_sha256);
        h.update(&slot.program_binding_sha256);
    }
    hashInt(&h, value.main_columns);
    hashInt(&h, value.interaction_columns);
    hashInt(&h, value.total_constraints);
    const geometry = value.native_geometry orelse unreachable;
    hashInt(&h, geometry.version);
    hashInt(&h, @as(u32, @intCast(geometry.slot_count)));
    for (geometry.slotSlice()) |slot| {
        hashInt(&h, @as(u8, @intFromBool(slot.kind != null)));
        if (slot.kind) |kind| hashInt(&h, @as(u8, @intFromEnum(kind)));
        hashInt(&h, @as(u8, @intFromBool(slot.call_id != null)));
        if (slot.call_id) |id| hashInt(&h, id);
        inline for (.{ slot.trace_log_size, slot.evaluation_log_size, slot.main_offset, slot.main_columns, slot.interaction_offset, slot.interaction_columns, slot.constraint_offset, slot.n_constraints }) |number| hashInt(&h, number);
        hashInt(&h, slot.preprocessed_count);
        for (slot.preprocessed_indices[0..slot.preprocessed_count]) |index| hashInt(&h, index);
        hashInt(&h, slot.relation_count);
        for (slot.relation_ids[0..slot.relation_count]) |relation| hashInt(&h, relation);
        h.update(&slot.air_source_sha256);
    }
    const fri = geometry.pcs.fri_config;
    inline for (.{ fri.pow_bits, fri.log_blowup_factor, fri.log_last_layer_degree_bound, fri.n_queries, fri.fold_step, geometry.pcs.trace_lifting_log_size, geometry.pcs.preprocessed_lifting_log_size }) |number| hashInt(&h, number);
    for (geometry.tree_columns) |width| hashInt(&h, width);
    for (geometry.tree_lifting_log_sizes) |height| hashInt(&h, height);
    for (geometry.tree_columns[0..3], 0..) |width, tree| {
        for (geometry.columns[tree][0..width]) |column| {
            hashInt(&h, column.log_size);
            hashInt(&h, column.mask_width);
        }
    }
    h.update(&geometry.mask_points_sha256);
    hashInt(&h, geometry.max_column_log_size);
    hashInt(&h, geometry.composition_log_size);
    hashInt(&h, geometry.composition_split);
    h.update(&geometry.local_air_dependency_sha256);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn hashCall(h: *Sha256, call: Call) void {
    inline for (.{ call.call_id, call.source_node_id, call.input_node_id, call.rounds, call.constant }) |number|
        hashInt(h, number);
    for (call.input) |address| hashInt(h, address);
    for (call.output) |address| hashInt(h, address);
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

test "mixed composition admission derives interleaved pair and many sources" {
    const allocator = std.testing.allocator;
    const air_bytes = @embedFile("s31_air_programs");
    const source =
        \\{"version":1,"name":"mixed_three","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[
        \\{"name":"r0","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},
        \\{"name":"r1","op":"repeat","lhs":"r0","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":14}]},
        \\{"name":"r2","op":"repeat","lhs":"r1","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":15}]},
        \\{"name":"sum","op":"add","lhs":"r2","rhs":"x"},{"name":"product","op":"mul","lhs":"r2","rhs":"x"}],
        \\"assertions":[],"public_outputs":["sum","product"]}
    ;
    var projected = try inspectSource(allocator, source, air_bytes);
    try std.testing.expectEqual(@as(u8, 3), projected.call_count);
    try std.testing.expectEqual(@as(usize, 7), projected.slot_count);
    try std.testing.expectEqual(SourceKind.bundled_circuit, projected.slots[0].source_kind);
    try std.testing.expectEqual(SourceKind.pair_chip, projected.slots[1].source_kind);
    try std.testing.expectEqual(SourceKind.pair_bridge, projected.slots[2].source_kind);
    try std.testing.expectEqual(SourceKind.pair_chip, projected.slots[3].source_kind);
    try std.testing.expectEqual(SourceKind.pair_bridge, projected.slots[4].source_kind);
    try std.testing.expectEqual(SourceKind.many_chip, projected.slots[5].source_kind);
    try std.testing.expectEqual(SourceKind.many_bridge, projected.slots[6].source_kind);
    try std.testing.expectEqual(@as(u32, 63), projected.main_columns);
    try std.testing.expectEqual(@as(u32, 92), projected.interaction_columns);
    const geometry = projected.native_geometry.?;
    try std.testing.expectEqual(@as(usize, 7), geometry.slot_count);
    try std.testing.expectEqual(@as(u32, 8), geometry.tree_columns[0]);
    try std.testing.expectEqual(@as(u32, 63), geometry.tree_columns[1]);
    try std.testing.expectEqual(@as(u32, 92), geometry.tree_columns[2]);
    try std.testing.expectEqual(projected.slots[5].trace_log_size, geometry.columns[1][projected.slots[5].main_offset].log_size);
    try std.testing.expect(geometry.columns[2][projected.slots[6].interaction_offset].mask_width > 0);
    try std.testing.expect(!std.meta.eql(geometry.mask_points_sha256, [_]u8{0} ** 32));
    try std.testing.expect(!std.meta.eql(geometry.local_air_dependency_sha256, [_]u8{0} ** 32));
    try std.testing.expect(try matchesSource(allocator, &projected, source, air_bytes));

    projected.slots[5].source_kind = .pair_chip;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.slots[6].relation_ids[1] ^= 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.calls[2].input[0] += 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.slots[2].program_binding_sha256[0] ^= 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.pcs.fri_config.n_queries += 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.tree_lifting_log_sizes[2] += 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.columns[1][projected.slots[5].main_offset].mask_width += 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.mask_points_sha256[0] ^= 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.local_air_dependency_sha256[0] ^= 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    projected.native_geometry.?.slots[5].air_source_sha256[0] ^= 1;
    projected.digest = digestSelectedSchedule(&projected);
    try std.testing.expect(!try matchesSource(allocator, &projected, source, air_bytes));
    projected = try inspectSource(allocator, source, air_bytes);
    const changed_source = try allocator.dupe(u8, source);
    defer allocator.free(changed_source);
    const constant_at = std.mem.indexOf(u8, changed_source, "\"constant\":15") orelse unreachable;
    changed_source[constant_at + "\"constant\":".len + 1] = '6';
    try std.testing.expect(!try matchesSource(allocator, &projected, changed_source, air_bytes));
}
