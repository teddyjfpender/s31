//! Closed, versioned constructor registry for bounded mixed pair/many AIRs.
//!
//! This chooses a component from a source-derived call ID and canonical slot.
//! It never accepts a kind nominated by a proof or package. Native facts are
//! checked against an actual registered verifier handle before use.
const std = @import("std");
const cpu = @import("stwo_circuit_cpu_integration");
const circuit = @import("stwo_circuit_frontend");

const Native = cpu.direct_mixed_admission;
pub const version: u32 = 1;
pub const max_calls = cpu.private_many_boundary.max_calls;
pub const max_components = 1 + 2 * max_calls;
pub const Role = enum(u8) { circuit, chip, bridge };
pub const Key = enum(u8) { bundled_circuit, pair_chip, pair_bridge, many_chip, many_bridge };

pub const Constructor = struct {
    key: Key,
    id: u32,
    version: u32,
    role: Role,
    relation_ids: [2]u32,
    relation_count: u8,
    main_columns: u32,
    interaction_columns: u32,
    n_constraints: u32,
    evaluation_log_delta: u32,
};

const gate_relation = circuit.common.component_list.GATE_RELATION_ID;
const chip_relation = cpu.private_many_boundary.relation_id;

pub fn constructor(key: Key) Constructor {
    return switch (key) {
        .bundled_circuit => .{
            .key = key,
            .id = 0,
            .version = version,
            .role = .circuit,
            .relation_ids = .{ gate_relation, 0 },
            .relation_count = 1,
            // Circuit geometry comes only from the selected bundled AIR.
            .main_columns = 0,
            .interaction_columns = 0,
            .n_constraints = 0,
            .evaluation_log_delta = 0,
        },
        .pair_chip, .many_chip => .{
            .key = key,
            .id = if (key == .pair_chip) 1 else 3,
            .version = version,
            .role = .chip,
            .relation_ids = .{ chip_relation, 0 },
            .relation_count = 1,
            .main_columns = 9,
            .interaction_columns = 8,
            .n_constraints = 6,
            .evaluation_log_delta = 1,
        },
        .pair_bridge, .many_bridge => .{
            .key = key,
            .id = if (key == .pair_bridge) 2 else 4,
            .version = version,
            .role = .bridge,
            .relation_ids = .{ gate_relation, chip_relation },
            .relation_count = 2,
            .main_columns = 8,
            .interaction_columns = 20,
            .n_constraints = 13,
            .evaluation_log_delta = 2,
        },
    };
}

/// The only policy in version 1: two pair calls, then bounded many calls.
pub fn forCall(call_id: u32, role: Role) !Constructor {
    if (call_id >= max_calls or role == .circuit)
        return error.UnregisteredMixedComponent;
    const pair = call_id < 2;
    return constructor(if (pair)
        (if (role == .chip) .pair_chip else .pair_bridge)
    else
        (if (role == .chip) .many_chip else .many_bridge));
}

pub const Slot = struct { call_id: ?u32, constructor: Constructor };

/// Canonical proof and claimed-sum order: circuit, then chip/bridge per call.
pub fn forSlot(index: usize, call_count: usize) !Slot {
    if (call_count == 0 or call_count > max_calls or index >= 1 + 2 * call_count)
        return error.UnregisteredMixedComponent;
    if (index == 0) return .{ .call_id = null, .constructor = constructor(.bundled_circuit) };
    const call_id: u32 = @intCast((index - 1) / 2);
    return .{
        .call_id = call_id,
        .constructor = try forCall(call_id, if (index % 2 == 1) .chip else .bridge),
    };
}

fn nativeKind(key: Key) !Native.SourceKind {
    return switch (key) {
        .pair_chip => .pair_chip,
        .pair_bridge => .pair_bridge,
        .many_chip => .many_chip,
        .many_bridge => .many_bridge,
        .bundled_circuit => error.UnregisteredMixedComponent,
    };
}

/// Instantiate the registered verifier AIR and check its live dependency and
/// geometry facts against this closed constructor table.
pub fn inspectNative(allocator: std.mem.Allocator, key: Key, call: cpu.private_many_boundary.Call) !Native.Fact {
    const spec = try forCall(call.call_id, constructor(key).role);
    if (spec.key != key) return error.UnregisteredMixedComponent;
    const fact = try Native.inspectNative(allocator, try nativeKind(key), call);
    if (fact.call_id != call.call_id or fact.kind != try nativeKind(key) or
        fact.main_columns != @as(usize, spec.main_columns) or
        fact.interaction_columns != @as(usize, spec.interaction_columns) or
        fact.n_constraints != @as(usize, spec.n_constraints) or
        fact.evaluation_log_size != fact.trace_log_size + spec.evaluation_log_delta or
        fact.relation_count != @as(usize, spec.relation_count) or
        !std.mem.eql(u32, fact.relationSlice(), spec.relation_ids[0..spec.relation_count]))
        return error.UnregisteredMixedComponent;
    return fact;
}

test "mixed registry chooses bounded pair then many components in sum order" {
    for (1..max_calls + 1) |n| {
        try std.testing.expectEqual(Key.bundled_circuit, (try forSlot(0, n)).constructor.key);
        for (0..n) |id| {
            const chip = try forSlot(1 + 2 * id, n);
            const bridge = try forSlot(2 + 2 * id, n);
            try std.testing.expectEqual(@as(?u32, @intCast(id)), chip.call_id);
            try std.testing.expectEqual(@as(?u32, @intCast(id)), bridge.call_id);
            try std.testing.expectEqual(if (id < 2) Key.pair_chip else Key.many_chip, chip.constructor.key);
            try std.testing.expectEqual(if (id < 2) Key.pair_bridge else Key.many_bridge, bridge.constructor.key);
            try std.testing.expectEqual(@as(u32, if (id < 2) 1 else 3), chip.constructor.id);
            try std.testing.expectEqual(@as(u32, if (id < 2) 2 else 4), bridge.constructor.id);
        }
        try std.testing.expectError(error.UnregisteredMixedComponent, forSlot(1 + 2 * n, n));
    }
    try std.testing.expectError(error.UnregisteredMixedComponent, forSlot(0, 0));
}
