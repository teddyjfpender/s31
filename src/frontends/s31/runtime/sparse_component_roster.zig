//! Source-derived AIR roster for the three-component sparse-gate profile.
//! The native verifier reconstructs this from the embedded source. The roster
//! is key metadata; the legacy sparse proof transcript remains unchanged.
const std = @import("std");
const circuit = @import("stwo_circuit_frontend");
const shared = @import("gate_component_roster.zig");

const Sha256 = std.crypto.hash.sha2.Sha256;
const list = circuit.common.component_list;
const sparse = circuit.common.sparse_arithmetic;

pub const Manifest = shared.Manifest;
pub const Generated = shared.Generated;

fn hex(allocator: std.mem.Allocator, bytes: [32]u8) ![]const u8 {
    return try allocator.dupe(u8, &std.fmt.bytesToHex(bytes, .lower));
}

pub fn generate(
    backing: std.mem.Allocator,
    pp: *const sparse.Circuit,
    program_digest: [32]u8,
    ir_digest: [32]u8,
    root: [32]u8,
    circuit_hash: [32]u8,
    air_bundle_sha256: []const u8,
) !Generated {
    var arena = std.heap.ArenaAllocator.init(backing);
    errdefer arena.deinit();
    const allocator = arena.allocator();
    const layout = pp.layout();
    const facts = list.component_facts.toArray();
    const indices = sparse.active_component_indices;
    const components = try allocator.alloc(shared.Component, indices.len);
    for (components, indices, 0..) |*item, source_index, proof_index| {
        const fact = facts[source_index];
        const size_source: []const u8, const log_size: u32 = switch (fact.log_size) {
            .fixed => |value| .{ "fixed", value },
            .preprocessed_column => |id| .{ id, layout.logSize(id) orelse return error.InvalidSparseComponentRoster },
        };
        item.* = .{
            .name = list.COMPONENT_NAMES[source_index],
            .source_index = @intCast(source_index),
            .proof_index = @intCast(proof_index),
            .claimed_sum_index = @intCast(proof_index),
            .trace_log_size = log_size,
            .base_trace_columns = fact.trace_columns,
            .interaction_trace_columns = fact.interaction_columns,
            .log_size_source = size_source,
            .lookup_uses_per_row = fact.relation_uses_per_row,
        };
    }
    const columns = try allocator.alloc(shared.Column, pp.columns.len);
    for (pp.columns, columns, layout.entries, 0..) |column, *item, entry, index| {
        if (!std.mem.eql(u8, column.id, entry.id) or column.logSize() != entry.log_size)
            return error.InvalidSparseComponentRoster;
        var hasher = Sha256.init(.{});
        var word: [4]u8 = undefined;
        for (column.values) |value| {
            std.mem.writeInt(u32, &word, value.toU32(), .little);
            hasher.update(&word);
        }
        var column_digest: [32]u8 = undefined;
        hasher.final(&column_digest);
        item.* = .{
            .id = column.id,
            .commitment_index = index,
            .log_size = entry.log_size,
            .rows = column.values.len,
            .values_sha256 = try hex(allocator, column_digest),
        };
    }
    return .{ .arena = arena, .value = .{
        .schema = "s31-component-roster-sparse-gate-v1",
        .profile = "sparse-v3",
        .program_sha256 = try hex(allocator, program_digest),
        .canonical_ir_sha256 = try hex(allocator, ir_digest),
        .air_bundle_sha256 = air_bundle_sha256,
        .preprocessed_root = try hex(allocator, root),
        .circuit_hash = try hex(allocator, circuit_hash),
        .claimed_sums = @intCast(indices.len),
        .components = components,
        .preprocessed_columns = columns,
    } };
}

pub fn digest(allocator: std.mem.Allocator, manifest: Manifest) ![32]u8 {
    return shared.digestWithDomain(allocator, manifest, "S31-SPARSE-GATE-COMPONENT-ROSTER-V1\x00");
}
