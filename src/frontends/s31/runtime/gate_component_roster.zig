//! Source-derived, verifier-checked roster for the legacy 11-component gate AIR.
//! This describes the actual compiled circuit geometry. It does not change the
//! legacy proof transcript or claim that a manifest digest is mixed into it.
const std = @import("std");
const circuit = @import("stwo_circuit_frontend");

const Sha256 = std.crypto.hash.sha2.Sha256;
const list = circuit.common.component_list;
const preprocessed = circuit.common.preprocessed;

pub const Component = struct {
    name: []const u8,
    source_index: u32,
    proof_index: u32,
    claimed_sum_index: u32,
    trace_log_size: u32,
    base_trace_columns: usize,
    interaction_trace_columns: usize,
    log_size_source: []const u8,
    lookup_uses_per_row: []const list.RelationUse,
};

pub const Column = struct {
    id: []const u8,
    commitment_index: usize,
    log_size: u32,
    rows: usize,
    values_sha256: []const u8,
};

pub const Manifest = struct {
    schema: []const u8,
    profile: []const u8,
    program_sha256: []const u8,
    canonical_ir_sha256: []const u8,
    air_bundle_sha256: []const u8,
    preprocessed_root: []const u8,
    circuit_hash: []const u8,
    claimed_sums: u32,
    components: []const Component,
    preprocessed_columns: []const Column,
};

pub const Generated = struct {
    arena: std.heap.ArenaAllocator,
    value: Manifest,

    pub fn deinit(self: *Generated) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

fn hex(allocator: std.mem.Allocator, bytes: [32]u8) ![]const u8 {
    return try allocator.dupe(u8, &std.fmt.bytesToHex(bytes, .lower));
}

pub fn generate(
    backing: std.mem.Allocator,
    pp: *const preprocessed.PreprocessedCircuit,
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
    const log_sizes = (try list.circuitComponentLogSizes(&layout)).toArray();
    const facts = list.component_facts.toArray();
    const components = try allocator.alloc(Component, list.N_COMPONENTS);
    for (components, facts, log_sizes, 0..) |*item, fact, log_size, index| {
        item.* = .{
            .name = list.COMPONENT_NAMES[index],
            .source_index = @intCast(index),
            .proof_index = @intCast(index),
            .claimed_sum_index = @intCast(index),
            .trace_log_size = log_size,
            .base_trace_columns = fact.trace_columns,
            .interaction_trace_columns = fact.interaction_columns,
            .log_size_source = switch (fact.log_size) {
                .fixed => "fixed",
                .preprocessed_column => |id| id,
            },
            .lookup_uses_per_row = fact.relation_uses_per_row,
        };
    }
    const columns = try allocator.alloc(Column, pp.columns.len);
    for (pp.columns, columns, layout.entries, 0..) |column, *item, entry, index| {
        if (!std.mem.eql(u8, column.id, entry.id) or column.logSize() != entry.log_size)
            return error.InvalidGateComponentRoster;
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
        .schema = "s31-component-roster-gate-v1",
        .profile = "circuit-v1",
        .program_sha256 = try hex(allocator, program_digest),
        .canonical_ir_sha256 = try hex(allocator, ir_digest),
        .air_bundle_sha256 = air_bundle_sha256,
        .preprocessed_root = try hex(allocator, root),
        .circuit_hash = try hex(allocator, circuit_hash),
        .claimed_sums = @intCast(list.N_COMPONENTS),
        .components = components,
        .preprocessed_columns = columns,
    } };
}

pub fn digest(allocator: std.mem.Allocator, manifest: Manifest) ![32]u8 {
    const encoded = try std.json.Stringify.valueAlloc(allocator, manifest, .{});
    defer allocator.free(encoded);
    var hasher = Sha256.init(.{});
    hasher.update("S31-GATE-COMPONENT-ROSTER-V1\x00");
    hasher.update(encoded);
    var result: [32]u8 = undefined;
    hasher.final(&result);
    return result;
}
