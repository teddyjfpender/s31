//! Auditable, source-derived component manifest for the direct-gate profile.
//! The native verifier reconstructs this from its sealed source and AIR.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");

const direct = circuit.common.direct_arithmetic;
const Sha256 = std.crypto.hash.sha2.Sha256;

pub const TraceSpan = struct { tree: u32, start: u32, end: u32 };

pub const Component = struct {
    name: []const u8,
    source_index: u32,
    proof_index: u32,
    trace_log_size: u32,
    evaluation_log_size: u32,
    base_trace_columns: usize,
    interaction_trace_columns: usize,
    n_constraints: u32,
    random_coefficient_offset: u32,
    trace_spans: []const TraceSpan,
    preprocessed_indices: []const u32,
    program_binding_sha256: []const u8,
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
    composition_plan_hash: u64,
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

/// Generate from concrete preprocessed values and the selected, rebound AIR.
/// The AIR bundle bytes are hashed in the component program binding, so a
/// 64-bit semantic hash alone is never treated as a cryptographic identity.
pub fn directGate(
    backing: std.mem.Allocator,
    pp: *const direct.Circuit,
    air_bytes: []const u8,
    program_digest: [32]u8,
    ir_digest: [32]u8,
    preprocessed_root: [32]u8,
    circuit_hash: [32]u8,
) !Generated {
    var arena = std.heap.ArenaAllocator.init(backing);
    errdefer arena.deinit();
    const allocator = arena.allocator();
    var template = try cpu.air.parse(allocator, air_bytes);
    defer template.deinit();
    const layout = pp.layout();
    var bound = try cpu.air.bindDirectArithmetic(allocator, &template, pp.traceLogSize(), &layout);
    defer bound.deinit();
    if (bound.components.len != 1 or pp.columns.len != 8) return error.InvalidComponentManifest;
    const selected = bound.components[0];
    if (!std.mem.eql(u8, selected.label, "qm31_ops") or selected.random_coefficient_offset != 0 or
        selected.preprocessed_indices.len != 8 or bound.total_constraints != selected.n_constraints)
        return error.InvalidComponentManifest;

    const spans = try allocator.alloc(TraceSpan, selected.trace_spans.len);
    for (selected.trace_spans, spans) |span, *copy| copy.* = .{
        .tree = span.tree,
        .start = span.start,
        .end = span.end,
    };
    const indices = try allocator.dupe(u32, selected.preprocessed_indices);
    const components = try allocator.alloc(Component, 1);
    const facts = circuit.common.component_list.component_facts.qm31_ops;
    var program_hash = Sha256.init(.{});
    program_hash.update("S31-DIRECT-GATE-PROGRAM-V1\x00");
    program_hash.update(air_bytes);
    var index_word: [4]u8 = undefined;
    std.mem.writeInt(u32, &index_word, 1, .little);
    program_hash.update(&index_word);
    var part_word: [8]u8 = undefined;
    for (selected.parts) |part| {
        std.mem.writeInt(u64, &part_word, part.semantic_hash, .little);
        program_hash.update(&part_word);
    }
    var program_hash_bytes: [32]u8 = undefined;
    program_hash.final(&program_hash_bytes);
    components[0] = .{
        .name = selected.label,
        .source_index = 1,
        .proof_index = 0,
        .trace_log_size = selected.trace_log_size,
        .evaluation_log_size = selected.evaluation_log_size,
        .base_trace_columns = facts.trace_columns,
        .interaction_trace_columns = facts.interaction_columns,
        .n_constraints = selected.n_constraints,
        .random_coefficient_offset = selected.random_coefficient_offset,
        .trace_spans = spans,
        .preprocessed_indices = indices,
        .program_binding_sha256 = try hex(allocator, program_hash_bytes),
    };

    const columns = try allocator.alloc(Column, pp.columns.len);
    for (pp.columns, columns, 0..) |column, *item, index| {
        if (!std.mem.eql(u8, column.id, layout.entries[index].id))
            return error.InvalidComponentManifest;
        var values_hash = Sha256.init(.{});
        var word: [4]u8 = undefined;
        for (column.values) |value| {
            std.mem.writeInt(u32, &word, value.toU32(), .little);
            values_hash.update(&word);
        }
        var digest: [32]u8 = undefined;
        values_hash.final(&digest);
        item.* = .{
            .id = column.id,
            .commitment_index = index,
            .log_size = column.logSize(),
            .rows = column.values.len,
            .values_sha256 = try hex(allocator, digest),
        };
    }

    var bundle_digest: [32]u8 = undefined;
    Sha256.hash(air_bytes, &bundle_digest, .{});
    if (!std.mem.eql(u8, &std.fmt.bytesToHex(bundle_digest, .lower), cpu.air.bundle_sha256))
        return error.AirBundleMismatch;
    return .{ .arena = arena, .value = .{
        .schema = "s31-component-manifest-direct-gate-v1",
        .profile = "direct-m31-v4",
        .program_sha256 = try hex(allocator, program_digest),
        .canonical_ir_sha256 = try hex(allocator, ir_digest),
        .air_bundle_sha256 = try hex(allocator, bundle_digest),
        .preprocessed_root = try hex(allocator, preprocessed_root),
        .circuit_hash = try hex(allocator, circuit_hash),
        .composition_plan_hash = bound.plan_hash,
        .claimed_sums = 1,
        .components = components,
        .preprocessed_columns = columns,
    } };
}

pub fn matches(allocator: std.mem.Allocator, sealed: Manifest, generated: Manifest) !bool {
    const left = try std.json.Stringify.valueAlloc(allocator, sealed, .{});
    defer allocator.free(left);
    const right = try std.json.Stringify.valueAlloc(allocator, generated, .{});
    defer allocator.free(right);
    return std.mem.eql(u8, left, right);
}

fn hex(allocator: std.mem.Allocator, digest: [32]u8) ![]const u8 {
    const encoded = std.fmt.bytesToHex(digest, .lower);
    return allocator.dupe(u8, &encoded);
}
