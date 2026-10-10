//! Auditable, source-derived component manifests for direct-M31 profiles.
//! The native verifier reconstructs this from its sealed source and AIR.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");

const direct = circuit.common.direct_arithmetic;
const direct_trace = circuit.witness.direct_arithmetic;
const Sha256 = std.crypto.hash.sha2.Sha256;
const chip = cpu.repeated_step_chip;
const bridge = cpu.private_boundary_bridge;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

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
    /// Native components use source_index 0 and bind their pinned Zig AIR.
    claimed_sum_index: ?u32 = null,
    main_trace_span: ?TraceSpan = null,
    interaction_trace_span: ?TraceSpan = null,
    max_constraint_log_degree_bound: ?u32 = null,
    lookup_relation_ids: ?[]const u32 = null,
};

/// The current direct chip has exactly one call. Its six-field lookup tuple
/// has no call ID, so this type must not be reused for multiple calls.
pub const ChipCall = struct {
    call_id: u32,
    relation_id: u32,
    rounds: u32,
    constant: u32,
    private_boundary: ?direct.PrivateBoundary,
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
    chip_call: ?ChipCall = null,
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
        // The bound AIR is deinitialized before this manifest is serialized.
        // Arena free can poison its label, so retain an independently owned copy.
        .name = try allocator.dupe(u8, selected.label),
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
    // Finish all arena allocations before copying the arena into Generated.
    // Copying it while value fields still allocate would retain an old
    // end_index, so the next extension could overwrite these digest strings.
    const value: Manifest = .{
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
    };
    return .{ .arena = arena, .value = value };
}

/// Extend the source-derived direct gate manifest with the two native AIRs
/// selected by the existing one-chip prover/verifier. The trace offsets and
/// sum positions below mirror the selected native component constructors;
/// both are checked again when a key is opened by the sealed verifier.
pub fn directChip(
    backing: std.mem.Allocator,
    pp: *const direct.Circuit,
    air_bytes: []const u8,
    program_digest: [32]u8,
    ir_digest: [32]u8,
    preprocessed_root: [32]u8,
    circuit_hash: [32]u8,
    rounds: u32,
    constant: u32,
    boundary: ?direct.PrivateBoundary,
) !Generated {
    const chip_log = try chip.validateRounds(rounds);
    if (constant >= core.fields.m31.Modulus) return error.InvalidComponentManifest;
    if (boundary) |addresses| {
        // The compiled circuit owns all addresses. Bounds and uniqueness
        // were checked when this preprocessed circuit was constructed.
        if (pp.private_boundary == null or !std.meta.eql(pp.private_boundary.?, addresses))
            return error.InvalidComponentManifest;
    } else if (pp.private_boundary != null) return error.InvalidComponentManifest;

    var generated = try directGate(backing, pp, air_bytes, program_digest, ir_digest, preprocessed_root, circuit_hash);
    errdefer generated.deinit();
    const allocator = generated.arena.allocator();
    const count: usize = if (boundary != null) 3 else 2;
    const components = try allocator.alloc(Component, count);
    const circuit_main: u32 = @intCast(direct_trace.main_width);
    const circuit_interaction: u32 = @intCast(direct_trace.interaction_width);
    if (components.len != count or generated.value.components[0].base_trace_columns != circuit_main or
        generated.value.components[0].interaction_trace_columns != circuit_interaction)
        return error.InvalidComponentManifest;
    var circuit_main_found = false;
    var circuit_interaction_found = false;
    for (generated.value.components[0].trace_spans) |span| {
        if (span.tree == 1 and span.start == 0 and span.end == circuit_main) circuit_main_found = true;
        if (span.tree == 2 and span.start == 0 and span.end == circuit_interaction) circuit_interaction_found = true;
    }
    if (!circuit_main_found or !circuit_interaction_found) return error.InvalidComponentManifest;
    components[0] = generated.value.components[0];
    components[0].claimed_sum_index = 0;
    components[0].main_trace_span = .{ .tree = 1, .start = 0, .end = circuit_main };
    components[0].interaction_trace_span = .{ .tree = 2, .start = 0, .end = circuit_interaction };
    components[0].max_constraint_log_degree_bound = components[0].evaluation_log_size;
    components[0].lookup_relation_ids = try allocator.dupe(u32, &.{circuit.common.component_list.GATE_RELATION_ID});
    const chip_air: chip.Component = .{
        .log_size = chip_log,
        .constant = M31.fromCanonical(constant),
        .main_offset = circuit_main,
        .interaction_offset = circuit_interaction,
        .elements = .init(QM31.zero(), QM31.zero()),
        .claimed_sum = QM31.zero(),
    };
    const chip_main_end: u32 = circuit_main + @as(u32, @intCast(chip.main_width));
    const chip_interaction_end: u32 = circuit_interaction + @as(u32, @intCast(chip.interaction_width));
    components[1] = .{
        .name = "repeated_step_chip",
        .source_index = 0,
        .proof_index = 1,
        .trace_log_size = chip_log,
        .evaluation_log_size = chip_air.maxConstraintLogDegreeBound(),
        .base_trace_columns = chip.main_width,
        .interaction_trace_columns = chip.interaction_width,
        .n_constraints = @intCast(chip_air.nConstraints()),
        .random_coefficient_offset = components[0].n_constraints,
        .trace_spans = try allocator.dupe(TraceSpan, &.{
            .{ .tree = 1, .start = circuit_main, .end = chip_main_end },
            .{ .tree = 2, .start = circuit_interaction, .end = chip_interaction_end },
        }),
        .preprocessed_indices = &.{},
        .program_binding_sha256 = try nativeBinding(allocator, "S31-CHIP-AIR-V1\x00", @embedFile("s31_chip_air_source"), &.{ rounds, constant, chip.relation_id }),
        .claimed_sum_index = 1,
        .main_trace_span = .{ .tree = 1, .start = circuit_main, .end = chip_main_end },
        .interaction_trace_span = .{ .tree = 2, .start = circuit_interaction, .end = chip_interaction_end },
        .max_constraint_log_degree_bound = chip_air.maxConstraintLogDegreeBound(),
        .lookup_relation_ids = try allocator.dupe(u32, &.{chip.relation_id}),
    };
    if (boundary) |addresses| {
        const main_start = chip_main_end;
        const interaction_start = chip_interaction_end;
        const bridge_air: bridge.Component = .{
            .main_offset = main_start,
            .interaction_offset = interaction_start,
            .boundary = addresses,
            .rounds = rounds,
            .elements = .init(QM31.zero(), QM31.zero()),
            .claimed_sum = QM31.zero(),
        };
        const bridge_main_end: u32 = main_start + @as(u32, @intCast(bridge.main_width));
        const bridge_interaction_end: u32 = interaction_start + @as(u32, @intCast(bridge.interaction_width));
        components[2] = .{
            .name = "private_boundary_bridge",
            .source_index = 0,
            .proof_index = 2,
            .trace_log_size = bridge.log_size,
            .evaluation_log_size = bridge_air.maxConstraintLogDegreeBound(),
            .base_trace_columns = bridge.main_width,
            .interaction_trace_columns = bridge.interaction_width,
            .n_constraints = @intCast(bridge_air.nConstraints()),
            .random_coefficient_offset = components[0].n_constraints + components[1].n_constraints,
            .trace_spans = try allocator.dupe(TraceSpan, &.{
                .{ .tree = 1, .start = main_start, .end = bridge_main_end },
                .{ .tree = 2, .start = interaction_start, .end = bridge_interaction_end },
            }),
            .preprocessed_indices = &.{},
            .program_binding_sha256 = try bridgeBinding(allocator, rounds, addresses),
            .claimed_sum_index = 2,
            .main_trace_span = .{ .tree = 1, .start = main_start, .end = bridge_main_end },
            .interaction_trace_span = .{ .tree = 2, .start = interaction_start, .end = bridge_interaction_end },
            .max_constraint_log_degree_bound = bridge_air.maxConstraintLogDegreeBound(),
            .lookup_relation_ids = try allocator.dupe(u32, &.{ circuit.common.component_list.GATE_RELATION_ID, chip.relation_id }),
        };
    }
    generated.value.schema = "s31-component-manifest-direct-chip-v1";
    generated.value.profile = if (boundary != null) "direct-m31-private-v5" else "direct-m31-v4";
    generated.value.claimed_sums = @intCast(count);
    generated.value.components = components;
    generated.value.chip_call = .{
        .call_id = 0,
        .relation_id = chip.relation_id,
        .rounds = rounds,
        .constant = constant,
        .private_boundary = boundary,
    };
    return generated;
}

fn nativeBinding(allocator: std.mem.Allocator, domain: []const u8, source: []const u8, parameters: []const u32) ![]const u8 {
    var hash = Sha256.init(.{});
    hash.update(domain);
    hash.update(source);
    var word: [4]u8 = undefined;
    for (parameters) |parameter| {
        std.mem.writeInt(u32, &word, parameter, .little);
        hash.update(&word);
    }
    var digest: [32]u8 = undefined;
    hash.final(&digest);
    return hex(allocator, digest);
}

fn bridgeBinding(allocator: std.mem.Allocator, rounds: u32, addresses: direct.PrivateBoundary) ![]const u8 {
    const parameters = [_]u32{rounds} ++ addresses.input ++ addresses.output;
    return nativeBinding(allocator, "S31-PRIVATE-BRIDGE-AIR-V1\x00", @embedFile("s31_bridge_air_source"), &parameters);
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
