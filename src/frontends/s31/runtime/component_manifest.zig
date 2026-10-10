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
const pair = cpu.private_pair_boundary;
const pair_chip = cpu.tagged_pair_chip;
const pair_bridge = cpu.tagged_pair_bridge;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

pub const TraceSpan = struct { tree: u32, start: u32, end: u32 };

pub const Component = struct {
    name: []const u8,
    /// Direct profiles use 1 for the bundle's `qm31_ops` component and 0 as
    /// a native-component sentinel. The sentinel collides with a possible
    /// zero-based bundle index in other profiles, so this field is meaningful
    /// only together with this profile's component name and program binding.
    /// A future general scheduler needs an explicit source-kind variant.
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
    /// In the sealed v1/v2 format, 1 means the bundled circuit AIR and 0 is
    /// a native-AIR sentinel. Resolve the source with `componentSource`;
    /// this integer alone is not a unique program identifier.
    claimed_sum_index: ?u32 = null,
    main_trace_span: ?TraceSpan = null,
    interaction_trace_span: ?TraceSpan = null,
    max_constraint_log_degree_bound: ?u32 = null,
    lookup_relation_ids: ?[]const u32 = null,
};

/// Internal, typed interpretation of the legacy source_index field. Keep it
/// outside the sealed v1/v2 JSON and its transcript digest. A general
/// component scheduler needs a versioned manifest with this source kind and
/// a stable native program identity serialized explicitly.
pub const ComponentSource = union(enum) {
    bundled_air: u32,
    native_air: NativeAir,
};

pub const NativeAir = enum {
    repeated_step_chip,
    private_boundary_bridge,
    tagged_pair_chip,
    tagged_pair_bridge,
};

/// Fail closed when interpreting a component's source. In particular,
/// source_index 0 is meaningful only with a known native program name and
/// profile; a new native chip cannot silently inherit another chip's slot.
pub fn componentSource(schema: []const u8, c: Component) !ComponentSource {
    if (std.mem.eql(u8, c.name, "qm31_ops")) {
        if (c.source_index != 1) return error.InvalidComponentSource;
        if (std.mem.eql(u8, schema, "s31-component-manifest-direct-gate-v1") or
            std.mem.eql(u8, schema, "s31-component-manifest-direct-chip-v2") or
            std.mem.eql(u8, schema, "s31-component-manifest-direct-pair-v1"))
            return .{ .bundled_air = 1 };
        return error.InvalidComponentSource;
    }
    if (c.source_index != 0) return error.InvalidComponentSource;
    if (std.mem.eql(u8, schema, "s31-component-manifest-direct-chip-v2")) {
        if (std.mem.eql(u8, c.name, "repeated_step_chip")) return .{ .native_air = .repeated_step_chip };
        if (std.mem.eql(u8, c.name, "private_boundary_bridge")) return .{ .native_air = .private_boundary_bridge };
    } else if (std.mem.eql(u8, schema, "s31-component-manifest-direct-pair-v1")) {
        if (std.mem.eql(u8, c.name, "tagged_pair_chip")) return .{ .native_air = .tagged_pair_chip };
        if (std.mem.eql(u8, c.name, "tagged_pair_bridge")) return .{ .native_air = .tagged_pair_bridge };
    }
    return error.InvalidComponentSource;
}

/// The released direct profiles have a fixed ordered roster. Validate the
/// source classes and proof/sum positions independently of the generated
/// fields before serializing or comparing them with a sealed key.
pub fn validateDirectSourceRoster(manifest: Manifest) !void {
    const gate = std.mem.eql(u8, manifest.schema, "s31-component-manifest-direct-gate-v1");
    const chip_profile = std.mem.eql(u8, manifest.schema, "s31-component-manifest-direct-chip-v2");
    if (!gate and !chip_profile) return error.InvalidComponentSource;
    const expected_len: usize = if (gate) 1 else blk: {
        const call = manifest.chip_call orelse return error.InvalidComponentSource;
        if (call.call_id != 0) return error.InvalidComponentSource;
        break :blk if (call.private_boundary != null) 3 else 2;
    };
    if (manifest.components.len != expected_len or manifest.claimed_sums != @as(u32, @intCast(expected_len)) or
        (gate and manifest.chip_call != null)) return error.InvalidComponentSource;
    for (manifest.components, 0..) |c, i| {
        const source = try componentSource(manifest.schema, c);
        if (c.proof_index != @as(u32, @intCast(i)) or
            (chip_profile and (c.claimed_sum_index == null or c.claimed_sum_index.? != @as(u32, @intCast(i)))) or
            (gate and c.claimed_sum_index != null)) return error.InvalidComponentSource;
        const expected: ComponentSource = switch (i) {
            0 => .{ .bundled_air = 1 },
            1 => .{ .native_air = .repeated_step_chip },
            2 => .{ .native_air = .private_boundary_bridge },
            else => unreachable,
        };
        if (!std.meta.eql(source, expected)) return error.InvalidComponentSource;
    }
}

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

/// Separate schema: adding pair fields to Manifest would alter the JSON of
/// sealed one-call keys. Call IDs and endpoints are mandatory in this type.
pub const PairCall = struct {
    call_id: u32,
    relation_id: u32,
    rounds: u32,
    constant: u32,
    input: [4]u32,
    output: [4]u32,
};

pub const PairManifest = struct {
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
    pair_calls: [2]PairCall,
};

pub const PairGenerated = struct {
    arena: std.heap.ArenaAllocator,
    value: PairManifest,

    pub fn deinit(self: *PairGenerated) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// The experimental pair has exactly five proof components and two canonical
/// call tags. This typed interpretation is independent of JSON field order
/// and leaves the sealed V3 byte format unchanged.
pub fn validatePairSourceRoster(value: PairManifest) !void {
    if (!std.mem.eql(u8, value.schema, "s31-component-manifest-direct-pair-v1") or
        value.components.len != 5 or value.claimed_sums != 5)
        return error.InvalidPairComponentManifest;
    for (value.pair_calls, 0..) |call, id| {
        if (call.call_id != @as(u32, @intCast(id)) or call.relation_id != pair.relation_id)
            return error.InvalidPairComponentManifest;
    }
    const expected = [_]ComponentSource{
        .{ .bundled_air = 1 },
        .{ .native_air = .tagged_pair_chip },
        .{ .native_air = .tagged_pair_chip },
        .{ .native_air = .tagged_pair_bridge },
        .{ .native_air = .tagged_pair_bridge },
    };
    for (value.components, expected, 0..) |entry, source, index| {
        const actual = componentSource(value.schema, entry) catch return error.InvalidPairComponentManifest;
        if (!std.meta.eql(actual, source) or
            entry.proof_index != @as(u32, @intCast(index)) or
            entry.claimed_sum_index == null or entry.claimed_sum_index.? != @as(u32, @intCast(index)))
            return error.InvalidPairComponentManifest;
    }
}

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
    try validateDirectSourceRoster(value);
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
    generated.value.schema = "s31-component-manifest-direct-chip-v2";
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
    try validateDirectSourceRoster(generated.value);
    return generated;
}

/// Rebuild the exact five-role native pair roster from the source-derived
/// circuit and Plan. The caller supplies no component offsets or call IDs.
/// The S31 proof path remains disabled until a sealed verifier and byte
/// envelope reconstruct this value independently from source.
pub fn directPair(
    backing: std.mem.Allocator,
    pp: *const direct.Circuit,
    plan: pair.Plan,
    air_bytes: []const u8,
    program_digest: [32]u8,
    ir_digest: [32]u8,
    preprocessed_root: [32]u8,
    circuit_hash: [32]u8,
) !PairGenerated {
    if (pp.private_pair_boundary == null or !std.meta.eql(pp.private_pair_boundary.?, plan.boundary()))
        return error.InvalidPairComponentManifest;
    for (plan.calls, 0..) |call, id|
        if (call.call_id != id) return error.NonCanonicalPairCallId;
    var generated = try directGate(backing, pp, air_bytes, program_digest, ir_digest, preprocessed_root, circuit_hash);
    errdefer generated.deinit();
    const a = generated.arena.allocator();
    const circuit_component = generated.value.components[0];
    const specs = try pair.expectedSpecs(plan, pp.traceLogSize(), @intCast(circuit_component.n_constraints));
    const components = try a.alloc(Component, pair.roster.len);
    components[0] = circuit_component;
    components[0].claimed_sum_index = 0;
    components[0].main_trace_span = .{ .tree = 1, .start = 0, .end = @intCast(pair.circuit_main_width) };
    components[0].interaction_trace_span = .{ .tree = 2, .start = 0, .end = @intCast(pair.circuit_interaction_width) };
    components[0].max_constraint_log_degree_bound = components[0].evaluation_log_size;
    components[0].lookup_relation_ids = try a.dupe(u32, &.{circuit.common.component_list.GATE_RELATION_ID});
    for (plan.calls, 0..) |call, id| {
        const chip_spec = specs[1 + id];
        const chip_air: pair_chip.Component = .{
            .log_size = chip_spec.log_size,
            .call_id = call.call_id,
            .constant = call.constant,
            .main_offset = chip_spec.main_offset,
            .interaction_offset = chip_spec.interaction_offset,
            .elements = .init(QM31.zero(), QM31.zero()),
            .claimed_sum = QM31.zero(),
        };
        if (chip_air.nConstraints() != chip_spec.constraint_count or
            chip_air.maxConstraintLogDegreeBound() != chip_spec.log_size + 1)
            return error.InvalidPairComponentManifest;
        components[1 + id] = try pairComponent(a, chip_spec, "tagged_pair_chip", chip_air.maxConstraintLogDegreeBound(), try pairNativeBinding(a, "S31-TAGGED-PAIR-CHIP-AIR-V1\x00", &.{ call.call_id, call.rounds, call.constant.toU32(), pair.relation_id }), &.{pair.relation_id});

        const bridge_spec = specs[3 + id];
        const bridge_air: pair_bridge.Component = .{
            .main_offset = bridge_spec.main_offset,
            .interaction_offset = bridge_spec.interaction_offset,
            .boundary = call,
            .elements = .init(QM31.zero(), QM31.zero()),
            .claimed_sum = QM31.zero(),
        };
        if (bridge_air.nConstraints() != bridge_spec.constraint_count or
            bridge_air.maxConstraintLogDegreeBound() != bridge_spec.log_size + 2)
            return error.InvalidPairComponentManifest;
        const params = [_]u32{ call.call_id, call.rounds, call.constant.toU32(), pair.relation_id } ++ call.input ++ call.output;
        components[3 + id] = try pairComponent(a, bridge_spec, "tagged_pair_bridge", bridge_air.maxConstraintLogDegreeBound(), try pairNativeBinding(a, "S31-TAGGED-PAIR-BRIDGE-AIR-V1\x00", &params), &.{ circuit.common.component_list.GATE_RELATION_ID, pair.relation_id });
    }
    var calls: [2]PairCall = undefined;
    for (plan.calls, &calls) |call, *entry| entry.* = .{
        .call_id = call.call_id,
        .relation_id = pair.relation_id,
        .rounds = call.rounds,
        .constant = call.constant.toU32(),
        .input = call.input,
        .output = call.output,
    };
    const value: PairManifest = .{
        .schema = "s31-component-manifest-direct-pair-v1",
        .profile = "direct-m31-private-pair-v1",
        .program_sha256 = generated.value.program_sha256,
        .canonical_ir_sha256 = generated.value.canonical_ir_sha256,
        .air_bundle_sha256 = generated.value.air_bundle_sha256,
        .preprocessed_root = generated.value.preprocessed_root,
        .circuit_hash = generated.value.circuit_hash,
        .composition_plan_hash = generated.value.composition_plan_hash,
        .claimed_sums = @intCast(pair.roster.len),
        .components = components,
        .preprocessed_columns = generated.value.preprocessed_columns,
        .pair_calls = calls,
    };
    try validatePairSourceRoster(value);
    return .{ .arena = generated.arena, .value = value };
}

fn pairComponent(a: std.mem.Allocator, spec: pair.ComponentSpec, name: []const u8, max_degree: u32, binding: []const u8, relation_ids: []const u32) !Component {
    const main_span = TraceSpan{ .tree = 1, .start = @intCast(spec.main_offset), .end = @intCast(spec.main_offset + spec.main_columns) };
    const interaction_span = TraceSpan{ .tree = 2, .start = @intCast(spec.interaction_offset), .end = @intCast(spec.interaction_offset + spec.interaction_columns) };
    return .{
        .name = name,
        .source_index = 0,
        .proof_index = @intFromEnum(spec.role),
        .trace_log_size = spec.log_size,
        .evaluation_log_size = max_degree,
        .base_trace_columns = spec.main_columns,
        .interaction_trace_columns = spec.interaction_columns,
        .n_constraints = @intCast(spec.constraint_count),
        .random_coefficient_offset = @intCast(spec.constraint_offset),
        .trace_spans = try a.dupe(TraceSpan, &.{ main_span, interaction_span }),
        .preprocessed_indices = &.{},
        .program_binding_sha256 = binding,
        .claimed_sum_index = @intFromEnum(spec.role),
        .main_trace_span = main_span,
        .interaction_trace_span = interaction_span,
        .max_constraint_log_degree_bound = max_degree,
        .lookup_relation_ids = try a.dupe(u32, relation_ids),
    };
}

fn pairNativeBinding(a: std.mem.Allocator, domain: []const u8, parameters: []const u32) ![]const u8 {
    var h = Sha256.init(.{});
    h.update(domain);
    // Both native components and the joint proof schedule depend on these
    // modules for tuple arity, row placement, transitions, interactions and
    // transcript order. Bind the pinned source set in the V3 manifest.
    inline for (.{
        @embedFile("s31_pair_boundary_source"),
        @embedFile("s31_chip_air_source"),
        @embedFile("s31_tagged_pair_chip_air_source"),
        @embedFile("s31_tagged_pair_bridge_air_source"),
        @embedFile("s31_pair_proof_source"),
    }) |source| hashBytes(&h, source);
    for (parameters) |parameter| hashInt(&h, parameter);
    var digest: [32]u8 = undefined;
    h.final(&digest);
    return hex(a, digest);
}

/// Typed V3 commitment. It includes every generated field except the circuit
/// hash (which depends on it) and separates this profile from one-call V2.
pub fn pairPrecommitmentDigest(manifest: PairManifest) [32]u8 {
    var h = Sha256.init(.{});
    h.update("S31-COMPONENT-MANIFEST-PRECOMMIT-V3\x00");
    hashManifestCore(&h, manifest);
    hashInt(&h, @as(u64, manifest.pair_calls.len));
    for (manifest.pair_calls) |call| {
        hashInt(&h, call.call_id);
        hashInt(&h, call.relation_id);
        hashInt(&h, call.rounds);
        hashInt(&h, call.constant);
        for (call.input) |address| hashInt(&h, address);
        for (call.output) |address| hashInt(&h, address);
    }
    var digest: [32]u8 = undefined;
    h.final(&digest);
    return digest;
}

fn hashManifestCore(h: *Sha256, manifest: PairManifest) void {
    hashBytes(h, manifest.schema);
    hashBytes(h, manifest.profile);
    hashBytes(h, manifest.program_sha256);
    hashBytes(h, manifest.canonical_ir_sha256);
    hashBytes(h, manifest.air_bundle_sha256);
    hashBytes(h, manifest.preprocessed_root);
    // circuit_hash is excluded because it depends on the precommitment.
    hashInt(h, manifest.composition_plan_hash);
    hashInt(h, manifest.claimed_sums);
    hashInt(h, @as(u64, @intCast(manifest.components.len)));
    for (manifest.components) |c| {
        hashBytes(h, c.name);
        hashInt(h, c.source_index);
        hashInt(h, c.proof_index);
        hashInt(h, c.trace_log_size);
        hashInt(h, c.evaluation_log_size);
        hashInt(h, @as(u64, @intCast(c.base_trace_columns)));
        hashInt(h, @as(u64, @intCast(c.interaction_trace_columns)));
        hashInt(h, c.n_constraints);
        hashInt(h, c.random_coefficient_offset);
        hashInt(h, @as(u64, @intCast(c.trace_spans.len)));
        for (c.trace_spans) |span| hashSpan(h, span);
        hashInt(h, @as(u64, @intCast(c.preprocessed_indices.len)));
        for (c.preprocessed_indices) |index| hashInt(h, index);
        hashBytes(h, c.program_binding_sha256);
        hashOptionalInt(h, c.claimed_sum_index);
        hashOptionalSpan(h, c.main_trace_span);
        hashOptionalSpan(h, c.interaction_trace_span);
        hashOptionalInt(h, c.max_constraint_log_degree_bound);
        if (c.lookup_relation_ids) |ids| {
            hashInt(h, @as(u8, 1));
            hashInt(h, @as(u64, @intCast(ids.len)));
            for (ids) |id| hashInt(h, id);
        } else hashInt(h, @as(u8, 0));
    }
    hashInt(h, @as(u64, @intCast(manifest.preprocessed_columns.len)));
    for (manifest.preprocessed_columns) |column| {
        hashBytes(h, column.id);
        hashInt(h, @as(u64, @intCast(column.commitment_index)));
        hashInt(h, column.log_size);
        hashInt(h, @as(u64, @intCast(column.rows)));
        hashBytes(h, column.values_sha256);
    }
}

pub fn pairEffectiveSourceDigest(source_digest: [32]u8, manifest: PairManifest) [32]u8 {
    return pair.effectiveDigest(source_digest, pairPrecommitmentDigest(manifest));
}

pub fn setPairCircuitHash(generated: *PairGenerated, circuit_hash: [32]u8) !void {
    generated.value.circuit_hash = try hex(generated.arena.allocator(), circuit_hash);
}

pub fn matchesPair(a: std.mem.Allocator, sealed: PairManifest, generated: PairManifest) !bool {
    validatePairSourceRoster(sealed) catch return false;
    try validatePairSourceRoster(generated);
    const left = try std.json.Stringify.valueAlloc(a, sealed, .{});
    defer a.free(left);
    const right = try std.json.Stringify.valueAlloc(a, generated, .{});
    defer a.free(right);
    return std.mem.eql(u8, left, right);
}

/// The v2 precommitment is a typed, length-delimited serialization of every
/// generated roster field except circuit_hash, which depends on this digest.
/// It contains no witness values. The true source hash remains a separate key
/// field; the returned effective digest is used only by the native engine.
pub fn precommitmentDigest(manifest: Manifest) [32]u8 {
    var h = Sha256.init(.{});
    h.update("S31-COMPONENT-MANIFEST-PRECOMMIT-V2\x00");
    hashBytes(&h, manifest.schema);
    hashBytes(&h, manifest.profile);
    hashBytes(&h, manifest.program_sha256);
    hashBytes(&h, manifest.canonical_ir_sha256);
    hashBytes(&h, manifest.air_bundle_sha256);
    hashBytes(&h, manifest.preprocessed_root);
    // circuit_hash is deliberately excluded to avoid a hash cycle.
    hashInt(&h, manifest.composition_plan_hash);
    hashInt(&h, manifest.claimed_sums);
    hashInt(&h, @as(u64, @intCast(manifest.components.len)));
    for (manifest.components) |c| {
        hashBytes(&h, c.name);
        hashInt(&h, c.source_index);
        hashInt(&h, c.proof_index);
        hashInt(&h, c.trace_log_size);
        hashInt(&h, c.evaluation_log_size);
        hashInt(&h, @as(u64, @intCast(c.base_trace_columns)));
        hashInt(&h, @as(u64, @intCast(c.interaction_trace_columns)));
        hashInt(&h, c.n_constraints);
        hashInt(&h, c.random_coefficient_offset);
        hashInt(&h, @as(u64, @intCast(c.trace_spans.len)));
        for (c.trace_spans) |s| hashSpan(&h, s);
        hashInt(&h, @as(u64, @intCast(c.preprocessed_indices.len)));
        for (c.preprocessed_indices) |i| hashInt(&h, i);
        hashBytes(&h, c.program_binding_sha256);
        hashOptionalInt(&h, c.claimed_sum_index);
        hashOptionalSpan(&h, c.main_trace_span);
        hashOptionalSpan(&h, c.interaction_trace_span);
        hashOptionalInt(&h, c.max_constraint_log_degree_bound);
        if (c.lookup_relation_ids) |ids| {
            hashInt(&h, @as(u8, 1));
            hashInt(&h, @as(u64, @intCast(ids.len)));
            for (ids) |id| hashInt(&h, id);
        } else hashInt(&h, @as(u8, 0));
    }
    hashInt(&h, @as(u64, @intCast(manifest.preprocessed_columns.len)));
    for (manifest.preprocessed_columns) |c| {
        hashBytes(&h, c.id);
        hashInt(&h, @as(u64, @intCast(c.commitment_index)));
        hashInt(&h, c.log_size);
        hashInt(&h, @as(u64, @intCast(c.rows)));
        hashBytes(&h, c.values_sha256);
    }
    if (manifest.chip_call) |call| {
        hashInt(&h, @as(u8, 1));
        hashInt(&h, call.call_id);
        hashInt(&h, call.relation_id);
        hashInt(&h, call.rounds);
        hashInt(&h, call.constant);
        if (call.private_boundary) |b| {
            hashInt(&h, @as(u8, 1));
            for (b.input) |address| hashInt(&h, address);
            for (b.output) |address| hashInt(&h, address);
        } else hashInt(&h, @as(u8, 0));
    } else hashInt(&h, @as(u8, 0));
    var digest: [32]u8 = undefined;
    h.final(&digest);
    return digest;
}

pub fn effectiveSourceDigest(source_digest: [32]u8, manifest: Manifest) [32]u8 {
    var h = Sha256.init(.{});
    h.update("S31-DIRECT-CHIP-MANIFEST-TRANSCRIPT-V2\x00");
    h.update(&source_digest);
    const digest = precommitmentDigest(manifest);
    h.update(&digest);
    var result: [32]u8 = undefined;
    h.final(&result);
    return result;
}

pub fn setCircuitHash(generated: *Generated, circuit_hash: [32]u8) !void {
    generated.value.circuit_hash = try hex(generated.arena.allocator(), circuit_hash);
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

fn hashBytes(h: *Sha256, value: []const u8) void {
    hashInt(h, @as(u64, @intCast(value.len)));
    h.update(value);
}

fn hashSpan(h: *Sha256, span: TraceSpan) void {
    hashInt(h, span.tree);
    hashInt(h, span.start);
    hashInt(h, span.end);
}

fn hashOptionalInt(h: *Sha256, value: ?u32) void {
    if (value) |v| {
        hashInt(h, @as(u8, 1));
        hashInt(h, v);
    } else hashInt(h, @as(u8, 0));
}

fn hashOptionalSpan(h: *Sha256, value: ?TraceSpan) void {
    if (value) |v| {
        hashInt(h, @as(u8, 1));
        hashSpan(h, v);
    } else hashInt(h, @as(u8, 0));
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
    validateDirectSourceRoster(sealed) catch return false;
    try validateDirectSourceRoster(generated);
    const left = try std.json.Stringify.valueAlloc(allocator, sealed, .{});
    defer allocator.free(left);
    const right = try std.json.Stringify.valueAlloc(allocator, generated, .{});
    defer allocator.free(right);
    return std.mem.eql(u8, left, right);
}

test "legacy component source slots have a typed, closed interpretation" {
    var c: Component = .{
        .name = "qm31_ops",
        .source_index = 1,
        .proof_index = 0,
        .trace_log_size = 9,
        .evaluation_log_size = 10,
        .base_trace_columns = 12,
        .interaction_trace_columns = 8,
        .n_constraints = 1,
        .random_coefficient_offset = 0,
        .trace_spans = &.{},
        .preprocessed_indices = &.{},
        .program_binding_sha256 = "binding",
    };
    const gate_schema = "s31-component-manifest-direct-gate-v1";
    const chip_schema = "s31-component-manifest-direct-chip-v2";
    const pair_schema = "s31-component-manifest-direct-pair-v1";
    try std.testing.expect(std.meta.eql(try componentSource(gate_schema, c), ComponentSource{ .bundled_air = 1 }));
    c.source_index = 0;
    try std.testing.expectError(error.InvalidComponentSource, componentSource(gate_schema, c));
    c.name = "repeated_step_chip";
    try std.testing.expect(std.meta.eql(try componentSource(chip_schema, c), ComponentSource{ .native_air = .repeated_step_chip }));
    try std.testing.expectError(error.InvalidComponentSource, componentSource(gate_schema, c));
    c.name = "tagged_pair_bridge";
    try std.testing.expect(std.meta.eql(try componentSource(pair_schema, c), ComponentSource{ .native_air = .tagged_pair_bridge }));
    try std.testing.expectError(error.InvalidComponentSource, componentSource(chip_schema, c));
    c.name = "unregistered_native_air";
    try std.testing.expectError(error.InvalidComponentSource, componentSource(pair_schema, c));
}

fn hex(allocator: std.mem.Allocator, digest: [32]u8) ![]const u8 {
    const encoded = std.fmt.bytesToHex(digest, .lower);
    return allocator.dupe(u8, &encoded);
}
