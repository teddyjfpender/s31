//! Witness-free inspection of the verifier components in the direct M31 profile.
//!
//! The one-call manifest has a fixed wire format. This module checks that its
//! claimed geometry still agrees with the actual AIR handles selected by the
//! native verifier. It consumes no proof bytes and changes no transcript.
const std = @import("std");
const core = @import("stwo_core");
const cairo = @import("stwo_cairo_frontend");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const manifest = @import("component_manifest.zig");

const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;
const chip = cpu.repeated_step_chip;
const bridge = cpu.private_boundary_bridge;
const direct_trace = circuit.witness.direct_arithmetic;
const n_fixed = circuit.common.direct_arithmetic.N_COLUMNS;

pub const ChipSpec = struct { rounds: u32, constant: M31 };

/// One in-place owner for the verifier's exact AIR handles. The handles contain
/// pointers into this struct, so callers must not copy or return it by value.
/// The predecode geometry walk and the final STARK verifier use the same owner.
pub const DirectHandles = struct {
    bound: cpu.air.Bundle,
    captured: cairo.proving.air.component.Component,
    chip_component: chip.Component = undefined,
    bridge_component: bridge.Component = undefined,
    handles: [3]core.air.components.Component = undefined,
    preprocessed_logs: [n_fixed]u32,
    chip_log: ?u32,
    has_boundary: bool,
    count: usize,

    pub fn init(
        self: *DirectHandles,
        allocator: std.mem.Allocator,
        layout: *const circuit.common.direct_arithmetic.Layout,
        template: *const cpu.air.Bundle,
        pcs: core.pcs.config_v2.PcsConfigV2,
        chip_spec: ?ChipSpec,
        boundary: ?bridge.Boundary,
    ) !void {
        if (boundary != null and chip_spec == null) return error.InvalidDirectHandleRoster;
        if (boundary) |addresses| try addresses.validate(core.fields.m31.Modulus);
        const circuit_log = layout.traceLogSize();
        const chip_log: ?u32 = if (chip_spec) |spec| try chip.validateRounds(spec.rounds) else null;
        self.bound = try cpu.air.bindDirectArithmetic(allocator, template, circuit_log, layout);
        errdefer self.bound.deinit();
        if (self.bound.components.len != 1) return error.InvalidDirectHandleRoster;
        self.preprocessed_logs = [_]u32{circuit_log} ** n_fixed;
        const lifted_log = std.math.sub(u32, pcs.trace_lifting_log_size, pcs.fri_config.log_blowup_factor) catch
            return error.InvalidDirectHandlePcs;
        const lifting_bound = try std.math.add(u32, lifted_log, 1);
        self.captured = cairo.proving.air.component.Component.init(
            allocator,
            &self.bound.components[0],
            &self.preprocessed_logs,
            lifting_bound,
            QM31.one(),
            QM31.one(),
            QM31.zero(),
        );
        self.handles[0] = self.captured.asVerifierComponent();
        self.chip_log = chip_log;
        self.has_boundary = boundary != null;
        self.count = 1;
        if (chip_spec) |spec| {
            self.chip_component = .{
                .log_size = chip_log.?,
                .constant = spec.constant,
                .main_offset = direct_trace.main_width,
                .interaction_offset = direct_trace.interaction_width,
                .elements = .init(QM31.one(), QM31.one()),
                .claimed_sum = QM31.zero(),
            };
            self.handles[1] = self.chip_component.asVerifierComponent();
            self.count = 2;
        }
        if (boundary) |addresses| {
            self.bridge_component = .{
                .main_offset = direct_trace.main_width + chip.main_width,
                .interaction_offset = direct_trace.interaction_width + chip.interaction_width,
                .boundary = addresses,
                .rounds = chip_spec.?.rounds,
                .elements = .init(QM31.one(), QM31.one()),
                .claimed_sum = QM31.zero(),
            };
            self.handles[2] = self.bridge_component.asVerifierComponent();
            self.count = 3;
        }
    }

    pub fn deinit(self: *DirectHandles) void {
        self.bound.deinit();
        self.* = undefined;
    }

    pub fn components(self: *const DirectHandles) core.air.components.Components {
        return .{ .components = self.handles[0..self.count], .n_preprocessed_columns = n_fixed };
    }

    pub fn slice(self: *const DirectHandles) []const core.air.components.Component {
        return self.handles[0..self.count];
    }

    /// Transcript challenges and claims do not affect geometry, but they must
    /// be installed on the very handles that were inspected before decoding.
    pub fn setClaims(self: *DirectHandles, z: QM31, alpha: QM31, sums: []const QM31) !void {
        if (sums.len != self.count) return error.InvalidDirectHandleRoster;
        self.captured.runtime.lookup_z = z;
        self.captured.runtime.lookup_alpha = alpha;
        self.captured.runtime.claimed_sum = sums[0];
        if (self.chip_log != null) {
            self.chip_component.elements = .init(z, alpha);
            self.chip_component.claimed_sum = sums[1];
        }
        if (self.has_boundary) {
            self.bridge_component.elements = .init(z, alpha);
            self.bridge_component.claimed_sum = sums[2];
        }
    }
};

pub const Fact = struct {
    trace_log_size: u32,
    evaluation_log_size: u32,
    main_start: u32,
    main_width: u32,
    interaction_start: u32,
    interaction_width: u32,
    constraint_offset: u32,
    n_constraints: u32,
    preprocessed_indices: [n_fixed]u32 = [_]u32{0} ** n_fixed,
    preprocessed_count: usize = 0,
    relation_ids: [2]u32 = .{ 0, 0 },
    relation_count: usize = 0,

    pub fn preprocessedSlice(self: *const Fact) []const u32 {
        return self.preprocessed_indices[0..self.preprocessed_count];
    }

    pub fn relationSlice(self: *const Fact) []const u32 {
        return self.relation_ids[0..self.relation_count];
    }
};

pub const Inspection = struct {
    facts: [3]Fact = undefined,
    count: usize,
    tree_columns: [4]u32,
    sample_width_limits: [4]u32,
    max_column_log_size: u32,
    composition_log_size: u32,
    composition_split: u32,

    pub fn factSlice(self: *const Inspection) []const Fact {
        return self.facts[0..self.count];
    }
};

/// Inspect the exact circuit, chip and optional bridge verifier component
/// types. Dummy lookup challenges are enough: handle geometry is independent
/// of Fiat-Shamir draws and claimed sums.
pub fn inspect(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.direct_arithmetic.Layout,
    template: *const cpu.air.Bundle,
    pcs: core.pcs.config_v2.PcsConfigV2,
    chip_spec: ?ChipSpec,
    boundary: ?bridge.Boundary,
) !Inspection {
    var owned: DirectHandles = undefined;
    try owned.init(allocator, layout, template, pcs, chip_spec, boundary);
    defer owned.deinit();
    return inspectHandles(allocator, layout, pcs, &owned);
}

pub fn inspectHandles(
    allocator: std.mem.Allocator,
    layout: *const circuit.common.direct_arithmetic.Layout,
    pcs: core.pcs.config_v2.PcsConfigV2,
    owned: *const DirectHandles,
) !Inspection {
    const circuit_log = layout.traceLogSize();
    const chip_log = owned.chip_log;
    const count = owned.count;
    const handles = owned.slice();
    var result: Inspection = .{
        .count = count,
        .tree_columns = @splat(0),
        .sample_width_limits = @splat(0),
        .max_column_log_size = 0,
        .composition_log_size = 0,
        .composition_split = 0,
    };
    var main_at: u32 = 0;
    var interaction_at: u32 = 0;
    var constraint_at: u32 = 0;
    for (handles[0..count], result.facts[0..count], 0..) |handle, *fact, index| {
        if (handle.compositionLogSplit() != core.verifier_types.COMPOSITION_LOG_SPLIT)
            return error.InvalidDirectHandleComposition;
        const main_width: u32 = @intCast(switch (index) {
            0 => direct_trace.main_width,
            1 => chip.main_width,
            2 => bridge.main_width,
            else => unreachable,
        });
        const interaction_width: u32 = @intCast(switch (index) {
            0 => direct_trace.interaction_width,
            1 => chip.interaction_width,
            2 => bridge.interaction_width,
            else => unreachable,
        });
        const trace_log: u32 = switch (index) {
            0 => circuit_log,
            1 => chip_log.?,
            2 => bridge.log_size,
            else => unreachable,
        };
        fact.* = .{
            .trace_log_size = trace_log,
            .evaluation_log_size = handle.maxConstraintLogDegreeBound(),
            .main_start = main_at,
            .main_width = main_width,
            .interaction_start = interaction_at,
            .interaction_width = interaction_width,
            .constraint_offset = constraint_at,
            .n_constraints = std.math.cast(u32, handle.nConstraints()) orelse return error.InvalidDirectHandleRoster,
        };
        const indices = try handle.preprocessedColumnIndices(allocator);
        defer allocator.free(indices);
        if (indices.len > n_fixed or (index != 0 and indices.len != 0))
            return error.InvalidDirectHandleRoster;
        fact.preprocessed_count = indices.len;
        for (indices, 0..) |fixed, offset| {
            if (fixed >= n_fixed) return error.InvalidDirectHandleRoster;
            fact.preprocessed_indices[offset] = @intCast(fixed);
        }
        switch (index) {
            0 => {
                fact.relation_ids[0] = circuit.common.component_list.GATE_RELATION_ID;
                fact.relation_count = 1;
            },
            1 => {
                fact.relation_ids[0] = chip.relation_id;
                fact.relation_count = 1;
            },
            2 => {
                fact.relation_ids = .{ circuit.common.component_list.GATE_RELATION_ID, chip.relation_id };
                fact.relation_count = 2;
            },
            else => unreachable,
        }
        main_at = try std.math.add(u32, main_at, main_width);
        interaction_at = try std.math.add(u32, interaction_at, interaction_width);
        constraint_at = try std.math.add(u32, constraint_at, fact.n_constraints);
    }
    const selected = owned.components();
    const split = try selected.compositionLogSplit();
    const composition_log = core.verifier_types.compositionMaskLogSize(selected.compositionLogDegreeBound(), split) orelse
        return error.InvalidDirectHandleComposition;
    const composition_columns = core.verifier_types.compositionColumnCount(split, core.fields.qm31.SECURE_EXTENSION_DEGREE) orelse
        return error.InvalidDirectHandleComposition;
    var logs = try selected.columnLogSizes(allocator);
    defer logs.deinitDeep(allocator);
    const point = core.circle.secureFieldPointFromRandomSeed(QM31.one());
    var masks = try selected.maskPoints(allocator, point, composition_log, true);
    defer masks.deinitDeep(allocator);
    if (logs.items.len != 3 or masks.items.len != 3) return error.InvalidDirectHandleTree;
    const widths = [_]u32{ n_fixed, main_at, interaction_at };
    for (logs.items, masks.items, widths, 0..) |tree_logs, tree_masks, width, tree| {
        if (tree_logs.len != @as(usize, width) or tree_masks.len != @as(usize, width))
            return error.InvalidDirectHandleTree;
        result.tree_columns[tree] = width;
        for (tree_logs, tree_masks, 0..) |log, mask, column| {
            const wanted = if (tree == 0) circuit_log else blk: {
                for (result.factSlice()) |fact| {
                    const start = if (tree == 1) fact.main_start else fact.interaction_start;
                    const span = if (tree == 1) fact.main_width else fact.interaction_width;
                    if (column >= @as(usize, start) and column < @as(usize, start + span))
                        break :blk fact.trace_log_size;
                }
                return error.InvalidDirectHandleTree;
            };
            if (log != wanted or mask.len == 0 or mask.len > 2) return error.InvalidDirectHandleTree;
            result.max_column_log_size = @max(result.max_column_log_size, log);
            result.sample_width_limits[tree] = @max(result.sample_width_limits[tree], @as(u32, @intCast(mask.len)));
        }
    }
    result.tree_columns[3] = @intCast(composition_columns);
    result.sample_width_limits[3] = 1;
    result.max_column_log_size = @max(result.max_column_log_size, composition_log);
    result.composition_log_size = composition_log;
    result.composition_split = split;
    const blowup = pcs.fri_config.log_blowup_factor;
    const max_trace_log = @max(circuit_log, chip_log orelse 0);
    if (pcs.trace_lifting_log_size != try std.math.add(u32, max_trace_log, blowup) or
        pcs.preprocessed_lifting_log_size != try std.math.add(u32, circuit_log, blowup))
        return error.InvalidDirectHandlePcs;
    return result;
}

/// Compare all fields present in the existing direct-chip v2 manifest with
/// the live verifier roster. No candidate-provided hash grants authority.
pub fn requireManifest(value: manifest.Manifest, live: *const Inspection) !void {
    try manifest.validateDirectSourceRoster(value);
    if (!std.mem.eql(u8, value.schema, "s31-component-manifest-direct-chip-v2") or
        value.components.len != live.count or value.claimed_sums != @as(u32, @intCast(live.count)))
        return error.DirectManifestHandleMismatch;
    for (value.components, live.factSlice(), 0..) |entry, fact, index| {
        const main = manifest.TraceSpan{ .tree = 1, .start = fact.main_start, .end = try std.math.add(u32, fact.main_start, fact.main_width) };
        const interaction = manifest.TraceSpan{ .tree = 2, .start = fact.interaction_start, .end = try std.math.add(u32, fact.interaction_start, fact.interaction_width) };
        const relation_ids = entry.lookup_relation_ids orelse return error.DirectManifestHandleMismatch;
        if (entry.proof_index != @as(u32, @intCast(index)) or entry.claimed_sum_index == null or
            entry.claimed_sum_index.? != @as(u32, @intCast(index)) or
            entry.trace_log_size != fact.trace_log_size or entry.evaluation_log_size != fact.evaluation_log_size or
            entry.base_trace_columns != @as(usize, fact.main_width) or
            entry.interaction_trace_columns != @as(usize, fact.interaction_width) or
            entry.n_constraints != fact.n_constraints or entry.random_coefficient_offset != fact.constraint_offset or
            entry.max_constraint_log_degree_bound == null or entry.max_constraint_log_degree_bound.? != fact.evaluation_log_size or
            entry.main_trace_span == null or !std.meta.eql(entry.main_trace_span.?, main) or
            entry.interaction_trace_span == null or !std.meta.eql(entry.interaction_trace_span.?, interaction) or
            !std.mem.eql(u32, entry.preprocessed_indices, fact.preprocessedSlice()) or
            !std.mem.eql(u32, relation_ids, fact.relationSlice()) or
            (index != 0 and (entry.trace_spans.len != 2 or
                !std.meta.eql(entry.trace_spans[0], main) or !std.meta.eql(entry.trace_spans[1], interaction))))
            return error.DirectManifestHandleMismatch;
    }
}

test "direct-chip live roster rejects a changed manifest and injected handle drift" {
    const a = std.testing.allocator;
    var gates: [32]circuit.builder.circuit.BinaryGate = undefined;
    for (&gates, 0..) |*gate, id| gate.* = .{ .in0 = 0, .in1 = 1, .out = @intCast(3 + id) };
    const source = circuit.common.preprocessed.CircuitView{ .n_vars = 36, .add = &gates, .output = &.{35} };
    var pp = try circuit.common.direct_arithmetic.Circuit.fromCircuit(a, source);
    defer pp.deinit(a);
    const air_bytes = @embedFile("s31_air_programs");
    var template = try cpu.air.parse(a, air_bytes);
    defer template.deinit();
    const pcs = blk: {
        const fri = try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
        var value = core.pcs.config_v2.PcsConfigV2.fromFriAndTraceSize(fri, pp.traceLogSize());
        value.preprocessed_lifting_log_size = pp.traceLogSize() + fri.log_blowup_factor;
        break :blk value;
    };
    const spec: ChipSpec = .{ .rounds = 16, .constant = M31.fromCanonical(7) };
    const layout = pp.layout();
    const live = try inspect(a, &layout, &template, pcs, spec, null);
    try std.testing.expectEqual(@as(usize, 2), live.count);
    try std.testing.expectEqual(@as(u32, 21), live.tree_columns[1]);
    try std.testing.expectEqual(@as(u32, 16), live.tree_columns[2]);
    var owned: DirectHandles = undefined;
    try owned.init(a, &layout, &template, pcs, spec, null);
    defer owned.deinit();
    const before_claims = try inspectHandles(a, &layout, pcs, &owned);
    var logs = try owned.components().columnLogSizes(a);
    defer logs.deinitDeep(a);
    try std.testing.expectEqual(@as(usize, 3), logs.items.len);
    try std.testing.expectEqual(@as(usize, before_claims.tree_columns[0]), logs.items[0].len);
    try std.testing.expectEqual(@as(usize, before_claims.tree_columns[1]), logs.items[1].len);
    try std.testing.expectEqual(@as(usize, before_claims.tree_columns[2]), logs.items[2].len);
    for (logs.items[0]) |size| try std.testing.expectEqual(layout.traceLogSize(), size);
    for (logs.items[1][0..direct_trace.main_width]) |size| try std.testing.expectEqual(layout.traceLogSize(), size);
    for (logs.items[1][direct_trace.main_width..]) |size| try std.testing.expectEqual(owned.chip_log.?, size);
    for (logs.items[2][0..direct_trace.interaction_width]) |size| try std.testing.expectEqual(layout.traceLogSize(), size);
    for (logs.items[2][direct_trace.interaction_width..]) |size| try std.testing.expectEqual(owned.chip_log.?, size);
    try std.testing.expectError(error.InvalidDirectHandleRoster, owned.setClaims(QM31.one(), QM31.one(), &.{QM31.zero()}));
    try owned.setClaims(QM31.fromU32Unchecked(3, 4, 5, 6), QM31.fromU32Unchecked(7, 8, 9, 10), &.{ QM31.one(), QM31.zero() });
    const after_claims = try inspectHandles(a, &layout, pcs, &owned);
    try std.testing.expectEqual(before_claims.tree_columns, after_claims.tree_columns);
    try std.testing.expectEqual(before_claims.sample_width_limits, after_claims.sample_width_limits);
    for (before_claims.factSlice(), after_claims.factSlice()) |before, after|
        try std.testing.expectEqualDeep(before, after);
    var bad_pcs = pcs;
    bad_pcs.preprocessed_lifting_log_size += 1;
    try std.testing.expectError(error.InvalidDirectHandlePcs, inspect(a, &layout, &template, bad_pcs, spec, null));
    var generated = try manifest.directChip(a, &pp, air_bytes, [_]u8{0} ** 32, [_]u8{0} ** 32, [_]u8{0} ** 32, [_]u8{0} ** 32, spec.rounds, spec.constant.toU32(), null);
    defer generated.deinit();
    try requireManifest(generated.value, &live);
    var altered = live;
    altered.facts[1].n_constraints += 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));
    altered = live;
    altered.facts[1].evaluation_log_size += 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));
    altered = live;
    altered.facts[1].relation_ids[0] ^= 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));
    altered = live;
    altered.facts[1].main_width += 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));
    altered = live;
    altered.facts[1].constraint_offset += 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));
    altered = live;
    altered.facts[0].preprocessed_indices[0] ^= 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(generated.value, &altered));

    const addresses: bridge.Boundary = .{ .input = .{ 3, 4, 5, 6 }, .output = .{ 7, 8, 9, 10 } };
    var private_pp = try circuit.common.direct_arithmetic.Circuit.fromCircuitWithPrivateBoundary(a, source, addresses);
    defer private_pp.deinit(a);
    const private_layout = private_pp.layout();
    const private_live = try inspect(a, &private_layout, &template, pcs, spec, addresses);
    try std.testing.expectEqual(@as(usize, 3), private_live.count);
    try std.testing.expectEqual(@as(u32, 29), private_live.tree_columns[1]);
    try std.testing.expectEqual(@as(u32, 36), private_live.tree_columns[2]);
    var private_generated = try manifest.directChip(a, &private_pp, air_bytes, [_]u8{0} ** 32, [_]u8{0} ** 32, [_]u8{0} ** 32, [_]u8{0} ** 32, spec.rounds, spec.constant.toU32(), addresses);
    defer private_generated.deinit();
    try requireManifest(private_generated.value, &private_live);
    altered = private_live;
    altered.facts[2].relation_ids[1] ^= 1;
    try std.testing.expectError(error.DirectManifestHandleMismatch, requireManifest(private_generated.value, &altered));
}
