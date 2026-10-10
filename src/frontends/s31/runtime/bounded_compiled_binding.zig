//! Compiled endpoint inspection for the bounded-call V4 plan.
//!
//! No function in this module parses or accepts proof bytes. `inspectMany`
//! binds every admitted count to source-compiled endpoints and the actual
//! circuit AIR, then checks live V4 component geometry. Its source-derived
//! request and witness helpers serve the experimental in-memory V4 scheduler.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const relation = @import("../language/relation.zig");
const compiler = @import("../language/relation_compiler.zig");
const admission = @import("../language/bounded_call_admission.zig");
const v4 = @import("bounded_component_manifest.zig");
const sealed = @import("component_manifest.zig");
const live_pair = @import("pair_source_binding.zig");
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Sha256 = std.crypto.hash.sha2.Sha256;

pub const EndpointCall = struct {
    call_id: u32,
    source_node_id: u32,
    input_node_id: u32,
    rounds: u32,
    constant: u32,
    input: [4]u32,
    output: [4]u32,
};

const empty_call: EndpointCall = .{
    .call_id = 0,
    .source_node_id = 0,
    .input_node_id = 0,
    .rounds = 0,
    .constant = 0,
    .input = [_]u32{0} ** 4,
    .output = [_]u32{0} ** 4,
};

pub const Topology = struct {
    source_sha256: v4.Digest,
    canonical_ir_sha256: v4.Digest,
    calls: [admission.max_calls]EndpointCall = [_]EndpointCall{empty_call} ** admission.max_calls,
    call_count: usize = 0,
    circuit_variables: u32 = 0,
    circuit_rows: usize = 0,
    fixed_root: v4.Digest = [_]u8{0} ** 32,

    pub fn callSlice(self: *const Topology) []const EndpointCall {
        return self.calls[0..self.call_count];
    }
};

/// Parse and admit the source, then compile every chip endpoint without a
/// witness. The returned addresses belong to the compiled circuit topology.
pub fn compileSourceTopology(allocator: std.mem.Allocator, source_bytes: []const u8) !Topology {
    if (source_bytes.len > admission.max_source_bytes) return error.ManyCallSourceTooLarge;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    return compileProgramTopology(allocator, parsed.value, source_bytes);
}

fn compileProgramTopology(allocator: std.mem.Allocator, program: relation.Program, source_bytes: []const u8) !Topology {
    const plan = try admission.extract(allocator, program);
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(circuit.builder.NoValue, allocator, program, null, &maps);
    defer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit);
    try validateEndpoints(allocator, view, maps.bounded_calls.items);
    var result: Topology = .{
        .source_sha256 = digest(source_bytes),
        .canonical_ir_sha256 = plan.canonical_ir_sha256,
        .call_count = plan.call_count,
        .circuit_variables = @intCast(view.n_vars),
        .circuit_rows = view.nQm31OpsRows(),
    };
    if (maps.bounded_calls.items.len != plan.call_count) return error.BoundedCallCountMismatch;
    for (plan.callSlice(), maps.bounded_calls.items, result.calls[0..plan.call_count]) |source, compiled, *out| {
        if (source.call_id != compiled.call_id or source.source_node_id != compiled.source_node_id or
            source.input_node_id != compiled.input_node_id)
            return error.BoundedCallOrderMismatch;
        out.* = .{
            .call_id = source.call_id,
            .source_node_id = source.source_node_id,
            .input_node_id = source.input_node_id,
            .rounds = source.rounds,
            .constant = source.constant,
            .input = compiled.input,
            .output = compiled.output,
        };
    }
    const native_plan = try manyPlan(result.callSlice());
    var pp = try native_plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    result.fixed_root = try pp.preprocessedRoot(allocator, 1);
    return result;
}

/// Compile a witness with the same lowering mode and reject any change in
/// endpoint addresses or basic circuit shape. For the executable two-call
/// inspection, `inspectTwoCall` also compares the committed fixed root.
pub fn checkWitnessTopology(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    assignment: relation.Assignment,
    expected: Topology,
) !void {
    var witness = try compileManyWitness(allocator, source_bytes, assignment, expected);
    defer witness.deinit();
}

/// Compile a value-carrying circuit only after checking the exact source,
/// canonical calls, compiled endpoint addresses, circuit shape and fixed root
/// against an independently compiled witness-free topology.
pub fn compileManyWitness(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    assignment: relation.Assignment,
    expected: Topology,
) !circuit.builder.Context(QM31) {
    const source_hash = digest(source_bytes);
    if (!std.mem.eql(u8, &source_hash, &expected.source_sha256)) return error.BoundedSourceMismatch;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    const plan = try admission.extract(allocator, parsed.value);
    if (!std.mem.eql(u8, &plan.canonical_ir_sha256, &expected.canonical_ir_sha256) or
        plan.call_count != expected.call_count)
        return error.BoundedSourceMismatch;
    for (plan.callSlice(), expected.callSlice()) |actual, wanted| {
        if (actual.call_id != wanted.call_id or
            actual.source_node_id != wanted.source_node_id or
            actual.input_node_id != wanted.input_node_id or
            actual.rounds != wanted.rounds or actual.constant != wanted.constant)
            return error.BoundedSourceMismatch;
    }
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(QM31, allocator, parsed.value, assignment, &maps);
    errdefer ctx.deinit();
    try padDirect(allocator, QM31, &ctx);
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit);
    try validateEndpoints(allocator, view, maps.bounded_calls.items);
    if (maps.bounded_calls.items.len != expected.call_count or
        view.n_vars != expected.circuit_variables or
        view.nQm31OpsRows() != expected.circuit_rows)
        return error.BoundedWitnessTopologyMismatch;
    for (maps.bounded_calls.items, expected.callSlice()) |actual, wanted| {
        if (actual.call_id != wanted.call_id or actual.source_node_id != wanted.source_node_id or
            actual.input_node_id != wanted.input_node_id or
            !std.meta.eql(actual.input, wanted.input) or !std.meta.eql(actual.output, wanted.output))
            return error.BoundedWitnessTopologyMismatch;
    }
    const native_plan = try manyPlan(expected.callSlice());
    var pp = try native_plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.meta.eql(root, expected.fixed_root)) return error.BoundedWitnessTopologyMismatch;
    return ctx;
}

/// Reconstruct the exact witness-free circuit used by a native verifier.
/// The caller must first derive `expected` from its authenticated source via
/// `inspectMany`; this function also recompiles the source to reject drift.
pub fn compileManyTopology(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    expected: Topology,
) !circuit.builder.Context(circuit.builder.NoValue) {
    const rebuilt = try compileSourceTopology(allocator, source_bytes);
    if (!std.meta.eql(rebuilt, expected)) return error.BoundedTopologyMismatch;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &maps);
    errdefer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit);
    try validateEndpoints(allocator, view, maps.bounded_calls.items);
    if (maps.bounded_calls.items.len != expected.call_count or
        view.n_vars != expected.circuit_variables or
        view.nQm31OpsRows() != expected.circuit_rows)
        return error.BoundedTopologyMismatch;
    for (maps.bounded_calls.items, expected.callSlice()) |actual, wanted| {
        if (actual.call_id != wanted.call_id or actual.source_node_id != wanted.source_node_id or
            actual.input_node_id != wanted.input_node_id or
            !std.meta.eql(actual.input, wanted.input) or !std.meta.eql(actual.output, wanted.output))
            return error.BoundedTopologyMismatch;
    }
    const plan = try manyPlan(expected.callSlice());
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.meta.eql(root, expected.fixed_root)) return error.BoundedTopologyMismatch;
    return ctx;
}

pub const TwoCallInspection = struct {
    topology: Topology,
    generated: v4.Generated,
    preprocessed_root: v4.Digest,

    pub fn deinit(self: *TwoCallInspection) void {
        self.generated.deinit();
        self.* = undefined;
    }
};

pub const ManyInspection = struct {
    topology: Topology,
    generated: v4.Generated,
    selected_schedule: cpu.direct_many_schedule.SelectedSchedule,
    preprocessed_root: v4.Digest,
    manifest_precommitment: v4.Digest,
    effective_source_digest: v4.Digest,
    circuit_identity: v4.Digest,

    pub fn deinit(self: *ManyInspection) void {
        self.generated.deinit();
        self.* = undefined;
    }
};

/// The returned request has no authority by itself. Proof admission must
/// reconstruct `inspection` from authenticated source in the same call.
pub fn nativeManyRequest(inspection: *const ManyInspection) !cpu.experimental_direct_many_arithmetic.Request {
    return .{
        .source_digest = inspection.selected_schedule.geometry.source_digest,
        .manifest_digest = inspection.selected_schedule.manifest_digest,
        .plan = inspection.selected_schedule.fixedCircuitPlan(),
    };
}

/// This is an exact typed projection of the regenerated S31 manifest. The
/// engine treats its dimensions as assertions against live AIR handles, never
/// as instructions for constructing a trace or choosing PCS parameters.
fn candidateManySchedule(
    value: v4.Manifest,
    topology: Topology,
) !cpu.direct_many_schedule.CandidateSchedule {
    if (value.calls.len != topology.call_count or value.components.len != 1 + 2 * topology.call_count or
        value.components.len > cpu.private_many_boundary.max_components or
        !std.meta.eql(value.source_sha256, topology.source_sha256) or
        !std.meta.eql(value.preprocessed_root, topology.fixed_root))
        return error.BoundedManyRosterMismatch;
    const plan = try manyPlan(topology.callSlice());
    var result: cpu.direct_many_schedule.CandidateSchedule = .{
        .source_digest = topology.source_sha256,
        .fixed_root = topology.fixed_root,
        .calls = plan.calls,
        .call_count = plan.count,
        .slots = undefined,
        .slot_count = value.components.len,
        .pcs_profile = .{
            .pow_bits = value.pcs.pow_bits,
            .log_blowup_factor = value.pcs.log_blowup_factor,
            .last_layer_degree_bound = value.pcs.last_layer_degree_bound,
            .queries = value.pcs.queries,
            .fold_step = value.pcs.fold_step,
        },
    };
    for (value.components, result.slots[0..value.components.len]) |component, *slot| {
        if (component.preprocessed_indices.len > circuit.common.direct_arithmetic.N_COLUMNS or
            component.lookup_relation_ids.len > 2 or
            component.main.tree != 1 or component.interaction.tree != 2)
            return error.BoundedManyRosterMismatch;
        const main_width = std.math.sub(u32, component.main.end, component.main.start) catch
            return error.BoundedManyRosterMismatch;
        const interaction_width = std.math.sub(u32, component.interaction.end, component.interaction.start) catch
            return error.BoundedManyRosterMismatch;
        const kind: cpu.private_many_boundary.ComponentKind = switch (component.role) {
            .circuit => .circuit,
            .chip => .chip,
            .bridge => .bridge,
        };
        slot.* = .{
            .kind = kind,
            .source_kind = undefined,
            .call_id = component.call_id,
            .proof_index = component.proof_index,
            .claimed_sum_index = component.claimed_sum_index,
            .trace_log_size = component.trace_log_size,
            .evaluation_log_size = component.evaluation_log_size,
            .main_offset = component.main.start,
            .main_columns = main_width,
            .interaction_offset = component.interaction.start,
            .interaction_columns = interaction_width,
            .constraint_offset = component.random_coefficient_offset,
            .n_constraints = component.n_constraints,
            .preprocessed_count = component.preprocessed_indices.len,
            .relation_count = component.lookup_relation_ids.len,
            .program_binding_sha256 = undefined,
        };
        @memcpy(slot.preprocessed_indices[0..component.preprocessed_indices.len], component.preprocessed_indices);
        @memcpy(slot.relation_ids[0..component.lookup_relation_ids.len], component.lookup_relation_ids);
        switch (component.source) {
            .bundled_air => |source| {
                slot.source_kind = .bundled_circuit;
                slot.bundle_index = source.index;
                slot.bundle_sha256 = source.bundle_sha256;
                slot.program_binding_sha256 = source.selected_program_sha256;
            },
            .native_air => |source| {
                slot.source_kind = switch (source.kind) {
                    .tagged_chip => .tagged_chip,
                    .tagged_bridge => .tagged_bridge,
                };
                slot.program_binding_sha256 = source.program_binding_sha256;
            },
        }
    }
    return result;
}

/// Witness-free V4 source inspection for N=1..8. The official direct circuit
/// AIR is rebound to the exact selected fixed circuit; the tagged chip and
/// bridge slots are checked against the engine's source-owned roster geometry.
/// The experimental in-memory engine uses the live handles and PCS schedule;
/// release proof admission still needs a canonical V4 envelope and a verifier
/// embedding or otherwise authenticating `source_bytes`.
pub fn inspectMany(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
) !ManyInspection {
    const topology = try compileSourceTopology(allocator, source_bytes);
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &maps);
    defer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit);
    try validateEndpoints(allocator, view, maps.bounded_calls.items);
    if (maps.bounded_calls.items.len != topology.call_count or
        view.n_vars != topology.circuit_variables or view.nQm31OpsRows() != topology.circuit_rows)
        return error.BoundedTopologyMismatch;
    for (maps.bounded_calls.items, topology.callSlice()) |actual, wanted| {
        if (actual.call_id != wanted.call_id or actual.source_node_id != wanted.source_node_id or
            actual.input_node_id != wanted.input_node_id or
            !std.meta.eql(actual.input, wanted.input) or !std.meta.eql(actual.output, wanted.output))
            return error.BoundedTopologyMismatch;
    }
    const plan = try manyPlan(topology.callSlice());
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.meta.eql(root, topology.fixed_root)) return error.BoundedTopologyMismatch;
    var gate = try sealed.directGate(
        allocator,
        &pp,
        air_bundle_bytes,
        topology.source_sha256,
        topology.canonical_ir_sha256,
        root,
        [_]u8{0} ** 32,
    );
    defer gate.deinit();
    if (gate.value.components.len != 1) return error.BoundedCircuitAirMismatch;
    const selected = gate.value.components[0];
    if (selected.program_binding_sha256.len != 64 or selected.preprocessed_indices.len != 8)
        return error.BoundedCircuitAirMismatch;
    var selected_hash: v4.Digest = undefined;
    _ = try std.fmt.hexToBytes(&selected_hash, selected.program_binding_sha256);
    var selected_indices: [8]u32 = undefined;
    @memcpy(&selected_indices, selected.preprocessed_indices);
    const facts: v4.CircuitFacts = .{
        .trace_log_size = selected.trace_log_size,
        .evaluation_log_size = selected.evaluation_log_size,
        .main_columns = @intCast(selected.base_trace_columns),
        .interaction_columns = @intCast(selected.interaction_trace_columns),
        .preprocessed_indices = selected_indices,
        .n_constraints = selected.n_constraints,
        .selected_program_sha256 = selected_hash,
        .preprocessed_root = root,
    };
    var generated = try v4.fromSource(allocator, source_bytes, air_bundle_bytes, facts);
    errdefer generated.deinit();
    try attachCompiledEndpoints(&generated, topology.callSlice());
    var template = try cpu.air.parse(allocator, air_bundle_bytes);
    defer template.deinit();
    const candidate = try candidateManySchedule(generated.value, topology);
    const selected_geometry = try cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, candidate);
    const live = selected_geometry.live;
    try compareManyRoster(generated.value, try cpu.private_many_boundary.expectedRoster(
        plan,
        pp.traceLogSize(),
        selected.n_constraints,
    ), live, plan);
    generated.value.native_preflight = .{
        .tree_columns = live.tree_columns,
        .sample_width_limits = live.sample_width_limits,
        .max_column_log_size = live.max_column_log_size,
        .composition_log_size = live.composition_log_size,
        .composition_split = live.composition_split,
    };
    const precommitment = v4.precommitmentDigest(generated.value);
    const selected_schedule = selected_geometry.bindManifestDigest(precommitment);
    return .{
        .topology = topology,
        .generated = generated,
        .selected_schedule = selected_schedule,
        .preprocessed_root = root,
        .manifest_precommitment = precommitment,
        .effective_source_digest = selected_schedule.effectiveDigest(),
        .circuit_identity = selected_schedule.circuitIdentity(),
    };
}

/// Rebuild the source-owned inspection. A digest updated to match altered
/// candidate metadata is insufficient: the independent source recompilation
/// must reproduce the exact roster, fixed root, endpoints and identities.
/// This remains an inspection check, not a native proof verifier.
pub fn matchesManyInspection(
    allocator: std.mem.Allocator,
    candidate: *const ManyInspection,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
) !bool {
    var expected = try inspectMany(allocator, source_bytes, air_bundle_bytes);
    defer expected.deinit();
    if (!std.meta.eql(candidate.topology, expected.topology) or
        !std.meta.eql(candidate.preprocessed_root, expected.preprocessed_root) or
        !std.meta.eql(candidate.manifest_precommitment, expected.manifest_precommitment) or
        !std.meta.eql(candidate.selected_schedule.manifest_digest, expected.selected_schedule.manifest_digest) or
        !std.meta.eql(candidate.selected_schedule.geometry.source_digest, expected.selected_schedule.geometry.source_digest) or
        !std.meta.eql(candidate.selected_schedule.geometry.fixed_root, expected.selected_schedule.geometry.fixed_root) or
        candidate.selected_schedule.geometry.call_count != expected.selected_schedule.geometry.call_count or
        candidate.selected_schedule.geometry.slot_count != expected.selected_schedule.geometry.slot_count or
        !std.meta.eql(candidate.effective_source_digest, expected.effective_source_digest) or
        !std.meta.eql(candidate.circuit_identity, expected.circuit_identity) or
        !std.meta.eql(candidate.selected_schedule.geometry.live.pcs, expected.selected_schedule.geometry.live.pcs) or
        !std.meta.eql(candidate.selected_schedule.geometry.live.tree_columns, expected.selected_schedule.geometry.live.tree_columns) or
        !std.meta.eql(candidate.selected_schedule.geometry.live.sample_width_limits, expected.selected_schedule.geometry.live.sample_width_limits) or
        candidate.selected_schedule.geometry.live.count != expected.selected_schedule.geometry.live.count or
        candidate.selected_schedule.geometry.live.max_column_log_size != expected.selected_schedule.geometry.live.max_column_log_size or
        candidate.selected_schedule.geometry.live.composition_log_size != expected.selected_schedule.geometry.live.composition_log_size or
        candidate.selected_schedule.geometry.live.composition_split != expected.selected_schedule.geometry.live.composition_split)
        return false;
    for (candidate.selected_schedule.callSlice(), expected.selected_schedule.callSlice()) |actual, wanted|
        if (!std.meta.eql(actual, wanted)) return false;
    for (candidate.selected_schedule.slotSlice(), expected.selected_schedule.slotSlice()) |actual, wanted|
        if (!std.meta.eql(actual, wanted)) return false;
    for (candidate.selected_schedule.geometry.live.factSlice(), expected.selected_schedule.geometry.live.factSlice()) |actual, wanted|
        if (!std.meta.eql(actual, wanted)) return false;
    const left = try std.json.Stringify.valueAlloc(allocator, candidate.generated.value, .{});
    defer allocator.free(left);
    const right = try std.json.Stringify.valueAlloc(allocator, expected.generated.value, .{});
    defer allocator.free(right);
    return std.mem.eql(u8, left, right);
}

fn manyPlan(calls: []const EndpointCall) !cpu.private_many_boundary.Plan {
    if (calls.len == 0 or calls.len > admission.max_calls) return error.BoundedCallCountMismatch;
    var plan: cpu.private_many_boundary.Plan = .{ .count = @intCast(calls.len) };
    for (calls, plan.calls[0..calls.len], 0..) |call, *slot, id| {
        if (call.call_id != id or call.constant >= core.fields.m31.Modulus)
            return error.InvalidBoundedCall;
        slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    return plan;
}

fn compareManyRoster(
    value: v4.Manifest,
    planned: cpu.private_many_boundary.Roster,
    live: cpu.direct_many_preflight.Inspection,
    plan: cpu.private_many_boundary.Plan,
) !void {
    if (!std.meta.eql(value.pcs, v4.fixed_pcs)) return error.BoundedManyRosterMismatch;
    if (value.components.len != planned.count or value.claimed_sums != planned.count or
        value.main_columns != planned.main_width or
        value.interaction_columns != planned.interaction_width or
        value.total_constraints != planned.constraint_count or live.count != planned.count or
        live.tree_columns[0] != 8 or live.tree_columns[1] != planned.main_width or
        live.tree_columns[2] != planned.interaction_width or live.tree_columns[3] == 0 or
        live.composition_split != core.verifier_types.COMPOSITION_LOG_SPLIT or
        live.composition_log_size > live.max_column_log_size or
        live.pcs.fri_config.pow_bits != value.pcs.pow_bits or
        live.pcs.fri_config.log_blowup_factor != value.pcs.log_blowup_factor or
        live.pcs.fri_config.log_last_layer_degree_bound != value.pcs.last_layer_degree_bound - 1 or
        live.pcs.fri_config.n_queries != value.pcs.queries or
        live.pcs.fri_config.fold_step != value.pcs.fold_step or
        live.pcs.trace_lifting_log_size != value.max_component_trace_log_size + value.pcs.log_blowup_factor or
        live.pcs.preprocessed_lifting_log_size != value.components[0].trace_log_size + value.pcs.log_blowup_factor)
        return error.BoundedManyRosterMismatch;
    for (live.sample_width_limits) |width|
        if (width == 0 or width > 2) return error.BoundedManyRosterMismatch;
    var max_log: u32 = 0;
    for (value.components, planned.slice(), live.factSlice(), 0..) |component, spec, actual, index| {
        max_log = @max(max_log, spec.log_size);
        const wanted_role: v4.Role = switch (spec.kind) {
            .circuit => .circuit,
            .chip => .chip,
            .bridge => .bridge,
        };
        if (component.role != wanted_role or component.call_id != spec.call_id or
            component.proof_index != index or component.claimed_sum_index != index or
            component.trace_log_size != spec.log_size or
            component.main.tree != 1 or component.main.start != spec.main_offset or
            component.main.end != spec.main_offset + spec.main_columns or
            component.interaction.tree != 2 or component.interaction.start != spec.interaction_offset or
            component.interaction.end != spec.interaction_offset + spec.interaction_columns or
            component.n_constraints != spec.constraint_count or
            component.random_coefficient_offset != spec.constraint_offset or
            actual.kind != spec.kind or actual.call_id != spec.call_id or
            actual.trace_log_size != spec.log_size or
            actual.evaluation_log_size != component.evaluation_log_size or
            actual.main_offset != spec.main_offset or actual.main_columns != spec.main_columns or
            actual.interaction_offset != spec.interaction_offset or
            actual.interaction_columns != spec.interaction_columns or
            actual.constraint_offset != spec.constraint_offset or
            actual.n_constraints != spec.constraint_count or
            !std.mem.eql(u32, actual.preprocessedSlice(), component.preprocessed_indices) or
            !std.mem.eql(u32, actual.relationSlice(), component.lookup_relation_ids))
            return error.BoundedManyRosterMismatch;
        if (index == 0) {
            if (component.source != .bundled_air) return error.BoundedManyRosterMismatch;
        } else {
            const kind: v4.NativeKind = if (spec.kind == .chip) .tagged_chip else .tagged_bridge;
            if (component.source != .native_air or component.source.native_air.kind != kind or
                !std.meta.eql(actual.air_source_sha256, v4.nativeAirSourceDigest(kind)))
                return error.BoundedManyRosterMismatch;
            const id: usize = @intCast(spec.call_id orelse return error.BoundedManyRosterMismatch);
            if (spec.kind == .chip) {
                if (actual.chip_constant == null or actual.chip_constant.? != plan.calls[id].constant.toU32() or
                    actual.bridge_boundary != null) return error.BoundedManyRosterMismatch;
            } else {
                if (actual.bridge_boundary == null or !std.meta.eql(actual.bridge_boundary.?, plan.calls[id]) or
                    actual.chip_constant != null) return error.BoundedManyRosterMismatch;
            }
        }
    }
    if (value.max_component_trace_log_size != max_log) return error.BoundedManyRosterMismatch;
}

/// Recompile and inspect the exact selected bundled AIR and both native chip
/// and bridge handles. This returns metadata, never a key or proof verifier.
/// The guard is intentional: current tagged native handles reject call IDs
/// 2..7 and the native PCS roster is hardcoded to two calls. Even for two
/// calls, the source must pass the live V3 pair grammar and cross-path check.
pub fn inspectTwoCall(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
) !TwoCallInspection {
    const topology = try compileSourceTopology(allocator, source_bytes);
    if (topology.call_count != cpu.private_pair_boundary.n_calls)
        return error.NativeHandleCountUnsupported;
    var live = try live_pair.derive(allocator, source_bytes, air_bundle_bytes, 1);
    defer live.deinit();
    return inspectAgainstLivePair(allocator, source_bytes, air_bundle_bytes, topology, &live);
}

// Kept private so a caller cannot substitute a supposed V3 binding. The
// public inspection above always obtains it from the live source binding path.
fn inspectAgainstLivePair(
    allocator: std.mem.Allocator,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
    topology: Topology,
    live: *const live_pair.Binding,
) !TwoCallInspection {
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &maps);
    defer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    if (maps.bounded_calls.items.len != topology.call_count) return error.BoundedCallCountMismatch;
    const plan = try pairPlan(topology.callSlice());
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit);
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.meta.eql(root, topology.fixed_root)) return error.BoundedTopologyMismatch;
    var pair_generated = try sealed.directPair(
        allocator,
        &pp,
        plan,
        air_bundle_bytes,
        topology.source_sha256,
        topology.canonical_ir_sha256,
        root,
        [_]u8{0} ** 32,
    );
    defer pair_generated.deinit();
    try compareLivePairBinding(allocator, topology, root, pp.traceLogSize(), pair_generated.value, live);
    const selected = pair_generated.value.components[0];
    var selected_hash: v4.Digest = undefined;
    if (selected.program_binding_sha256.len != 64) return error.InvalidSelectedAirIdentity;
    _ = try std.fmt.hexToBytes(&selected_hash, selected.program_binding_sha256);
    if (selected.preprocessed_indices.len != 8) return error.InvalidSelectedAirGeometry;
    var selected_indices: [8]u32 = undefined;
    @memcpy(&selected_indices, selected.preprocessed_indices);
    const facts: v4.CircuitFacts = .{
        .trace_log_size = selected.trace_log_size,
        .evaluation_log_size = selected.evaluation_log_size,
        .main_columns = @intCast(selected.base_trace_columns),
        .interaction_columns = @intCast(selected.interaction_trace_columns),
        .preprocessed_indices = selected_indices,
        .n_constraints = selected.n_constraints,
        .selected_program_sha256 = selected_hash,
        .preprocessed_root = root,
    };
    var generated = try v4.fromSource(allocator, source_bytes, air_bundle_bytes, facts);
    errdefer generated.deinit();
    try attachCompiledEndpoints(&generated, topology.callSlice());
    try compareNativeRoster(generated.value, pair_generated.value, topology.callSlice());
    return .{ .topology = topology, .generated = generated, .preprocessed_root = root };
}

fn attachCompiledEndpoints(generated: *v4.Generated, calls: []const EndpointCall) !void {
    if (generated.value.calls.len != calls.len) return error.BoundedCallCountMismatch;
    const rebound = try generated.arena.allocator().dupe(v4.Call, generated.value.calls);
    for (rebound, calls) |*entry, compiled| {
        if (entry.call_id != compiled.call_id or entry.source_node_id != compiled.source_node_id or
            entry.input_node_id != compiled.input_node_id or entry.rounds != compiled.rounds or
            entry.constant != compiled.constant or entry.endpoints != null)
            return error.BoundedCompiledEndpointMismatch;
        entry.endpoints = .{ .input = compiled.input, .output = compiled.output };
    }
    generated.value.calls = rebound;
    try v4.rebindCompiledNativePrograms(generated);
}

fn compareLivePairBinding(
    allocator: std.mem.Allocator,
    topology: Topology,
    root: v4.Digest,
    trace_log_size: u32,
    bounded_pair_manifest: sealed.PairManifest,
    live: *const live_pair.Binding,
) !void {
    if (topology.call_count != cpu.private_pair_boundary.n_calls or
        !std.mem.eql(u8, &topology.source_sha256, &live.source_digest) or
        !std.mem.eql(u8, &topology.canonical_ir_sha256, &live.ir_digest) or
        !std.mem.eql(u8, &root, &live.preprocessed_root) or
        trace_log_size != live.trace_log_size or
        bounded_pair_manifest.components.len != live.generated.value.components.len or
        bounded_pair_manifest.components.len != 5)
        return error.BoundedLivePairMismatch;
    for (topology.callSlice(), live.plan.calls, 0..) |bounded_call, v3_call, id| {
        if (bounded_call.call_id != id or bounded_call.call_id != v3_call.call_id or
            bounded_call.rounds != v3_call.rounds or
            bounded_call.constant != v3_call.constant.toU32() or
            !std.meta.eql(bounded_call.input, v3_call.input) or
            !std.meta.eql(bounded_call.output, v3_call.output))
            return error.BoundedLivePairMismatch;
    }
    const bounded_air = bounded_pair_manifest.components[0];
    const v3_air = live.generated.value.components[0];
    if (bounded_air.source_index != v3_air.source_index or
        !std.mem.eql(u8, bounded_air.program_binding_sha256, v3_air.program_binding_sha256) or
        bounded_air.trace_log_size != v3_air.trace_log_size or
        bounded_air.evaluation_log_size != v3_air.evaluation_log_size or
        bounded_air.base_trace_columns != v3_air.base_trace_columns or
        bounded_air.interaction_trace_columns != v3_air.interaction_trace_columns or
        bounded_air.n_constraints != v3_air.n_constraints or
        bounded_air.random_coefficient_offset != v3_air.random_coefficient_offset or
        !std.mem.eql(u32, bounded_air.preprocessed_indices, v3_air.preprocessed_indices) or
        !try sealed.matchesPair(allocator, bounded_pair_manifest, live.generated.value))
        return error.BoundedLivePairMismatch;
}

/// Rederive all source, circuit and native facts. A candidate altered together
/// with its own digest still fails the comparison. This is an inspection check
/// only and must not be used as a native proof admission API.
pub fn matchesTwoCallInspection(
    allocator: std.mem.Allocator,
    candidate: *const TwoCallInspection,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
) !bool {
    var expected = try inspectTwoCall(allocator, source_bytes, air_bundle_bytes);
    defer expected.deinit();
    if (!std.meta.eql(candidate.topology, expected.topology) or
        !std.meta.eql(candidate.preprocessed_root, expected.preprocessed_root)) return false;
    const left = try std.json.Stringify.valueAlloc(allocator, candidate.generated.value, .{});
    defer allocator.free(left);
    const right = try std.json.Stringify.valueAlloc(allocator, expected.generated.value, .{});
    defer allocator.free(right);
    return std.mem.eql(u8, left, right);
}

fn pairPlan(calls: []const EndpointCall) !cpu.private_pair_boundary.Plan {
    if (calls.len != cpu.private_pair_boundary.n_calls) return error.NativeHandleCountUnsupported;
    var result: cpu.private_pair_boundary.Plan = .{ .calls = undefined };
    for (calls, &result.calls, 0..) |call, *slot, id| {
        if (call.call_id != id or call.constant >= core.fields.m31.Modulus)
            return error.InvalidBoundedCall;
        slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    return result;
}

fn compareNativeRoster(value: v4.Manifest, actual: sealed.PairManifest, calls: []const EndpointCall) !void {
    if (value.components.len != 5 or actual.components.len != 5 or value.calls.len != 2 or
        value.claimed_sums != actual.claimed_sums)
        return error.BoundedNativeRosterMismatch;
    for (calls, actual.pair_calls, value.calls) |compiled, native, source| {
        const endpoints = source.endpoints orelse return error.BoundedNativeRosterMismatch;
        if (compiled.call_id != native.call_id or compiled.call_id != source.call_id or
            compiled.rounds != native.rounds or compiled.rounds != source.rounds or
            compiled.constant != native.constant or compiled.constant != source.constant or
            !std.meta.eql(compiled.input, endpoints.input) or !std.meta.eql(compiled.output, endpoints.output) or
            !std.meta.eql(compiled.input, native.input) or !std.meta.eql(compiled.output, native.output))
            return error.BoundedNativeRosterMismatch;
    }
    for (value.components, actual.components, 0..) |candidate, handle, index| {
        if (candidate.proof_index != handle.proof_index or
            handle.claimed_sum_index == null or candidate.claimed_sum_index != handle.claimed_sum_index.? or
            candidate.trace_log_size != handle.trace_log_size or
            candidate.evaluation_log_size != handle.evaluation_log_size or
            candidate.main.tree != 1 or candidate.interaction.tree != 2 or
            handle.main_trace_span == null or handle.interaction_trace_span == null or
            candidate.main.start != handle.main_trace_span.?.start or
            candidate.main.end != handle.main_trace_span.?.end or
            candidate.interaction.start != handle.interaction_trace_span.?.start or
            candidate.interaction.end != handle.interaction_trace_span.?.end or
            candidate.n_constraints != handle.n_constraints or
            candidate.random_coefficient_offset != handle.random_coefficient_offset or
            !std.mem.eql(u32, candidate.preprocessed_indices, handle.preprocessed_indices) or
            !std.mem.eql(u32, candidate.lookup_relation_ids, handle.lookup_relation_ids orelse return error.BoundedNativeRosterMismatch))
            return error.BoundedNativeRosterMismatch;
        if (index == 0) {
            if (candidate.role != .circuit or candidate.call_id != null or
                candidate.source != .bundled_air or candidate.source.bundled_air.index != handle.source_index)
                return error.BoundedNativeRosterMismatch;
        } else {
            const chip_role = index <= 2;
            if (candidate.role != (if (chip_role) v4.Role.chip else v4.Role.bridge) or
                candidate.call_id == null or candidate.call_id.? != @as(u32, @intCast(if (chip_role) index - 1 else index - 3)) or
                candidate.source != .native_air or handle.source_index != 0 or
                candidate.source.native_air.kind != (if (chip_role) v4.NativeKind.tagged_chip else v4.NativeKind.tagged_bridge))
                return error.BoundedNativeRosterMismatch;
        }
    }
}

fn validateEndpoints(allocator: std.mem.Allocator, view: circuit.common.preprocessed.CircuitView, calls: []const compiler.BoundedCallMap) !void {
    try view.validate();
    try view.validateUniqueProducers(allocator);
    if (calls.len == 0 or calls.len > admission.max_calls) return error.BoundedCallCountMismatch;
    const counts = try view.computeUses(allocator);
    defer allocator.free(counts);
    try circuit.common.preprocessed.addCanonicalMultiplicity(&counts[0], view.permutationRows());
    for (calls, 0..) |call, id| {
        if (call.call_id != id) return error.BoundedCallOrderMismatch;
        for (call.input ++ call.output) |address| {
            if (address <= 2 or address >= view.n_vars or address >= core.fields.m31.Modulus or
                std.mem.indexOfScalar(u32, view.output, address) != null)
                return error.InvalidBoundedEndpoint;
            var producers: usize = 0;
            inline for (.{ view.add, view.sub, view.mul, view.pointwise_mul }) |gates| {
                for (gates) |gate| producers += @intFromBool(gate.out == address);
            }
            for (view.permutation_outputs) |output| producers += @intFromBool(output == address);
            if (producers != 1) return error.InvalidBoundedProducer;
            try circuit.common.preprocessed.addCanonicalMultiplicity(&counts[address], 1);
        }
    }
}

fn padDirect(allocator: std.mem.Allocator, comptime V: type, ctx: *circuit.builder.Context(V)) !void {
    const raw = circuit.common.finalize.rawComponentSizes(circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit));
    if (raw.eq != 0 or raw.triple_xor != 0 or raw.m31_to_u32 != 0 or raw.blake_g_gate != 0)
        return error.UnsupportedBoundedCircuit;
    try circuit.common.finalize.padToTargets(V, ctx, .{
        .eq = 0,
        .qm31_ops = circuit.common.finalize.paddedSize(raw.qm31_ops),
        .m31_to_u32 = 0,
        .triple_xor = 0,
        .blake_g_gate = 0,
    });
    if (try ctx.circuit.firstYieldViolation(allocator) != null) return error.InvalidBoundedYieldTopology;
}

fn digest(bytes: []const u8) v4.Digest {
    var result: v4.Digest = undefined;
    Sha256.hash(bytes, &result, .{});
    return result;
}

test "bounded pair endpoints agree in topology and witness compilation" {
    const a = std.testing.allocator;
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    var topology = try compileSourceTopology(a, source);
    try std.testing.expectEqual(@as(usize, 2), topology.call_count);
    try std.testing.expectEqual(@as(u32, 0), topology.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 1), topology.calls[1].call_id);
    var assignment = try relation.parseAssignment(a, @embedFile("../examples/boundary/private_pair16_32.valid.json"));
    defer assignment.deinit();
    try checkWitnessTopology(a, source, assignment.value, topology);
    topology.calls[0].input[0] += 1;
    try std.testing.expectError(error.BoundedWitnessTopologyMismatch, checkWitnessTopology(a, source, assignment.value, topology));
    topology.calls[0].input[0] -= 1;
    topology.calls[0].rounds += 16;
    try std.testing.expectError(error.BoundedSourceMismatch, checkWitnessTopology(a, source, assignment.value, topology));
    topology.calls[0].rounds -= 16;
    topology.calls[0].constant += 1;
    try std.testing.expectError(error.BoundedSourceMismatch, checkWitnessTopology(a, source, assignment.value, topology));
    topology.calls[0].constant -= 1;
    topology.fixed_root[0] ^= 1;
    try std.testing.expectError(error.BoundedWitnessTopologyMismatch, checkWitnessTopology(a, source, assignment.value, topology));
}

test "bounded two-call inspection rebinds selected AIR and native handle geometry" {
    const a = std.testing.allocator;
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const air = @embedFile("s31_air_programs");
    var inspection = try inspectTwoCall(a, source, air);
    defer inspection.deinit();
    try std.testing.expectEqual(@as(usize, 5), inspection.generated.value.components.len);
    try std.testing.expectEqual(@as(u32, 46), inspection.generated.value.main_columns);
    try std.testing.expectEqual(@as(u32, 64), inspection.generated.value.interaction_columns);
    try std.testing.expect(inspection.generated.value.calls[0].endpoints != null);
    try std.testing.expect(try matchesTwoCallInspection(a, &inspection, source, air));
    const original_digest = v4.precommitmentDigest(inspection.generated.value);
    const calls = try a.dupe(v4.Call, inspection.generated.value.calls);
    defer a.free(calls);
    inspection.generated.value.calls = calls;
    const original_call = calls[0];
    var altered_endpoint = calls[0].endpoints.?;
    altered_endpoint.input[0] += 1;
    calls[0].endpoints = altered_endpoint;
    const endpoint_digest = v4.precommitmentDigest(inspection.generated.value);
    try std.testing.expect(!std.mem.eql(u8, &original_digest, &endpoint_digest));
    try std.testing.expect(!try matchesTwoCallInspection(a, &inspection, source, air));
    calls[0] = original_call;
    const components = try a.dupe(v4.Component, inspection.generated.value.components);
    defer a.free(components);
    inspection.generated.value.components = components;
    const original_circuit = components[0];
    const indices = try a.dupe(u32, components[0].preprocessed_indices);
    defer a.free(indices);
    components[0].preprocessed_indices = indices;
    std.mem.swap(u32, &indices[1], &indices[2]);
    const resealed_digest = v4.precommitmentDigest(inspection.generated.value);
    try std.testing.expect(!std.mem.eql(u8, &original_digest, &resealed_digest));
    try std.testing.expect(!try matchesTwoCallInspection(a, &inspection, source, air));
    components[0] = original_circuit;
    components[2].random_coefficient_offset += 1;
    try std.testing.expect(!try matchesTwoCallInspection(a, &inspection, source, air));
    components[2].random_coefficient_offset -= 1;
    inspection.topology.calls[1].output[0] += 1;
    try std.testing.expect(!try matchesTwoCallInspection(a, &inspection, source, air));
    try std.testing.expectError(error.InvalidMagic, inspectTwoCall(a, source, "wrong bundle"));
}

test "bounded cross-path inspection rejects forced live V3 mismatch" {
    const a = std.testing.allocator;
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const air = @embedFile("s31_air_programs");
    const topology = try compileSourceTopology(a, source);
    var live = try live_pair.derive(a, source, air, 1);
    defer live.deinit();

    const original_address = live.plan.calls[0].output[0];
    live.plan.calls[0].output[0] += 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, inspectAgainstLivePair(a, source, air, topology, &live));
    live.plan.calls[0].output[0] = original_address;

    const original_source_digest = live.source_digest;
    live.source_digest[0] ^= 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, live.preprocessed_root, live.trace_log_size, live.generated.value, &live));
    live.source_digest = original_source_digest;

    const original_ir_digest = live.ir_digest;
    live.ir_digest[0] ^= 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, live.preprocessed_root, live.trace_log_size, live.generated.value, &live));
    live.ir_digest = original_ir_digest;

    const original_root = live.preprocessed_root;
    live.preprocessed_root[0] ^= 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, original_root, live.trace_log_size, live.generated.value, &live));
    live.preprocessed_root = original_root;

    const original_trace_log = live.trace_log_size;
    live.trace_log_size += 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, live.preprocessed_root, original_trace_log, live.generated.value, &live));
    live.trace_log_size = original_trace_log;

    const components = try a.dupe(sealed.Component, live.generated.value.components);
    defer a.free(components);
    var altered = live.generated.value;
    altered.components = components;
    components[0].evaluation_log_size += 1;
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, live.preprocessed_root, live.trace_log_size, altered, &live));
    components[0] = live.generated.value.components[0];
    components[0].program_binding_sha256 = "forged-selected-air";
    try std.testing.expectError(error.BoundedLivePairMismatch, compareLivePairBinding(a, topology, live.preprocessed_root, live.trace_log_size, altered, &live));
}

fn chainProgram(a: std.mem.Allocator, n: usize, steps: []relation.Step) !relation.Program {
    const inputs = try a.alloc(relation.Input, 1);
    inputs[0] = .{ .name = "x", .kind = .m31, .length = 4, .visibility = .private };
    const nodes = try a.alloc(relation.Node, n + 1);
    var previous: []const u8 = "x";
    for (nodes[0..n], 0..) |*node, id| {
        const name = try std.fmt.allocPrint(a, "r{d}", .{id});
        node.* = .{ .name = name, .op = .repeat, .lhs = previous, .rounds = 16, .body = steps };
        previous = name;
    }
    nodes[n] = .{ .name = "total", .op = .sum_lanes, .lhs = previous };
    const outputs = try a.alloc([]const u8, 1);
    outputs[0] = "total";
    return .{
        .version = 1,
        .name = "bounded_chain",
        .inputs = inputs,
        .nodes = nodes,
        .assertions = &.{},
        .public_outputs = outputs,
    };
}

test "bounded eight-call source compiles eight ordered endpoint maps" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    const program = try chainProgram(a, 8, &steps);
    const topology = try compileProgramTopology(a, program, "synthetic-eight-call-source");
    try std.testing.expectEqual(@as(usize, 8), topology.call_count);
    for (topology.callSlice(), 0..) |call, id| {
        try std.testing.expectEqual(@as(u32, @intCast(id)), call.call_id);
        for (call.input ++ call.output) |address| try std.testing.expect(address > 2 and address < topology.circuit_variables);
    }
}

test "bounded native inspection fails closed outside exact two-call schedule" {
    const one =
        \\{"version":1,"name":"one","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"r","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":3}]},{"name":"sum","op":"sum_lanes","lhs":"r"}],"assertions":[],"public_outputs":["sum"]}
    ;
    const three =
        \\{"version":1,"name":"three","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"a","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":3}]},{"name":"b","op":"repeat","lhs":"a","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":5}]},{"name":"c","op":"repeat","lhs":"b","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":7}]},{"name":"sum","op":"sum_lanes","lhs":"c"}],"assertions":[],"public_outputs":["sum"]}
    ;
    for ([_][]const u8{ one, three }) |source| {
        const topology = try compileSourceTopology(std.testing.allocator, source);
        try std.testing.expect(topology.call_count == 1 or topology.call_count == 3);
        try std.testing.expectError(error.NativeHandleCountUnsupported, inspectTwoCall(std.testing.allocator, source, @embedFile("s31_air_programs")));
        var inspection = try inspectMany(std.testing.allocator, source, @embedFile("s31_air_programs"));
        defer inspection.deinit();
        try std.testing.expectEqual(topology.call_count, inspection.generated.value.calls.len);
        try std.testing.expectEqual(@as(usize, 1 + 2 * topology.call_count), inspection.generated.value.components.len);
        try std.testing.expectEqual(@as(u32, @intCast(12 + 17 * topology.call_count)), inspection.generated.value.main_columns);
        try std.testing.expectEqual(@as(u32, @intCast(8 + 28 * topology.call_count)), inspection.generated.value.interaction_columns);
        try std.testing.expect(try matchesManyInspection(std.testing.allocator, &inspection, source, @embedFile("s31_air_programs")));
        const plan = try manyPlan(topology.callSlice());
        const roster = try cpu.private_many_boundary.expectedRoster(
            plan,
            inspection.generated.value.components[0].trace_log_size,
            inspection.generated.value.components[0].n_constraints,
        );
        var forged_live = inspection.selected_schedule.geometry.live;
        forged_live.facts[1].evaluation_log_size += 1;
        try std.testing.expectError(error.BoundedManyRosterMismatch, compareManyRoster(inspection.generated.value, roster, forged_live, plan));
        forged_live = inspection.selected_schedule.geometry.live;
        forged_live.facts[1].relation_ids[0] ^= 1;
        try std.testing.expectError(error.BoundedManyRosterMismatch, compareManyRoster(inspection.generated.value, roster, forged_live, plan));
        forged_live = inspection.selected_schedule.geometry.live;
        forged_live.facts[1].air_source_sha256[0] ^= 1;
        try std.testing.expectError(error.BoundedManyRosterMismatch, compareManyRoster(inspection.generated.value, roster, forged_live, plan));
        forged_live = inspection.selected_schedule.geometry.live;
        forged_live.sample_width_limits[1] = 3;
        try std.testing.expectError(error.BoundedManyRosterMismatch, compareManyRoster(inspection.generated.value, roster, forged_live, plan));
        const original_components = inspection.generated.value.components;
        const original_bridge_binding = original_components[1 + topology.call_count].source.native_air.program_binding_sha256;
        const original_calls = inspection.generated.value.calls;
        const changed = try std.testing.allocator.dupe(v4.Call, inspection.generated.value.calls);
        defer std.testing.allocator.free(changed);
        inspection.generated.value.calls = changed;
        defer inspection.generated.value.calls = original_calls;
        changed[0].endpoints.?.input[0] += 1;
        try v4.rebindCompiledNativePrograms(&inspection.generated);
        defer inspection.generated.value.components = original_components;
        const changed_bridge_binding = inspection.generated.value.components[1 + topology.call_count].source.native_air.program_binding_sha256;
        try std.testing.expect(!std.meta.eql(original_bridge_binding, changed_bridge_binding));
        inspection.manifest_precommitment = v4.precommitmentDigest(inspection.generated.value);
        try std.testing.expect(!try matchesManyInspection(std.testing.allocator, &inspection, source, @embedFile("s31_air_programs")));
    }
}

test "bounded V4 selected geometry rejects reordered and altered manifest slots" {
    const allocator = std.testing.allocator;
    const source = @embedFile("../examples/boundary/private_many1.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    var inspection = try inspectMany(allocator, source, air_bytes);
    defer inspection.deinit();
    var topology_ctx = try compileManyTopology(allocator, source, inspection.topology);
    defer topology_ctx.deinit();
    const plan = inspection.selected_schedule.fixedCircuitPlan();
    var pp = try plan.preprocessed(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&topology_ctx.circuit));
    defer pp.deinit(allocator);
    var template = try cpu.air.parse(allocator, air_bytes);
    defer template.deinit();
    const original = try candidateManySchedule(inspection.generated.value, inspection.topology);
    const selected = try cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, original);
    try std.testing.expectEqual(@as(usize, 3), selected.slot_count);
    try std.testing.expectEqual(@as(u8, 1), selected.call_count);

    var changed = original;
    changed.slots[1].proof_index = 2;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.slots[1].claimed_sum_index = 0;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.slots[1].source_kind = .tagged_bridge;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.slots[1].main_columns += 1;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.slots[1].relation_ids[0] ^= 1;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.slots[0].preprocessed_indices[0] ^= 1;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.fixed_root[0] ^= 1;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));
    changed = original;
    changed.pcs_profile.queries += 1;
    try std.testing.expectError(error.InvalidManySchedule, cpu.direct_many_schedule.selectGeometry(allocator, &pp, &template, changed));

    // These identities are authenticated by the source-pinned S31 wrapper,
    // not by the engine geometry selector alone.
    var changed_inspection = inspection;
    changed_inspection.selected_schedule.geometry.source_digest[0] ^= 1;
    try std.testing.expect(!try matchesManyInspection(allocator, &changed_inspection, source, air_bytes));
    changed_inspection = inspection;
    changed_inspection.selected_schedule.geometry.slots[1].program_binding_sha256[0] ^= 1;
    try std.testing.expect(!try matchesManyInspection(allocator, &changed_inspection, source, air_bytes));
    changed_inspection = inspection;
    changed_inspection.selected_schedule.manifest_digest[0] ^= 1;
    try std.testing.expect(!try matchesManyInspection(allocator, &changed_inspection, source, air_bytes));
    changed_inspection = inspection;
    changed_inspection.selected_schedule.geometry.call_count = 9;
    try std.testing.expectError(error.InvalidManySchedule, changed_inspection.selected_schedule.validateShape());
}

test "bounded V4 source-derived one-call native proof verifies a public statement" {
    // This exercises the source-owned in-memory adapter. It is deliberately
    // absent from the S31 proof-byte API until a source-pinned V4 envelope
    // and cross-count release matrix exist.
    const allocator = std.heap.smp_allocator;
    const source =
        \\{"version":1,"name":"one_call_native","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"r","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},{"name":"sum","op":"add","lhs":"r","rhs":"x"},{"name":"product","op":"mul","lhs":"r","rhs":"x"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    const assignment_json =
        \\{"public_inputs":{},"private_inputs":{"x":[3,5,7,11]},"public_outputs":{"sum":[532178715,836413119,2108197393,1611365786],"product":[1596536136,2034581923,1872479820,545154349]}}
    ;
    const air_bytes = @embedFile("s31_air_programs");
    var inspection = try inspectMany(allocator, source, air_bytes);
    defer inspection.deinit();
    const request = try nativeManyRequest(&inspection);
    try std.testing.expectEqual(@as(u8, 1), request.plan.count);
    var assignment = try relation.parseAssignment(allocator, assignment_json);
    defer assignment.deinit();
    var witness = try compileManyWitness(allocator, source, assignment.value, inspection.topology);
    defer witness.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment.value);
    var bundle = try cpu.experimental_direct_many_arithmetic.parseBundle(allocator, air_bytes);
    defer bundle.deinit();
    var proof = try cpu.experimental_direct_many_arithmetic.prove(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit),
        witness.values(),
        &bundle,
        inspection.selected_schedule.geometry.live.pcs,
        request,
    );
    defer proof.deinit();
    try std.testing.expectEqual(@as(usize, 3), proof.sum_count);
    var topology_maps = compiler.Maps{};
    defer topology_maps.deinit(allocator);
    var topology_ctx = try compiler.compileDirectBoundedWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &topology_maps);
    defer topology_ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &topology_ctx);
    try cpu.experimental_direct_many_arithmetic.verify(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&topology_ctx.circuit),
        &bundle,
        inspection.selected_schedule.geometry.live.pcs,
        request,
        words,
        &proof,
    );
    var changed_words = words;
    changed_words[0] += 1;
    try std.testing.expectError(
        error.InvalidManyPublicStatement,
        cpu.experimental_direct_many_arithmetic.verify(
            allocator,
            circuit.common.preprocessed.CircuitView.fromBuilder(&topology_ctx.circuit),
            &bundle,
            inspection.selected_schedule.geometry.live.pcs,
            request,
            changed_words,
            &proof,
        ),
    );
    const changed_source = try std.fmt.allocPrint(allocator, "{s} ", .{source});
    defer allocator.free(changed_source);
    var changed_inspection = try inspectMany(allocator, changed_source, air_bytes);
    defer changed_inspection.deinit();
    const changed_request = try nativeManyRequest(&changed_inspection);
    try std.testing.expectError(
        error.InvalidManyCircuitHash,
        cpu.experimental_direct_many_arithmetic.verify(
            allocator,
            circuit.common.preprocessed.CircuitView.fromBuilder(&topology_ctx.circuit),
            &bundle,
            changed_inspection.selected_schedule.geometry.live.pcs,
            changed_request,
            words,
            &proof,
        ),
    );
}
