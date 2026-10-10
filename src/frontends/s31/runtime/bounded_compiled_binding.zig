//! Compiled endpoint inspection for the bounded-call V4 plan.
//!
//! No function in this module parses or accepts a proof. The pinned engine has
//! a two-call native schedule; only that count can be rebound to actual native
//! component handles. All counts can be compiled to circuit endpoint wires.
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
    const source_hash = digest(source_bytes);
    if (!std.mem.eql(u8, &source_hash, &expected.source_sha256)) return error.BoundedSourceMismatch;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    const plan = try admission.extract(allocator, parsed.value);
    if (!std.mem.eql(u8, &plan.canonical_ir_sha256, &expected.canonical_ir_sha256) or
        plan.call_count != expected.call_count)
        return error.BoundedSourceMismatch;
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectBoundedWithSpans(QM31, allocator, parsed.value, assignment, &maps);
    defer ctx.deinit();
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
    }
}
