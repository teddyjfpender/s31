//! Source-derived V4 roster blueprint for 1..8 tagged chip calls.
//!
//! This is deliberately separate from the sealed V3 pair manifest. It does
//! not authorize a proof: source admission has no compiled endpoint addresses,
//! and no native prover/verifier checks this roster against component handles.
//! The tagged chip and bridge sources are templates: their current pair AIR
//! caps call IDs below two and is not an eight-call proof engine.
const std = @import("std");
const admission = @import("../language/bounded_call_admission.zig");
const relation = @import("../language/relation.zig");
const canonical = @import("../language/canonical.zig");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const Sha256 = std.crypto.hash.sha2.Sha256;
const chip = cpu.tagged_pair_chip;
const bridge = cpu.tagged_pair_bridge;
const pair = cpu.private_pair_boundary;

pub const schema = "s31-component-manifest-bounded-call-plan-v4";
pub const profile = "direct-m31-bounded-call-plan-v4";
pub const max_components = 1 + 2 * admission.max_calls;
pub const max_public_words: u32 = circuit.common.component_list.N_RESERVED;
pub const Digest = [32]u8;
pub const Span = struct { tree: u8, start: u32, end: u32 };
pub const Role = enum(u8) { circuit, chip, bridge };
pub const NativeKind = enum(u8) { tagged_chip, tagged_bridge };

/// A bundle slot and a native source have different identity spaces. V4 never
/// interprets the legacy native `source_index = 0` sentinel as a bundle slot.
pub const Source = union(enum) {
    bundled_air: struct { index: u32, bundle_sha256: Digest, selected_program_sha256: Digest },
    native_air: struct { kind: NativeKind, program_binding_sha256: Digest },
};

pub const Component = struct {
    role: Role,
    call_id: ?u32,
    source: Source,
    proof_index: u32,
    claimed_sum_index: u32,
    trace_log_size: u32,
    evaluation_log_size: u32,
    main: Span,
    interaction: Span,
    n_constraints: u32,
    random_coefficient_offset: u32,
    preprocessed_indices: []const u32,
    lookup_relation_ids: []const u32,
};

pub const Call = struct {
    call_id: u32,
    source_node_id: u32,
    input_node_id: u32,
    rounds: u32,
    constant: u32,
    /// Absent in the source-only blueprint. The compiled inspection attaches
    /// canonical circuit addresses after comparing the source and compiler plans.
    endpoints: ?Endpoints = null,
};

pub const Endpoints = struct {
    input: [4]u32,
    output: [4]u32,
};

pub const PublicOutput = struct {
    name: []const u8,
    canonical_node_id: u32,
    kind: relation.Kind,
    length: u32,
    word_offset: u32,
};

pub const PcsProfile = struct {
    pow_bits: u32,
    log_blowup_factor: u32,
    last_layer_degree_bound: u32,
    queries: u32,
    fold_step: u32,
};

pub const fixed_pcs: PcsProfile = .{
    .pow_bits = 26,
    .log_blowup_factor = 1,
    .last_layer_degree_bound = 1,
    .queries = 70,
    .fold_step = 1,
};

/// These facts must eventually come from a rebound AIR and a compiled direct
/// circuit, not from a package or proof. They are inputs to this plan-only API.
pub const CircuitFacts = struct {
    trace_log_size: u32,
    evaluation_log_size: u32,
    main_columns: u32,
    interaction_columns: u32,
    preprocessed_indices: [8]u32,
    n_constraints: u32,
    selected_program_sha256: Digest,
    preprocessed_root: Digest,
};

pub const Manifest = struct {
    schema_version: []const u8,
    proof_profile: []const u8,
    source_sha256: Digest,
    canonical_ir_sha256: Digest,
    bundle_sha256: Digest,
    native_template_sha256: Digest,
    preprocessed_root: Digest,
    calls: []const Call,
    public_outputs: []const PublicOutput,
    public_word_count: u32,
    pcs: PcsProfile,
    max_component_trace_log_size: u32,
    components: []const Component,
    claimed_sums: u32,
    total_constraints: u32,
    main_columns: u32,
    interaction_columns: u32,
};

pub const Generated = struct {
    arena: std.heap.ArenaAllocator,
    value: Manifest,

    pub fn deinit(self: *Generated) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Regenerate from literal source bytes. A caller cannot supply call IDs,
/// source node IDs, or component order independently of canonical admission.
pub fn fromSource(
    backing: std.mem.Allocator,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
    facts: CircuitFacts,
) !Generated {
    if (source_bytes.len > admission.max_source_bytes) return error.ManyCallSourceTooLarge;
    var parsed = try relation.parseProgram(backing, source_bytes);
    defer parsed.deinit();
    const plan = try admission.extract(backing, parsed.value);
    var ir = try canonical.build(backing, parsed.value);
    defer ir.deinit();
    if (!std.meta.eql(plan.canonical_ir_sha256, ir.sha256)) return error.InvalidBoundedManifestSource;
    return fromPlan(backing, source_bytes, air_bundle_bytes, facts, &plan, &ir);
}

fn fromPlan(
    backing: std.mem.Allocator,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
    facts: CircuitFacts,
    plan: *const admission.Plan,
    ir: *const canonical.IR,
) !Generated {
    if (plan.call_count == 0 or plan.call_count > admission.max_calls or
        facts.trace_log_size < 4 or facts.trace_log_size > 30 or
        facts.evaluation_log_size <= facts.trace_log_size or facts.evaluation_log_size > 32 or
        facts.main_columns == 0 or facts.interaction_columns == 0 or
        facts.n_constraints == 0)
        return error.InvalidBoundedManifestFacts;
    for (facts.preprocessed_indices, 0..) |index, position| {
        if (index >= 8) return error.InvalidBoundedPreprocessedIndex;
        for (facts.preprocessed_indices[0..position]) |earlier|
            if (index == earlier) return error.InvalidBoundedPreprocessedIndex;
    }
    var arena = std.heap.ArenaAllocator.init(backing);
    errdefer arena.deinit();
    const a = arena.allocator();
    const bundle_digest = digest(air_bundle_bytes);
    const template_digest = nativeTemplateDigest();
    const calls = try a.alloc(Call, plan.call_count);
    if (ir.public_outputs.len != plan.public_output_count) return error.InvalidBoundedManifestSource;
    const public_outputs = try a.alloc(PublicOutput, ir.public_outputs.len);
    var public_word_count: u32 = 0;
    for (ir.public_outputs, public_outputs, 0..) |output, *entry, index| {
        if (output.id != plan.public_output_ids[index] or output.id >= ir.nodes.len)
            return error.InvalidBoundedManifestSource;
        const node = ir.nodes[output.id];
        if (node.kind != .m31 or node.length == 0 or node.length > 4)
            return error.InvalidBoundedManifestPublicAbi;
        entry.* = .{
            .name = try a.dupe(u8, output.name),
            .canonical_node_id = output.id,
            .kind = node.kind,
            .length = node.length,
            .word_offset = public_word_count,
        };
        public_word_count = try std.math.add(u32, public_word_count, node.length);
        if (public_word_count > max_public_words) return error.TooManyBoundedPublicWords;
    }
    const components = try a.alloc(Component, 1 + 2 * plan.call_count);
    var main_end = facts.main_columns;
    var interaction_end = facts.interaction_columns;
    var constraint_end = facts.n_constraints;
    var max_trace_log = facts.trace_log_size;
    components[0] = .{
        .role = .circuit,
        .call_id = null,
        .source = .{ .bundled_air = .{
            .index = 1,
            .bundle_sha256 = bundle_digest,
            .selected_program_sha256 = facts.selected_program_sha256,
        } },
        .proof_index = 0,
        .claimed_sum_index = 0,
        .trace_log_size = facts.trace_log_size,
        .evaluation_log_size = facts.evaluation_log_size,
        .main = .{ .tree = 1, .start = 0, .end = main_end },
        .interaction = .{ .tree = 2, .start = 0, .end = interaction_end },
        .n_constraints = facts.n_constraints,
        .random_coefficient_offset = 0,
        .preprocessed_indices = try a.dupe(u32, &facts.preprocessed_indices),
        .lookup_relation_ids = try a.dupe(u32, &.{circuit.common.component_list.GATE_RELATION_ID}),
    };

    // Canonical order is circuit, all chips, then all bridges. Every span and
    // coefficient interval is calculated with checked addition, including
    // the largest admitted eight-call plan.
    for (plan.callSlice(), 0..) |source_call, id| {
        if (source_call.call_id != id or source_call.constant >= core.fields.m31.Modulus or
            source_call.input_node_id >= source_call.source_node_id or
            (id != 0 and source_call.source_node_id <= calls[id - 1].source_node_id))
            return error.InvalidBoundedManifestCall;
        calls[id] = .{
            .call_id = source_call.call_id,
            .source_node_id = source_call.source_node_id,
            .input_node_id = source_call.input_node_id,
            .rounds = source_call.rounds,
            .constant = source_call.constant,
        };
        const log_size = try chip.validateRounds(source_call.rounds);
        max_trace_log = @max(max_trace_log, log_size);
        const next_main = try std.math.add(u32, main_end, @intCast(chip.main_width));
        const next_interaction = try std.math.add(u32, interaction_end, @intCast(chip.interaction_width));
        const index: u32 = @intCast(1 + id);
        components[1 + id] = .{
            .role = .chip,
            .call_id = source_call.call_id,
            .source = .{ .native_air = .{
                .kind = .tagged_chip,
                .program_binding_sha256 = nativeProgramDigest(.tagged_chip, template_digest, source_call),
            } },
            .proof_index = index,
            .claimed_sum_index = index,
            .trace_log_size = log_size,
            .evaluation_log_size = try std.math.add(u32, log_size, 1),
            .main = .{ .tree = 1, .start = main_end, .end = next_main },
            .interaction = .{ .tree = 2, .start = interaction_end, .end = next_interaction },
            .n_constraints = @intCast(pair.chip_n_constraints),
            .random_coefficient_offset = constraint_end,
            .preprocessed_indices = &.{},
            .lookup_relation_ids = try a.dupe(u32, &.{pair.relation_id}),
        };
        main_end = next_main;
        interaction_end = next_interaction;
        constraint_end = try std.math.add(u32, constraint_end, @intCast(pair.chip_n_constraints));
    }
    for (plan.callSlice(), 0..) |source_call, id| {
        const next_main = try std.math.add(u32, main_end, @intCast(bridge.main_width));
        const next_interaction = try std.math.add(u32, interaction_end, @intCast(bridge.interaction_width));
        const index: u32 = @intCast(1 + plan.call_count + id);
        components[1 + plan.call_count + id] = .{
            .role = .bridge,
            .call_id = source_call.call_id,
            .source = .{ .native_air = .{
                .kind = .tagged_bridge,
                .program_binding_sha256 = nativeProgramDigest(.tagged_bridge, template_digest, source_call),
            } },
            .proof_index = index,
            .claimed_sum_index = index,
            .trace_log_size = bridge.log_size,
            .evaluation_log_size = try std.math.add(u32, bridge.log_size, 2),
            .main = .{ .tree = 1, .start = main_end, .end = next_main },
            .interaction = .{ .tree = 2, .start = interaction_end, .end = next_interaction },
            .n_constraints = @intCast(bridge.n_constraints),
            .random_coefficient_offset = constraint_end,
            .preprocessed_indices = &.{},
            .lookup_relation_ids = try a.dupe(u32, &.{ circuit.common.component_list.GATE_RELATION_ID, pair.relation_id }),
        };
        main_end = next_main;
        interaction_end = next_interaction;
        constraint_end = try std.math.add(u32, constraint_end, @intCast(bridge.n_constraints));
    }
    return .{ .arena = arena, .value = .{
        .schema_version = schema,
        .proof_profile = profile,
        .source_sha256 = digest(source_bytes),
        .canonical_ir_sha256 = plan.canonical_ir_sha256,
        .bundle_sha256 = bundle_digest,
        .native_template_sha256 = template_digest,
        .preprocessed_root = facts.preprocessed_root,
        .calls = calls,
        .public_outputs = public_outputs,
        .public_word_count = public_word_count,
        .pcs = fixed_pcs,
        .max_component_trace_log_size = max_trace_log,
        .components = components,
        .claimed_sums = @intCast(components.len),
        .total_constraints = constraint_end,
        .main_columns = main_end,
        .interaction_columns = interaction_end,
    } };
}

/// Source-derived equality is a consistency check for the plan-only artifact.
/// CircuitFacts remain caller supplied; this does not admit a proof or key.
/// Rehashing altered metadata cannot make it equal to the regenerated plan.
pub fn matchesSource(
    allocator: std.mem.Allocator,
    candidate: Manifest,
    source_bytes: []const u8,
    air_bundle_bytes: []const u8,
    facts: CircuitFacts,
) !bool {
    var expected = try fromSource(allocator, source_bytes, air_bundle_bytes, facts);
    defer expected.deinit();
    const left = try std.json.Stringify.valueAlloc(allocator, candidate, .{});
    defer allocator.free(left);
    const right = try std.json.Stringify.valueAlloc(allocator, expected.value, .{});
    defer allocator.free(right);
    return std.mem.eql(u8, left, right);
}

/// Typed, length-delimited V4 commitment. This is an audit digest only; no
/// current native transcript or verification key admits this schema.
pub fn precommitmentDigest(value: Manifest) Digest {
    var h = Sha256.init(.{});
    h.update("S31-BOUNDED-COMPONENT-MANIFEST-V4\x00");
    hashBytes(&h, value.schema_version);
    hashBytes(&h, value.proof_profile);
    h.update(&value.source_sha256);
    h.update(&value.canonical_ir_sha256);
    h.update(&value.bundle_sha256);
    h.update(&value.native_template_sha256);
    h.update(&value.preprocessed_root);
    hashInt(&h, @as(u32, @intCast(value.calls.len)));
    for (value.calls) |call| {
        hashInt(&h, call.call_id);
        hashInt(&h, call.source_node_id);
        hashInt(&h, call.input_node_id);
        hashInt(&h, call.rounds);
        hashInt(&h, call.constant);
        if (call.endpoints) |endpoints| {
            hashInt(&h, @as(u8, 1));
            for (endpoints.input) |address| hashInt(&h, address);
            for (endpoints.output) |address| hashInt(&h, address);
        } else hashInt(&h, @as(u8, 0));
    }
    hashInt(&h, @as(u32, @intCast(value.public_outputs.len)));
    for (value.public_outputs) |output| {
        hashBytes(&h, output.name);
        hashInt(&h, output.canonical_node_id);
        hashInt(&h, @as(u8, @intFromEnum(output.kind)));
        hashInt(&h, output.length);
        hashInt(&h, output.word_offset);
    }
    hashInt(&h, value.public_word_count);
    hashInt(&h, value.pcs.pow_bits);
    hashInt(&h, value.pcs.log_blowup_factor);
    hashInt(&h, value.pcs.last_layer_degree_bound);
    hashInt(&h, value.pcs.queries);
    hashInt(&h, value.pcs.fold_step);
    hashInt(&h, value.max_component_trace_log_size);
    hashInt(&h, @as(u32, @intCast(value.components.len)));
    for (value.components) |component| {
        hashInt(&h, @as(u8, @intFromEnum(component.role)));
        if (component.call_id) |id| {
            hashInt(&h, @as(u8, 1));
            hashInt(&h, id);
        } else hashInt(&h, @as(u8, 0));
        switch (component.source) {
            .bundled_air => |source| {
                hashInt(&h, @as(u8, 0));
                hashInt(&h, source.index);
                h.update(&source.bundle_sha256);
                h.update(&source.selected_program_sha256);
            },
            .native_air => |source| {
                hashInt(&h, @as(u8, 1));
                hashInt(&h, @as(u8, @intFromEnum(source.kind)));
                h.update(&source.program_binding_sha256);
            },
        }
        hashInt(&h, component.proof_index);
        hashInt(&h, component.claimed_sum_index);
        hashInt(&h, component.trace_log_size);
        hashInt(&h, component.evaluation_log_size);
        hashSpan(&h, component.main);
        hashSpan(&h, component.interaction);
        hashInt(&h, component.n_constraints);
        hashInt(&h, component.random_coefficient_offset);
        hashInt(&h, @as(u32, @intCast(component.preprocessed_indices.len)));
        for (component.preprocessed_indices) |index| hashInt(&h, index);
        hashInt(&h, @as(u32, @intCast(component.lookup_relation_ids.len)));
        for (component.lookup_relation_ids) |id| hashInt(&h, id);
    }
    hashInt(&h, value.claimed_sums);
    hashInt(&h, value.total_constraints);
    hashInt(&h, value.main_columns);
    hashInt(&h, value.interaction_columns);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn nativeTemplateDigest() Digest {
    var h = Sha256.init(.{});
    h.update("S31-BOUNDED-NATIVE-AIR-TEMPLATE-V4\x00");
    inline for (.{
        @embedFile("s31_pair_boundary_source"),
        @embedFile("s31_many_boundary_source"),
        @embedFile("s31_many_direct_circuit_source"),
        @embedFile("s31_tagged_pair_chip_air_source"),
        @embedFile("s31_tagged_pair_bridge_air_source"),
    }) |source| hashBytes(&h, source);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn nativeProgramDigest(kind: NativeKind, schedule: Digest, call: admission.Call) Digest {
    var h = Sha256.init(.{});
    h.update("S31-BOUNDED-NATIVE-COMPONENT-V4\x00");
    hashInt(&h, @as(u8, @intFromEnum(kind)));
    h.update(&schedule);
    switch (kind) {
        .tagged_chip => hashBytes(&h, @embedFile("s31_tagged_pair_chip_air_source")),
        .tagged_bridge => hashBytes(&h, @embedFile("s31_tagged_pair_bridge_air_source")),
    }
    hashInt(&h, call.call_id);
    hashInt(&h, call.source_node_id);
    hashInt(&h, call.input_node_id);
    hashInt(&h, call.rounds);
    hashInt(&h, call.constant);
    var result: Digest = undefined;
    h.final(&result);
    return result;
}

fn digest(bytes: []const u8) Digest {
    var result: Digest = undefined;
    Sha256.hash(bytes, &result, .{});
    return result;
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

fn hashBytes(h: *Sha256, bytes: []const u8) void {
    hashInt(h, @as(u64, @intCast(bytes.len)));
    h.update(bytes);
}

fn hashSpan(h: *Sha256, span: Span) void {
    hashInt(h, span.tree);
    hashInt(h, span.start);
    hashInt(h, span.end);
}

test "bounded V4 roster is 1+2N and uses disjoint checked intervals" {
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const facts: CircuitFacts = .{
        .trace_log_size = 5,
        .evaluation_log_size = 6,
        .main_columns = 12,
        .interaction_columns = 8,
        .preprocessed_indices = .{ 0, 2, 3, 1, 4, 5, 6, 7 },
        .n_constraints = 31,
        .selected_program_sha256 = digest("selected-air"),
        .preprocessed_root = digest("fixed-root"),
    };
    var generated = try fromSource(std.testing.allocator, source, "pinned-bundle", facts);
    defer generated.deinit();
    const value = generated.value;
    try std.testing.expectEqual(@as(usize, 5), value.components.len);
    try std.testing.expectEqual(@as(u32, 5), value.claimed_sums);
    try std.testing.expectEqual(@as(u32, 46), value.main_columns);
    try std.testing.expectEqual(@as(u32, 64), value.interaction_columns);
    try std.testing.expectEqual(@as(u32, 69), value.total_constraints);
    try std.testing.expectEqual(@as(u32, 8), value.public_word_count);
    try std.testing.expectEqual(@as(u32, 0), value.public_outputs[0].word_offset);
    try std.testing.expectEqual(@as(u32, 4), value.public_outputs[1].word_offset);
    try std.testing.expect(value.calls[0].endpoints == null);
    try std.testing.expectEqual(Role.circuit, value.components[0].role);
    try std.testing.expectEqual(Role.chip, value.components[1].role);
    try std.testing.expectEqual(Role.chip, value.components[2].role);
    try std.testing.expectEqual(Role.bridge, value.components[3].role);
    try std.testing.expectEqual(Role.bridge, value.components[4].role);
    try std.testing.expectEqual(@as(u32, 31), value.components[1].random_coefficient_offset);
    try std.testing.expectEqual(@as(u32, 43), value.components[3].random_coefficient_offset);
    try std.testing.expectEqual(@as(u32, 56), value.components[4].random_coefficient_offset);
    try std.testing.expect(try matchesSource(std.testing.allocator, value, source, "pinned-bundle", facts));
}

test "bounded V4 rejects rehashed roster, source, native identity and geometry mutations" {
    const a = std.testing.allocator;
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const facts: CircuitFacts = .{
        .trace_log_size = 5,
        .evaluation_log_size = 6,
        .main_columns = 12,
        .interaction_columns = 8,
        .preprocessed_indices = .{ 0, 2, 3, 1, 4, 5, 6, 7 },
        .n_constraints = 31,
        .selected_program_sha256 = digest("selected-air"),
        .preprocessed_root = digest("fixed-root"),
    };
    var generated = try fromSource(a, source, "pinned-bundle", facts);
    defer generated.deinit();
    var altered = generated.value;
    const components = try a.dupe(Component, altered.components);
    defer a.free(components);
    altered.components = components;
    const calls = try a.dupe(Call, altered.calls);
    defer a.free(calls);
    altered.calls = calls;
    const original_digest = precommitmentDigest(generated.value);
    components[1].proof_index = 2;
    const changed_digest = precommitmentDigest(altered);
    try std.testing.expect(!std.mem.eql(u8, &original_digest, &changed_digest));
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[1] = generated.value.components[1];
    components[3].main.start += 1;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[3] = generated.value.components[3];
    components[3].lookup_relation_ids = &.{pair.relation_id};
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[3] = generated.value.components[3];
    components[1].source.native_air.program_binding_sha256[0] ^= 1;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[1] = generated.value.components[1];
    components[1].source = .{ .bundled_air = .{
        .index = 1,
        .bundle_sha256 = generated.value.bundle_sha256,
        .selected_program_sha256 = facts.selected_program_sha256,
    } };
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[1] = generated.value.components[1];
    components[4].random_coefficient_offset += 1;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    components[4] = generated.value.components[4];
    const outputs = try a.dupe(PublicOutput, altered.public_outputs);
    defer a.free(outputs);
    altered.public_outputs = outputs;
    outputs[1].length = 3;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    outputs[1] = generated.value.public_outputs[1];
    outputs[1].name = "other";
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    outputs[1] = generated.value.public_outputs[1];
    calls[1].call_id = 0;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    calls[1] = generated.value.calls[1];
    calls[0].endpoints = .{ .input = [_]u32{3} ** 4, .output = [_]u32{4} ** 4 };
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    calls[0] = generated.value.calls[0];
    altered.claimed_sums = 4;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    altered.claimed_sums = generated.value.claimed_sums;
    altered.source_sha256[0] ^= 1;
    try std.testing.expect(!try matchesSource(a, altered, source, "pinned-bundle", facts));
    try std.testing.expect(!try matchesSource(a, generated.value, source, "changed-bundle", facts));
    var changed_facts = facts;
    changed_facts.selected_program_sha256[0] ^= 1;
    try std.testing.expect(!try matchesSource(a, generated.value, source, "pinned-bundle", changed_facts));
    changed_facts = facts;
    changed_facts.preprocessed_indices[1] = changed_facts.preprocessed_indices[0];
    try std.testing.expectError(error.InvalidBoundedPreprocessedIndex, fromSource(a, source, "pinned-bundle", changed_facts));
}

test "bounded V4 fails closed on coefficient overflow" {
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const facts: CircuitFacts = .{
        .trace_log_size = 5,
        .evaluation_log_size = 6,
        .main_columns = 12,
        .interaction_columns = 8,
        .preprocessed_indices = .{ 0, 2, 3, 1, 4, 5, 6, 7 },
        .n_constraints = std.math.maxInt(u32) - 1,
        .selected_program_sha256 = digest("selected-air"),
        .preprocessed_root = digest("fixed-root"),
    };
    try std.testing.expectError(error.Overflow, fromSource(std.testing.allocator, source, "bundle", facts));
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

test "bounded V4 supports one and eight calls with exact output shape" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var steps = [_]relation.Step{ .{ .op = .square }, .{ .op = .add_const, .constant = 13 } };
    const facts: CircuitFacts = .{
        .trace_log_size = 5,
        .evaluation_log_size = 6,
        .main_columns = 12,
        .interaction_columns = 8,
        .preprocessed_indices = .{ 0, 2, 3, 1, 4, 5, 6, 7 },
        .n_constraints = 31,
        .selected_program_sha256 = digest("selected-air"),
        .preprocessed_root = digest("fixed-root"),
    };
    for ([_]usize{ 1, 8 }) |n| {
        const program = try chainProgram(a, n, &steps);
        const plan = try admission.extract(a, program);
        var ir = try canonical.build(a, program);
        defer ir.deinit();
        var generated = try fromPlan(a, "source-for-test", "bundle", facts, &plan, &ir);
        defer generated.deinit();
        const value = generated.value;
        try std.testing.expectEqual(1 + 2 * n, value.components.len);
        try std.testing.expectEqual(@as(u32, @intCast(value.components.len)), value.claimed_sums);
        try std.testing.expectEqual(@as(u32, @intCast(12 + n * 17)), value.main_columns);
        try std.testing.expectEqual(@as(u32, @intCast(8 + n * 28)), value.interaction_columns);
        try std.testing.expectEqual(@as(u32, @intCast(31 + n * 19)), value.total_constraints);
        try std.testing.expectEqual(@as(u32, 1), value.public_word_count);
        try std.testing.expectEqual(@as(u32, 1), value.public_outputs[0].length);
        for (value.components, 0..) |component, id| {
            try std.testing.expectEqual(@as(u32, @intCast(id)), component.proof_index);
            try std.testing.expectEqual(@as(u32, @intCast(id)), component.claimed_sum_index);
        }
        try std.testing.expectEqual(@as(u32, 0), value.components[0].main.start);
        try std.testing.expectEqual(value.main_columns, value.components[value.components.len - 1].main.end);
        try std.testing.expectEqual(value.interaction_columns, value.components[value.components.len - 1].interaction.end);
    }
}
