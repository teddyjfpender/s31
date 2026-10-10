//! Source-owned admission for the experimental two-call direct chip profile.
//! This module does not enable a pair proof or accept proof bytes. It gives a
//! future prover and native verifier the same witness-free Plan, preprocessed
//! root and typed V3 manifest precommitment from the sealed source alone.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const relation = @import("../language/relation.zig");
const compiler = @import("../language/relation_compiler.zig");
const canonical = @import("../language/canonical.zig");
const manifest = @import("component_manifest.zig");

const PairPlan = cpu.private_pair_boundary.Plan;
const Sha256 = std.crypto.hash.sha2.Sha256;

pub const Binding = struct {
    plan: PairPlan,
    generated: manifest.PairGenerated,
    source_digest: [32]u8,
    ir_digest: [32]u8,
    preprocessed_root: [32]u8,
    trace_log_size: u32,
    precommitment_digest: [32]u8,
    effective_digest: [32]u8,

    pub fn deinit(self: *Binding) void {
        self.generated.deinit();
        self.* = undefined;
    }
};

/// `air_bytes` must be the same pinned official bundle embedded in the
/// released S31 runtime; directPair checks its pinned SHA256. `blowup` is
/// supplied by the selected, source-sealed PCS profile.
pub fn derive(allocator: std.mem.Allocator, source_bytes: []const u8, air_bytes: []const u8, blowup: u32) !Binding {
    if (blowup != 1) return error.UnsupportedPairPcsProfile;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    if (parsed.value.privateRepeatedStepPair() == null) return error.UnsupportedPairRelation;
    var ir = try canonical.build(allocator, parsed.value);
    defer ir.deinit();
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectPairWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &maps);
    defer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    const plan = maps.private_pair_plan orelse return error.MissingPairPlan;
    var pp = try plan.preprocessed(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit));
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, blowup);
    var source_digest: [32]u8 = undefined;
    Sha256.hash(source_bytes, &source_digest, .{});
    var generated = try manifest.directPair(allocator, &pp, plan, air_bytes, source_digest, ir.sha256, root, [_]u8{0} ** 32);
    errdefer generated.deinit();
    const precommitment = manifest.pairPrecommitmentDigest(generated.value);
    const effective = cpu.private_pair_boundary.effectiveDigest(source_digest, precommitment);
    return .{
        .plan = plan,
        .generated = generated,
        .source_digest = source_digest,
        .ir_digest = ir.sha256,
        .preprocessed_root = root,
        .trace_log_size = pp.traceLogSize(),
        .precommitment_digest = precommitment,
        .effective_digest = effective,
    };
}

/// Reconstruct the precommitment from sealed source. This checks every typed
/// manifest field and the canonical Plan even if an attacker has recomputed
/// a self-consistent digest for a different in-memory manifest. The native
/// proof verifier will call this before accepting a V3 pair key or envelope.
pub fn verifySourceBinding(allocator: std.mem.Allocator, source_bytes: []const u8, air_bytes: []const u8, expected: *const Binding) !void {
    var rebuilt = try derive(allocator, source_bytes, air_bytes, 1);
    defer rebuilt.deinit();
    // The circuit hash is intentionally outside the manifest precommitment.
    // The sealed proof verifier must recompute and check it separately after
    // this source-only check and before parsing or accepting proof bytes.
    var expected_manifest = expected.generated.value;
    expected_manifest.circuit_hash = "";
    var rebuilt_manifest = rebuilt.generated.value;
    rebuilt_manifest.circuit_hash = "";
    if (!std.meta.eql(expected.plan, rebuilt.plan) or
        !std.mem.eql(u8, &expected.source_digest, &rebuilt.source_digest) or
        !std.mem.eql(u8, &expected.ir_digest, &rebuilt.ir_digest) or
        !std.mem.eql(u8, &expected.preprocessed_root, &rebuilt.preprocessed_root) or
        expected.trace_log_size != rebuilt.trace_log_size or
        !std.mem.eql(u8, &expected.precommitment_digest, &rebuilt.precommitment_digest) or
        !std.mem.eql(u8, &expected.effective_digest, &rebuilt.effective_digest) or
        !(try manifest.matchesPair(allocator, expected_manifest, rebuilt_manifest)))
        return error.PairSourceBindingMismatch;
}

/// Recompile the source-owned circuit for native verification. This returns
/// no witness values and refuses a topology or pair Plan different from the
/// fully reconstructed binding.
pub fn compileTopology(allocator: std.mem.Allocator, source_bytes: []const u8, expected: *const Binding) !circuit.builder.Context(circuit.builder.NoValue) {
    var digest: [32]u8 = undefined;
    Sha256.hash(source_bytes, &digest, .{});
    if (!std.mem.eql(u8, &digest, &expected.source_digest)) return error.PairSourceMismatch;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    if (parsed.value.privateRepeatedStepPair() == null) return error.UnsupportedPairRelation;
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectPairWithSpans(circuit.builder.NoValue, allocator, parsed.value, null, &maps);
    errdefer ctx.deinit();
    try padDirect(allocator, circuit.builder.NoValue, &ctx);
    const plan = maps.private_pair_plan orelse return error.MissingPairPlan;
    if (!std.meta.eql(plan, expected.plan)) return error.PairPlanMismatch;
    var pp = try plan.preprocessed(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit));
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.mem.eql(u8, &root, &expected.preprocessed_root) or pp.traceLogSize() != expected.trace_log_size)
        return error.PairTopologyMismatch;
    return ctx;
}

pub const Witness = struct {
    context: circuit.builder.Context(core.fields.qm31.QM31),
    plan: PairPlan,

    pub fn deinit(self: *Witness) void {
        self.context.deinit();
        self.* = undefined;
    }
};

/// Compile witness values only after deriving the source binding. A forged
/// pair plan is rejected even if a caller could reseal its manifest digest.
pub fn compileWitness(allocator: std.mem.Allocator, source_bytes: []const u8, assignment: relation.Assignment, expected: *const Binding) !Witness {
    var digest: [32]u8 = undefined;
    Sha256.hash(source_bytes, &digest, .{});
    if (!std.mem.eql(u8, &digest, &expected.source_digest)) return error.PairSourceMismatch;
    var parsed = try relation.parseProgram(allocator, source_bytes);
    defer parsed.deinit();
    if (parsed.value.privateRepeatedStepPair() == null) return error.UnsupportedPairRelation;
    var maps = compiler.Maps{};
    defer maps.deinit(allocator);
    var ctx = try compiler.compileDirectPairWithSpans(core.fields.qm31.QM31, allocator, parsed.value, assignment, &maps);
    errdefer ctx.deinit();
    try padDirect(allocator, core.fields.qm31.QM31, &ctx);
    const plan = maps.private_pair_plan orelse return error.MissingPairPlan;
    if (!std.meta.eql(plan, expected.plan)) return error.PairPlanMismatch;
    var pp = try plan.preprocessed(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit));
    defer pp.deinit(allocator);
    const root = try pp.preprocessedRoot(allocator, 1);
    if (!std.mem.eql(u8, &root, &expected.preprocessed_root)) return error.PairTopologyMismatch;
    return .{ .context = ctx, .plan = plan };
}

fn padDirect(allocator: std.mem.Allocator, comptime V: type, ctx: *circuit.builder.Context(V)) !void {
    const raw = circuit.common.finalize.rawComponentSizes(circuit.common.preprocessed.CircuitView.fromBuilder(&ctx.circuit));
    if (raw.eq != 0 or raw.triple_xor != 0 or raw.m31_to_u32 != 0 or raw.blake_g_gate != 0)
        return error.UnsupportedPairCircuit;
    try circuit.common.finalize.padToTargets(V, ctx, .{
        .eq = 0,
        .qm31_ops = circuit.common.finalize.paddedSize(raw.qm31_ops),
        .m31_to_u32 = 0,
        .triple_xor = 0,
        .blake_g_gate = 0,
    });
    if (try ctx.circuit.firstYieldViolation(allocator) != null)
        return error.InvalidPairYieldTopology;
}
