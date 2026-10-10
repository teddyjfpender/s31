//! Experimental sealed two-call package. It is intentionally absent from the
//! S31 CLI and public frontend facade until byte-level native tests pass.
//! Source/Plan/manifest/key checks precede proof-envelope decoding.
const std = @import("std");
const core = @import("stwo_core");
const cpu = @import("stwo_circuit_cpu_integration");
const circuit = @import("stwo_circuit_frontend");
const pair_engine = @import("s31_pair_engine");
const postcard = @import("interop_postcard");
const relation = @import("../language/relation.zig");
const source_binding = @import("pair_source_binding.zig");
const manifest = @import("component_manifest.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const magic = "S31NAT8P";
const sum_count = cpu.private_pair_boundary.roster.len;
const header_len = magic.len + 8 + sum_count * 16;

pub const Key = struct {
    schema: []const u8,
    profile: []const u8,
    program_sha256: []const u8,
    canonical_ir_sha256: []const u8,
    preprocessed_root: []const u8,
    circuit_hash: []const u8,
    manifest_precommitment_sha256: []const u8,
    trace_log_size: u32,
    fri: struct {
        pow_bits: u32,
        log_blowup_factor: u32,
        last_layer_degree_bound: u32,
        queries: u32,
        fold_step: u32,
    },
    component_manifest: manifest.PairManifest,
};

fn pcsFor(binding: *const source_binding.Binding) !core.pcs.config_v2.PcsConfigV2 {
    const chip_log = @max(@as(u32, @intCast(@ctz(binding.plan.calls[0].rounds))), @as(u32, @intCast(@ctz(binding.plan.calls[1].rounds))));
    const fri = try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
    var pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndTraceSize(fri, @max(binding.trace_log_size, chip_log));
    pcs.preprocessed_lifting_log_size = binding.trace_log_size + fri.log_blowup_factor;
    return pcs;
}

fn circuitHash(binding: *const source_binding.Binding, pcs: core.pcs.config_v2.PcsConfigV2) [32]u8 {
    return pair_engine.identityHash(binding.effective_digest, binding.preprocessed_root, binding.trace_log_size, pcs.fri_config.log_blowup_factor, enginePlan(binding));
}

fn enginePlan(binding: *const source_binding.Binding) pair_engine.Plan {
    var plan: pair_engine.Plan = .{ .calls = undefined };
    for (binding.plan.calls, &plan.calls) |call, *converted| converted.* = .{
        .call_id = call.call_id,
        .rounds = call.rounds,
        .constant = call.constant,
        .input = call.input,
        .output = call.output,
    };
    return plan;
}

fn keyBytes(allocator: std.mem.Allocator, binding: *source_binding.Binding, pcs: core.pcs.config_v2.PcsConfigV2) ![]u8 {
    const hash = circuitHash(binding, pcs);
    try manifest.setPairCircuitHash(&binding.generated, hash);
    const source_hex = std.fmt.bytesToHex(binding.source_digest, .lower);
    const ir_hex = std.fmt.bytesToHex(binding.ir_digest, .lower);
    const root_hex = std.fmt.bytesToHex(binding.preprocessed_root, .lower);
    const hash_hex = std.fmt.bytesToHex(hash, .lower);
    const precommit_hex = std.fmt.bytesToHex(binding.precommitment_digest, .lower);
    const key: Key = .{
        .schema = "s31-verification-key-direct-pair-v1",
        .profile = "direct-m31-private-pair-v1",
        .program_sha256 = &source_hex,
        .canonical_ir_sha256 = &ir_hex,
        .preprocessed_root = &root_hex,
        .circuit_hash = &hash_hex,
        .manifest_precommitment_sha256 = &precommit_hex,
        .trace_log_size = binding.trace_log_size,
        .fri = .{
            .pow_bits = 26,
            .log_blowup_factor = 1,
            .last_layer_degree_bound = 1,
            .queries = 70,
            .fold_step = 1,
        },
        .component_manifest = binding.generated.value,
    };
    return std.json.Stringify.valueAlloc(allocator, key, .{});
}

/// Build the exact source-derived key bytes. A deployed verifier embeds
/// these bytes and its normalized source, as the existing one-call runtime
/// does; a caller cannot supply an alternate key with the same hash field.
pub fn sealKey(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) ![]u8 {
    var binding = try source_binding.derive(allocator, source, air_bytes, 1);
    defer binding.deinit();
    try source_binding.verifySourceBinding(allocator, source, air_bytes, &binding);
    return keyBytes(allocator, &binding, try pcsFor(&binding));
}

fn checkKey(allocator: std.mem.Allocator, binding: *source_binding.Binding, pcs: core.pcs.config_v2.PcsConfigV2, sealed_key: []const u8) !void {
    const reconstructed = try keyBytes(allocator, binding, pcs);
    defer allocator.free(reconstructed);
    if (!std.mem.eql(u8, sealed_key, reconstructed)) return error.InvalidPairVerificationKey;
}

fn engineRequest(binding: *const source_binding.Binding) pair_engine.Request {
    return .{
        .source_digest = binding.source_digest,
        .manifest_digest = binding.precommitment_digest,
        .plan = enginePlan(binding),
    };
}

fn publicValues(words: [8]u32) ![8]QM31 {
    var result: [8]QM31 = undefined;
    for (words, &result) |word, *value| {
        if (word >= core.fields.m31.Modulus) return error.NoncanonicalPairPublicWord;
        value.* = QM31.fromBase(M31.fromCanonical(word));
    }
    return result;
}

/// Prove only after source and exact key-byte validation. The returned bytes
/// have a fixed V3 header followed by one canonical postcard STARK proof.
pub fn proveSealed(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8, sealed_key: []const u8, assignment: relation.Assignment) ![]u8 {
    var binding = try source_binding.derive(allocator, source, air_bytes, 1);
    defer binding.deinit();
    try source_binding.verifySourceBinding(allocator, source, air_bytes, &binding);
    const pcs = try pcsFor(&binding);
    try checkKey(allocator, &binding, pcs, sealed_key);
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment);
    const expected_outputs = try publicValues(words);
    var witness = try source_binding.compileWitness(allocator, source, assignment, &binding);
    defer witness.deinit();
    var air = try pair_engine.parseBundle(allocator, air_bytes);
    defer air.deinit();
    var proof = try pair_engine.prove(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&witness.context.circuit), witness.context.values(), &air, pcs, engineRequest(&binding));
    defer proof.deinit();
    const expected_hash = circuitHash(&binding, pcs);
    if (!std.mem.eql(u8, &proof.circuit_hash, &expected_hash) or
        proof.output_values.len != expected_outputs.len)
        return error.InvalidPairProofIdentity;
    for (proof.output_values, &expected_outputs) |actual, expected|
        if (!actual.eql(expected)) return error.InvalidPairPublicStatement;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, magic);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    for (proof.claimed_sums) |sum| {
        for (sum.toM31Array()) |limb| {
            var word: [4]u8 = undefined;
            std.mem.writeInt(u32, &word, limb.toU32(), .little);
            try bytes.appendSlice(allocator, &word);
        }
    }
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    return bytes.toOwnedSlice(allocator);
}

/// The source-derived typed manifest and byte-exact key are checked before
/// inspecting `raw`. This is a host STARK verification path, not an evaluator
/// that recomputes the claimed result from private input.
pub fn verifySealed(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8, sealed_key: []const u8, public_words: [8]u32, raw: []const u8) !void {
    var binding = try source_binding.derive(allocator, source, air_bytes, 1);
    defer binding.deinit();
    try source_binding.verifySourceBinding(allocator, source, air_bytes, &binding);
    const pcs = try pcsFor(&binding);
    try checkKey(allocator, &binding, pcs, sealed_key);
    const outputs = try publicValues(public_words);
    var topology = try source_binding.compileTopology(allocator, source, &binding);
    defer topology.deinit();
    if (raw.len < header_len or raw.len > (16 << 20) or !std.mem.eql(u8, raw[0..magic.len], magic))
        return error.InvalidPairNativeEnvelope;
    const nonce = std.mem.readInt(u64, raw[magic.len..][0..8], .little);
    var sums: [sum_count]QM31 = undefined;
    for (&sums, 0..) |*sum, index| {
        const at = magic.len + 8 + index * 16;
        var limbs: [4]u32 = undefined;
        for (&limbs, 0..) |*limb, part| {
            limb.* = std.mem.readInt(u32, raw[at + part * 4 ..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidPairNativeEnvelope;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    const decode_memory = try allocator.alloc(u8, 64 << 20);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(raw[header_len..]);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != raw.len - header_len) return error.InvalidPairNativeEnvelope;
    var air = try pair_engine.parseBundle(allocator, air_bytes);
    defer air.deinit();
    try pair_engine.verifyBorrowed(allocator, circuit.common.preprocessed.CircuitView.fromBuilder(&topology.circuit), &air, pcs, engineRequest(&binding), public_words, .{
        .output_values = &outputs,
        .interaction_pow_nonce = nonce,
        .claimed_sums = sums,
        .stark_proof = &stark,
        .circuit_hash = circuitHash(&binding, pcs),
    });
}
