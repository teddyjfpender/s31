//! Experimental source-pinned N=4 mixed pair/many native proof envelope.
//!
//! The verifier rebuilds the selected source, component and PCS schedule
//! before bounded postcard decoding. `private` means language visibility;
//! these base traces do not provide witness confidentiality.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("interop_postcard");
const relation = @import("../../language/relation.zig");
const binding = @import("../bounded_compiled_binding.zig");
const mixed = @import("inspection.zig");
const descriptor = @import("descriptor.zig");
const engine = cpu.experimental_direct_mixed_four_arithmetic;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const magic = "S31MIX06";
const fixed_header_len = magic.len + 1 + 1 + 2 + 32 + 32 + 32 + 8;
const max_wire_bytes: usize = 16 << 20;

fn headerLen(sum_count: usize) usize {
    return fixed_header_len + 16 * sum_count;
}

fn publicValues(words: [8]u32) ![8]QM31 {
    var result: [8]QM31 = undefined;
    for (words, &result) |word, *value| {
        if (word >= core.fields.m31.Modulus) return error.InvalidMixedPublicStatement;
        value.* = QM31.fromBase(M31.fromCanonical(word));
    }
    return result;
}

fn selectedFromSource(source: *const mixed.SelectedSchedule) !engine.Selected {
    if (source.call_count != engine.n_calls or source.slot_count != engine.n_components)
        return error.UnsupportedMixedProofCount;
    var plan: cpu.private_many_boundary.Plan = .{ .count = source.call_count };
    for (source.calls[0..source.call_count], plan.calls[0..source.call_count]) |call, *slot| {
        if (call.constant >= core.fields.m31.Modulus) return error.InvalidMixedSource;
        slot.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    return .{
        .source_sha256 = source.source_sha256,
        .manifest_sha256 = source.digest,
        .fixed_root = source.fixed_root,
        .circuit_program_sha256 = source.slots[0].program_binding_sha256,
        .plan = plan,
        .geometry = source.native_geometry orelse return error.InvalidMixedSource,
    };
}

/// The same source-derived profile identity used by proveSealed and
/// verifyEmbedded. This is an audit view, never a caller-supplied verifier key.
pub const Inspection = struct {
    schedule: mixed.SelectedSchedule,
    circuit_identity_sha256: [32]u8,
};

pub const Sealed = struct {
    bytes: []u8,
    inspection: Inspection,
};

pub fn inspectProfile(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) !Inspection {
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    return .{ .schedule = schedule, .circuit_identity_sha256 = selected.circuitIdentity() };
}

/// Build the distinct N=4 envelope. Only the regenerated source schedule may
/// nominate component order and manifest digest. Use a concurrency-safe
/// allocator because native composition workers allocate concurrently.
pub fn proveSealed(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    assignment: relation.Assignment,
) ![]u8 {
    return (try proveSealedAndInspect(allocator, source, air_bytes, assignment)).bytes;
}

/// Produce the proof and the exact rebuilt identity used in its header.
/// The caller owns `bytes`; `inspection` contains no allocated slices.
pub fn proveSealedAndInspect(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    assignment: relation.Assignment,
) !Sealed {
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment);
    const expected_public = try publicValues(words);
    const topology = try binding.compileSourceTopology(allocator, source);
    var witness = try binding.compileManyWitness(allocator, source, assignment, topology);
    defer witness.deinit();
    var proof = try engine.proveSourceBound(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit),
        witness.values(),
        source,
        air_bytes,
        &selected,
    );
    defer proof.deinit();
    const identity = selected.circuitIdentity();
    if (proof.sum_count != engine.n_components or proof.output_values.len != 8 or
        !std.meta.eql(proof.circuit_hash, identity))
        return error.InvalidMixedProofIdentity;
    for (proof.output_values, &expected_public) |actual, expected|
        if (!actual.eql(expected)) return error.InvalidMixedPublicStatement;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, magic);
    try bytes.append(allocator, engine.n_calls);
    try bytes.append(allocator, @intCast(proof.sum_count));
    try bytes.appendSlice(allocator, &.{ 2, 0 });
    try bytes.appendSlice(allocator, &selected.source_sha256);
    try bytes.appendSlice(allocator, &selected.manifest_sha256);
    try bytes.appendSlice(allocator, &identity);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    for (proof.claimed_sums[0..proof.sum_count]) |sum| for (sum.toM31Array()) |limb| {
        var word: [4]u8 = undefined;
        std.mem.writeInt(u32, &word, limb.toU32(), .little);
        try bytes.appendSlice(allocator, &word);
    };
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    if (bytes.items.len > max_wire_bytes) return error.InvalidMixedNativeEnvelope;
    return .{
        .bytes = try bytes.toOwnedSlice(allocator),
        .inspection = .{ .schedule = schedule, .circuit_identity_sha256 = identity },
    };
}

/// Compiled-in source and AIR are the verifier's authority. This is the only
/// public proof-byte verifier entrypoint for the experimental mixed profile.
pub fn verifyEmbedded(
    comptime source: []const u8,
    comptime air_bytes: []const u8,
    allocator: std.mem.Allocator,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    _ = try verifySourceBound(allocator, source, air_bytes, public_words, raw);
}

/// Verified audit identity for a caller that also needs to check a saved
/// statement. Source and official AIR remain compile-time embedded authority.
pub fn verifyEmbeddedAndInspect(
    comptime source: []const u8,
    comptime air_bytes: []const u8,
    allocator: std.mem.Allocator,
    public_words: [8]u32,
    raw: []const u8,
) !Inspection {
    return verifySourceBound(allocator, source, air_bytes, public_words, raw);
}

/// Admit a supplied component descriptor only after reconstructing it from
/// compiled-in source. This accepts only the fixed N=4 profile.
pub fn verifyEmbeddedWithDescriptor(
    comptime source: []const u8,
    comptime air_bytes: []const u8,
    allocator: std.mem.Allocator,
    candidate: *const descriptor.Descriptor,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    try descriptor.requireSource(allocator, candidate, source, air_bytes);
    if (candidate.call_count != engine.n_calls) return error.UnsupportedMixedProofCount;
    _ = try verifySourceBound(allocator, source, air_bytes, public_words, raw);
}

fn verifySourceBound(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    public_words: [8]u32,
    raw: []const u8,
) !Inspection {
    if (raw.len < fixed_header_len or raw.len > max_wire_bytes or
        !std.mem.eql(u8, raw[0..magic.len], magic) or
        raw[magic.len] != engine.n_calls or raw[magic.len + 1] != engine.n_components or
        raw[magic.len + 2] != 2 or raw[magic.len + 3] != 0 or
        raw.len < headerLen(engine.n_components))
        return error.InvalidMixedNativeEnvelope;
    // This full source/handle/PCS reconstruction precedes proof allocation.
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    const identity = selected.circuitIdentity();
    var at: usize = magic.len + 4;
    if (!std.mem.eql(u8, raw[at..][0..32], &selected.source_sha256)) return error.InvalidMixedNativeEnvelope;
    at += 32;
    if (!std.mem.eql(u8, raw[at..][0..32], &selected.manifest_sha256)) return error.InvalidMixedNativeEnvelope;
    at += 32;
    if (!std.mem.eql(u8, raw[at..][0..32], &identity)) return error.InvalidMixedNativeEnvelope;
    at += 32;
    const nonce = std.mem.readInt(u64, raw[at..][0..8], .little);
    at += 8;
    const outputs = try publicValues(public_words);
    var sums = [_]QM31{QM31.zero()} ** cpu.private_many_boundary.max_components;
    for (sums[0..engine.n_components]) |*sum| {
        var limbs: [4]u32 = undefined;
        for (&limbs) |*limb| {
            limb.* = std.mem.readInt(u32, raw[at..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidMixedNativeEnvelope;
            at += 4;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    if (at != headerLen(engine.n_components)) return error.InvalidMixedNativeEnvelope;
    const topology = try binding.compileSourceTopology(allocator, source);
    var compiled = try binding.compileManyTopology(allocator, source, topology);
    defer compiled.deinit();
    const geometry = selected.geometry;
    const pcs = geometry.pcs;
    var sample_width_limits: [4]u32 = .{ 0, 0, 0, 1 };
    for (geometry.tree_columns[0..3], 0..) |width, tree| {
        for (geometry.columns[tree][0..width]) |column|
            sample_width_limits[tree] = @max(sample_width_limits[tree], column.mask_width);
    }
    try postcard.proof_preflight.validateFor(4, raw[at..], .{
        .config = .{
            .pow_bits = pcs.fri_config.pow_bits,
            .log_blowup_factor = pcs.fri_config.log_blowup_factor,
            .n_queries = pcs.fri_config.n_queries,
            .log_last_layer_degree_bound = pcs.fri_config.log_last_layer_degree_bound,
            .fold_step = pcs.fri_config.fold_step,
            .lifting_log_size = null,
        },
        .tree_columns = geometry.tree_columns,
        .max_column_log_size = geometry.max_column_log_size,
        .sample_width_limits = sample_width_limits,
        .hash_size = @sizeOf(H.Hash),
        .max_wire_bytes = max_wire_bytes - at,
    });
    const decode_limit = @min(@as(usize, 64 << 20), @max(@as(usize, 8 << 20), raw.len * 32));
    const decode_memory = try allocator.alloc(u8, decode_limit);
    defer allocator.free(decode_memory);
    var bounded = std.heap.FixedBufferAllocator.init(decode_memory);
    var stream = std.io.fixedBufferStream(raw[at..]);
    var stark = try postcard.deserializeProof(H, bounded.allocator(), stream.reader());
    defer stark.deinit(bounded.allocator());
    if (stream.pos != raw.len - at) return error.InvalidMixedNativeEnvelope;
    try engine.verifySourceBoundBorrowed(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&compiled.circuit),
        source,
        air_bytes,
        &selected,
        public_words,
        .{
            .output_values = &outputs,
            .interaction_pow_nonce = nonce,
            .claimed_sums = sums,
            .sum_count = engine.n_components,
            .stark_proof = &stark,
            .circuit_hash = identity,
        },
    );
    return .{ .schedule = schedule, .circuit_identity_sha256 = identity };
}

test "mixed sealed N4 native proof authenticates nine interleaved claims" {
    const allocator = std.heap.smp_allocator;
    const source = @embedFile("../../examples/boundary/mixed_four.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    const assignment_bytes = @embedFile("../../examples/boundary/mixed_four.valid.json");
    const expected_words = [8]u32{ 2094051178, 181768886, 881143857, 2099579072, 1987186231, 908844405, 1873039656, 1620533201 };
    var assignment = try relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment.value);
    try std.testing.expectEqualDeep(expected_words, words);
    var timer = try std.time.Timer.start();
    const sealed = try proveSealedAndInspect(allocator, source, air_bytes, assignment.value);
    defer allocator.free(sealed.bytes);
    var proof_digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(sealed.bytes, &proof_digest, .{});
    const proof_hex = std.fmt.bytesToHex(proof_digest, .lower);
    try std.testing.expectEqualStrings("408ff6a32b9374ea92a8a086ffc4b2ef0114749a2f9b2a09b4e5adb9b849aade", &proof_hex);
    try std.testing.expectEqual(@as(usize, 110_020), sealed.bytes.len);
    const prove_ns = timer.read();
    timer.reset();
    const verified = try verifyEmbeddedAndInspect(source, air_bytes, allocator, words, sealed.bytes);
    const verify_ns = timer.read();
    try std.testing.expectEqual(@as(u8, 4), verified.schedule.call_count);
    try std.testing.expectEqual(@as(usize, 9), verified.schedule.slot_count);
    try std.testing.expectEqual(@as(u32, 80), verified.schedule.main_columns);
    try std.testing.expectEqual(@as(u32, 120), verified.schedule.interaction_columns);
    try std.testing.expectEqualDeep(sealed.inspection.circuit_identity_sha256, verified.circuit_identity_sha256);
    std.debug.print("mixed N4 sealed proof: bytes={d} prove_ms={d} verify_ms={d} main_cols=80 interaction_cols=120 components=9\n", .{ sealed.bytes.len, prove_ns / std.time.ns_per_ms, verify_ns / std.time.ns_per_ms });

    const changed = try allocator.dupe(u8, sealed.bytes);
    defer allocator.free(changed);
    for (0..engine.n_components) |index| {
        @memcpy(changed, sealed.bytes);
        changed[fixed_header_len + 16 * index] ^= 1;
        if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| return error.AcceptedChangedN4Sum else |_| {}
    }
    @memcpy(changed, sealed.bytes);
    const left_at = fixed_header_len + 16 * 7;
    const right_at = fixed_header_len + 16 * 8;
    const p = core.fields.m31.Modulus;
    const left = std.mem.readInt(u32, changed[left_at..][0..4], .little);
    const right = std.mem.readInt(u32, changed[right_at..][0..4], .little);
    std.mem.writeInt(u32, changed[left_at..][0..4], if (left + 1 == p) 0 else left + 1, .little);
    std.mem.writeInt(u32, changed[right_at..][0..4], if (right == 0) p - 1 else right - 1, .little);
    if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| return error.AcceptedCompensatedN4Sums else |_| {}
    @memcpy(changed, sealed.bytes);
    changed[0] ^= 1;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, sealed.bytes);
    changed[magic.len] = 3;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, sealed.bytes);
    changed[magic.len + 1] = 7;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, sealed.bytes);
    changed[magic.len + 2] = 1;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    for ([_]usize{ magic.len + 4, magic.len + 36, magic.len + 68 }) |offset| {
        @memcpy(changed, sealed.bytes);
        changed[offset] ^= 1;
        try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    }
    var bad_words = words;
    bad_words[0] ^= 1;
    if (verifySourceBound(allocator, source, air_bytes, bad_words, sealed.bytes)) |_| return error.AcceptedChangedN4PublicOutput else |_| {}
    const trailing = try allocator.alloc(u8, sealed.bytes.len + 1);
    defer allocator.free(trailing);
    @memcpy(trailing[0..sealed.bytes.len], sealed.bytes);
    trailing[sealed.bytes.len] = 0;
    if (verifySourceBound(allocator, source, air_bytes, words, trailing)) |_| return error.AcceptedTrailingN4ProofByte else |_| {}

    const changed_source = try std.mem.replaceOwned(u8, allocator, source, "\"constant\": 16", "\"constant\": 17");
    defer allocator.free(changed_source);
    try std.testing.expect(!std.mem.eql(u8, source, changed_source));
    const changed_schedule = try mixed.inspectSource(allocator, changed_source, air_bytes);
    const changed_selected = try selectedFromSource(&changed_schedule);
    @memcpy(changed, sealed.bytes);
    @memcpy(changed[magic.len + 4 ..][0..32], &changed_selected.source_sha256);
    @memcpy(changed[magic.len + 36 ..][0..32], &changed_selected.manifest_sha256);
    const changed_identity = changed_selected.circuitIdentity();
    @memcpy(changed[magic.len + 68 ..][0..32], &changed_identity);
    if (verifySourceBound(allocator, changed_source, air_bytes, words, changed)) |_| return error.AcceptedResealedN4Source else |_| {}

    const source_descriptor = try descriptor.fromSource(allocator, source, air_bytes);
    try verifyEmbeddedWithDescriptor(source, air_bytes, allocator, &source_descriptor, words, sealed.bytes);
    var changed_descriptor = source_descriptor;
    std.mem.swap(@import("../component_descriptor_contract.zig").Source, &changed_descriptor.entries[7].source, &changed_descriptor.entries[8].source);
    changed_descriptor.digest = try @import("../component_descriptor_contract.zig").digest(changed_descriptor.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, verifyEmbeddedWithDescriptor(source, air_bytes, allocator, &changed_descriptor, words, sealed.bytes));
    const n3 = @import("package.zig");
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, n3.verifyEmbedded(source, air_bytes, allocator, words, sealed.bytes));
    const n3_source = @embedFile("../../examples/boundary/private_mixed3.s31.json");
    const n3_assignment_bytes = @embedFile("../../examples/boundary/private_mixed3.valid.json");
    var n3_assignment = try relation.parseAssignment(allocator, n3_assignment_bytes);
    defer n3_assignment.deinit();
    const n3_raw = try n3.proveSealed(allocator, n3_source, air_bytes, n3_assignment.value);
    defer allocator.free(n3_raw);
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, n3_raw));
}
