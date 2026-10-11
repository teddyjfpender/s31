//! Experimental source-pinned N=3 mixed pair/many native proof envelope.
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
const mixed = @import("../experimental_mixed_admission.zig");
const engine = cpu.experimental_direct_mixed_arithmetic;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const magic = "S31MIX05";
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

/// Build the distinct V5 envelope. Only the regenerated source schedule may
/// nominate component order and manifest digest. Use a concurrency-safe
/// allocator because native composition workers allocate concurrently.
pub fn proveSealed(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    assignment: relation.Assignment,
) ![]u8 {
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
    try bytes.appendSlice(allocator, &.{ 1, 0 });
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
    return bytes.toOwnedSlice(allocator);
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
    return verifySourceBound(allocator, source, air_bytes, public_words, raw);
}

fn verifySourceBound(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    if (raw.len < fixed_header_len or raw.len > max_wire_bytes or
        !std.mem.eql(u8, raw[0..magic.len], magic) or
        raw[magic.len] != engine.n_calls or raw[magic.len + 1] != engine.n_components or
        raw[magic.len + 2] != 1 or raw[magic.len + 3] != 0 or
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
}

test "mixed sealed N3 native envelope authenticates source and interleaved claims" {
    const allocator = std.heap.smp_allocator;
    const source =
        \\{"version":1,"name":"mixed_three_independent","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[
        \\{"name":"r0","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},
        \\{"name":"r1","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":14}]},
        \\{"name":"r2","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":15}]},
        \\{"name":"s01","op":"add","lhs":"r0","rhs":"r1"},{"name":"sum","op":"add","lhs":"s01","rhs":"r2"},
        \\{"name":"product","op":"mul","lhs":"r2","rhs":"x"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    const reordered =
        \\{"version":1,"name":"mixed_three_independent","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[
        \\{"name":"r1","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":14}]},
        \\{"name":"r0","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},
        \\{"name":"r2","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":15}]},
        \\{"name":"s01","op":"add","lhs":"r0","rhs":"r1"},{"name":"sum","op":"add","lhs":"s01","rhs":"r2"},
        \\{"name":"product","op":"mul","lhs":"r2","rhs":"x"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    const changed_endpoint =
        \\{"version":1,"name":"mixed_three_independent","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[
        \\{"name":"r0","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},
        \\{"name":"r1","op":"repeat","lhs":"r0","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":14}]},
        \\{"name":"r2","op":"repeat","lhs":"x","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":15}]},
        \\{"name":"s01","op":"add","lhs":"r0","rhs":"r1"},{"name":"sum","op":"add","lhs":"s01","rhs":"r2"},
        \\{"name":"product","op":"mul","lhs":"r2","rhs":"x"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    const air_bytes = @embedFile("s31_air_programs");
    const assignment_json =
        \\{"public_inputs":{},"private_inputs":{"x":[3,5,7,11]},"public_outputs":{"sum":[407231026,1367407014,184053579,1379998342],"product":[1961760110,753190624,1655995629,300857602]}}
    ;
    var assignment = try relation.parseAssignment(allocator, assignment_json);
    defer assignment.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment.value);
    try std.testing.expectEqualSlices(u32, &.{ 407231026, 1367407014, 184053579, 1379998342, 1961760110, 753190624, 1655995629, 300857602 }, &words);
    var timer = try std.time.Timer.start();
    const raw = try proveSealed(allocator, source, air_bytes, assignment.value);
    defer allocator.free(raw);
    const prove_ns = timer.read();
    timer.reset();
    try verifyEmbedded(source, air_bytes, allocator, words, raw);
    const verify_ns = timer.read();
    std.debug.print("mixed N3 sealed proof: bytes={d} prove_ms={d} verify_ms={d} main_cols=63 interaction_cols=92 components=7\n", .{ raw.len, prove_ns / std.time.ns_per_ms, verify_ns / std.time.ns_per_ms });
    try std.testing.expectEqual(@as(u8, engine.n_calls), raw[magic.len]);
    try std.testing.expectEqual(@as(u8, engine.n_components), raw[magic.len + 1]);
    const changed = try allocator.dupe(u8, raw);
    defer allocator.free(changed);
    for (0..engine.n_components) |sum_index| {
        @memcpy(changed, raw);
        changed[fixed_header_len + 16 * sum_index] ^= 1;
        if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| return error.AcceptedChangedMixedSum else |_| {}
    }
    @memcpy(changed, raw);
    const left_at = fixed_header_len + 16;
    const right_at = fixed_header_len + 32;
    const p = core.fields.m31.Modulus;
    const left = std.mem.readInt(u32, changed[left_at..][0..4], .little);
    const right = std.mem.readInt(u32, changed[right_at..][0..4], .little);
    std.mem.writeInt(u32, changed[left_at..][0..4], if (left + 1 == p) 0 else left + 1, .little);
    std.mem.writeInt(u32, changed[right_at..][0..4], if (right == 0) p - 1 else right - 1, .little);
    if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| return error.AcceptedCompensatedMixedSums else |_| {}
    @memcpy(changed, raw);
    changed[0] ^= 1;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, raw);
    changed[magic.len + 1] = 8;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, raw);
    changed[magic.len + 2] = 0;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, raw);
    changed[magic.len + 4] ^= 1;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    @memcpy(changed, raw);
    changed[magic.len + 36] ^= 1;
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
    var wrong_words = words;
    wrong_words[0] ^= 1;
    if (verifySourceBound(allocator, source, air_bytes, wrong_words, raw)) |_| return error.AcceptedWrongMixedPublicStatement else |_| {}
    const trailing = try allocator.alloc(u8, raw.len + 1);
    defer allocator.free(trailing);
    @memcpy(trailing[0..raw.len], raw);
    trailing[raw.len] = 0;
    if (verifySourceBound(allocator, source, air_bytes, words, trailing)) |_| return error.AcceptedTrailingMixedProofByte else |_| {}
    for ([_][]const u8{ reordered, changed_endpoint }, 0..) |altered_source, case_index| {
        const alternate = try mixed.inspectSource(allocator, altered_source, air_bytes);
        const alternate_selected = try selectedFromSource(&alternate);
        if (case_index == 0) {
            try std.testing.expect(alternate.calls[0].constant != 13);
        } else {
            const original = try mixed.inspectSource(allocator, source, air_bytes);
            try std.testing.expect(!std.meta.eql(alternate.calls[1].input, original.calls[1].input));
        }
        @memcpy(changed, raw);
        @memcpy(changed[magic.len + 4 ..][0..32], &alternate_selected.source_sha256);
        @memcpy(changed[magic.len + 36 ..][0..32], &alternate_selected.manifest_sha256);
        const alternate_identity = alternate_selected.circuitIdentity();
        @memcpy(changed[magic.len + 68 ..][0..32], &alternate_identity);
        if (verifySourceBound(allocator, altered_source, air_bytes, words, changed)) |_| return error.AcceptedResealedMixedSource else |_| {}
    }
    const v4 = @import("../many_native_package.zig");
    const v4_raw = try v4.proveSealed(allocator, source, air_bytes, assignment.value);
    defer allocator.free(v4_raw);
    try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, v4_raw));
    try std.testing.expectError(error.InvalidManyNativeEnvelope, v4.verifyEmbedded(source, air_bytes, allocator, words, raw));
}
