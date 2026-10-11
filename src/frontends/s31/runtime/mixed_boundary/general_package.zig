//! Experimental source-pinned one-to-eight-call mixed native proof envelope.
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
const registry_manifest = @import("registry_manifest.zig");
const engine = cpu.experimental_direct_mixed_general_arithmetic;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const magic = "S31MIX07";
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
    if (source.call_count == 0 or source.call_count > engine.max_calls or
        source.slot_count != 1 + 2 * @as(usize, source.call_count))
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
    const typed_manifest = try registry_manifest.fromSchedule(source);
    return .{
        .source_sha256 = source.source_sha256,
        .manifest_sha256 = typed_manifest.digest,
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
    registry_manifest_sha256: [32]u8,
    circuit_identity_sha256: [32]u8,
};

pub const Sealed = struct {
    bytes: []u8,
    inspection: Inspection,
    stages: ProveStages,
};

pub const NativeTiming = engine.Timing;

/// Monotonic wall-clock intervals inside the source-pinned mixed package.
/// The ordinary API measures the whole native prove including setup.
pub const ProveStages = struct {
    profile_rebuild_ns: u64,
    semantic_evaluation_ns: u64,
    topology_compile_ns: u64,
    witness_compile_ns: u64,
    native_prove_including_setup_ns: u64,
    envelope_and_serialization_ns: u64,
    package_total_ns: u64,
};

pub fn inspectProfile(allocator: std.mem.Allocator, source: []const u8, air_bytes: []const u8) !Inspection {
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    return .{ .schedule = schedule, .registry_manifest_sha256 = selected.manifest_sha256, .circuit_identity_sha256 = selected.circuitIdentity() };
}

/// Build the distinct bounded mixed envelope. Only the regenerated source schedule may
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
    return proveSealedAndInspectWithTiming(allocator, source, air_bytes, assignment, null);
}

/// Optional timing goes only to the caller; it is absent from proof bytes,
/// statement bytes, manifest, source identity, and verifier inputs.
pub fn proveSealedAndInspectWithTiming(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    assignment: relation.Assignment,
    native_timing: ?*NativeTiming,
) !Sealed {
    var timer = try std.time.Timer.start();
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    const profile_end = timer.read();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment);
    const expected_public = try publicValues(words);
    const semantic_end = timer.read();
    const topology = try binding.compileSourceTopology(allocator, source);
    const topology_end = timer.read();
    var witness = try binding.compileManyWitness(allocator, source, assignment, topology);
    defer witness.deinit();
    const witness_end = timer.read();
    var proof = try engine.proveSourceBoundWithTiming(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit),
        witness.values(),
        source,
        air_bytes,
        &selected,
        native_timing,
    );
    defer proof.deinit();
    const native_end = timer.read();
    const identity = selected.circuitIdentity();
    if (proof.sum_count != schedule.slot_count or proof.output_values.len != 8 or
        !std.meta.eql(proof.circuit_hash, identity))
        return error.InvalidMixedProofIdentity;
    for (proof.output_values, &expected_public) |actual, expected|
        if (!actual.eql(expected)) return error.InvalidMixedPublicStatement;
    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, magic);
    try bytes.append(allocator, schedule.call_count);
    try bytes.append(allocator, @intCast(proof.sum_count));
    try bytes.appendSlice(allocator, &.{ 3, 0 });
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
    const owned = try bytes.toOwnedSlice(allocator);
    const envelope_end = timer.read();
    return .{
        .bytes = owned,
        .inspection = .{ .schedule = schedule, .registry_manifest_sha256 = selected.manifest_sha256, .circuit_identity_sha256 = identity },
        .stages = .{
            .profile_rebuild_ns = profile_end,
            .semantic_evaluation_ns = semantic_end - profile_end,
            .topology_compile_ns = topology_end - semantic_end,
            .witness_compile_ns = witness_end - topology_end,
            .native_prove_including_setup_ns = native_end - witness_end,
            .envelope_and_serialization_ns = envelope_end - native_end,
            .package_total_ns = envelope_end,
        },
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
/// compiled-in source. This accepts only the source-derived bounded general profile.
pub fn verifyEmbeddedWithDescriptor(
    comptime source: []const u8,
    comptime air_bytes: []const u8,
    allocator: std.mem.Allocator,
    candidate: *const descriptor.Descriptor,
    public_words: [8]u32,
    raw: []const u8,
) !void {
    try descriptor.requireSource(allocator, candidate, source, air_bytes);
    if (candidate.call_count == 0 or candidate.call_count > engine.max_calls) return error.UnsupportedMixedProofCount;
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
        raw[magic.len] == 0 or raw[magic.len] > engine.max_calls or
        raw[magic.len + 1] != 1 + 2 * @as(usize, raw[magic.len]) or
        raw[magic.len + 2] != 3 or raw[magic.len + 3] != 0 or
        raw.len < headerLen(raw[magic.len + 1]))
        return error.InvalidMixedNativeEnvelope;
    // This full source/handle/PCS reconstruction precedes proof allocation.
    const schedule = try mixed.inspectSource(allocator, source, air_bytes);
    const selected = try selectedFromSource(&schedule);
    if (raw[magic.len] != schedule.call_count or raw[magic.len + 1] != schedule.slot_count)
        return error.InvalidMixedNativeEnvelope;
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
    for (sums[0..schedule.slot_count]) |*sum| {
        var limbs: [4]u32 = undefined;
        for (&limbs) |*limb| {
            limb.* = std.mem.readInt(u32, raw[at..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidMixedNativeEnvelope;
            at += 4;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    if (at != headerLen(schedule.slot_count)) return error.InvalidMixedNativeEnvelope;
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
            .sum_count = schedule.slot_count,
            .stark_proof = &stark,
            .circuit_hash = identity,
        },
    );
    return .{ .schedule = schedule, .registry_manifest_sha256 = selected.manifest_sha256, .circuit_identity_sha256 = identity };
}

test "mixed general sealed native proofs authenticate one through eight source calls" {
    const allocator = std.heap.smp_allocator;
    const air_bytes = @embedFile("s31_air_programs");
    const family = @import("test_source.zig");
    inline for (1..engine.max_calls + 1) |n| {
        const source = comptime family.forCount(n);
        const initial = [4]M31{ M31.fromCanonical(1), M31.fromCanonical(2), M31.fromCanonical(3), M31.fromCanonical(4) };
        var final = initial;
        for (0..n) |id| {
            const constant = M31.fromCanonical(@intCast(13 + id));
            for (0..16) |_| {
                for (&final) |*value| {
                    value.* = value.*.mul(value.*).add(constant);
                }
            }
        }
        var sum: [4]u32 = undefined;
        var product: [4]u32 = undefined;
        for (initial, final, &sum, &product) |start, end, *s, *p| {
            s.* = end.add(start).toU32();
            p.* = end.mul(start).toU32();
        }
        const assignment_bytes = try std.fmt.allocPrint(allocator, "{{\"public_inputs\":{{}},\"private_inputs\":{{\"x\":[1,2,3,4]}},\"public_outputs\":{{\"sum\":[{d},{d},{d},{d}],\"product\":[{d},{d},{d},{d}]}}}}", .{ sum[0], sum[1], sum[2], sum[3], product[0], product[1], product[2], product[3] });
        defer allocator.free(assignment_bytes);
        var assignment = try relation.parseAssignment(allocator, assignment_bytes);
        defer assignment.deinit();
        var program = try relation.parseProgram(allocator, source);
        defer program.deinit();
        const words = try relation.evaluate(allocator, program.value, assignment.value);
        try std.testing.expectEqualSlices(u32, &.{ sum[0], sum[1], sum[2], sum[3], product[0], product[1], product[2], product[3] }, &words);
        const sealed = try proveSealedAndInspect(allocator, source, air_bytes, assignment.value);
        defer allocator.free(sealed.bytes);
        try std.testing.expectEqual(@as(u8, n), sealed.inspection.schedule.call_count);
        try std.testing.expectEqual(@as(usize, 1 + 2 * n), sealed.inspection.schedule.slot_count);
        try std.testing.expectEqual(@as(u8, n), sealed.bytes[magic.len]);
        try std.testing.expectEqual(@as(u8, 1 + 2 * n), sealed.bytes[magic.len + 1]);
        try std.testing.expectEqual(@as(u8, 3), sealed.bytes[magic.len + 2]);
        const candidate = try descriptor.fromSource(allocator, source, air_bytes);
        try verifyEmbeddedWithDescriptor(source, air_bytes, allocator, &candidate, words, sealed.bytes);
        const checked = try verifyEmbeddedAndInspect(source, air_bytes, allocator, words, sealed.bytes);
        try std.testing.expectEqualDeep(sealed.inspection.registry_manifest_sha256, checked.registry_manifest_sha256);
        try std.testing.expectEqualDeep(sealed.inspection.circuit_identity_sha256, checked.circuit_identity_sha256);
        const changed = try allocator.dupe(u8, sealed.bytes);
        defer allocator.free(changed);
        changed[magic.len] = if (n == engine.max_calls) n - 1 else n + 1;
        try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
        @memcpy(changed, sealed.bytes);
        changed[magic.len + 1] ^= 2;
        try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
        @memcpy(changed, sealed.bytes);
        changed[magic.len + 36] ^= 1;
        try std.testing.expectError(error.InvalidMixedNativeEnvelope, verifySourceBound(allocator, source, air_bytes, words, changed));
        @memcpy(changed, sealed.bytes);
        changed[fixed_header_len] ^= 1;
        if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| {
            return error.AcceptedChangedGeneralMixedClaim;
        } else |_| {}
        var changed_words = words;
        changed_words[0] ^= 1;
        if (verifySourceBound(allocator, source, air_bytes, changed_words, sealed.bytes)) |_| {
            return error.AcceptedChangedGeneralMixedPublicWord;
        } else |_| {}
    }
}

test "mixed selected feeder native proof binds both private bit branches" {
    const allocator = std.heap.smp_allocator;
    const source = @embedFile("../../examples/boundary/private_selected_chip_feeder.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    const p: u64 = core.fields.m31.Modulus;
    const x = [4]u32{ 0, 1, core.fields.m31.Modulus - 1, 7 };
    const y = [4]u32{ 2, 3, 5, 11 };
    // Use plain widened integer arithmetic as an independent expected-value
    // oracle; this avoids sharing the prover's field helper implementation.
    var first = x;
    for (0..16) |_| {
        for (&first) |*word| word.* = @intCast((@as(u64, word.*) * word.* + 13) % p);
    }
    const profile = try inspectProfile(allocator, source, air_bytes);
    try std.testing.expectEqual(@as(u8, 2), profile.schedule.call_count);
    for (0..2) |bit| {
        var final: [4]u32 = undefined;
        var sums: [4]u32 = undefined;
        var products: [4]u32 = undefined;
        for (&final, x, y, first) |*word, left, right, computed| {
            word.* = @intCast((if (bit == 0)
                @as(u64, computed) + left
            else
                @as(u64, computed) * right) % p);
        }
        for (0..16) |_| {
            for (&final) |*word| word.* = @intCast((@as(u64, word.*) * word.* + 17) % p);
        }
        for (final, first, y, &sums, &products) |end, computed, right, *sum, *product| {
            sum.* = @intCast((@as(u64, end) + computed) % p);
            product.* = @intCast((@as(u64, end) * right) % p);
        }
        const assignment_bytes = try std.fmt.allocPrint(allocator, "{{\"public_inputs\":{{}},\"private_inputs\":{{\"x\":[0,1,{d},7],\"y\":[2,3,5,11],\"bit\":[{d}]}},\"public_outputs\":{{\"sum\":[{d},{d},{d},{d}],\"product\":[{d},{d},{d},{d}]}}}}", .{ core.fields.m31.Modulus - 1, bit, sums[0], sums[1], sums[2], sums[3], products[0], products[1], products[2], products[3] });
        defer allocator.free(assignment_bytes);
        var assignment = try relation.parseAssignment(allocator, assignment_bytes);
        defer assignment.deinit();
        var program = try relation.parseProgram(allocator, source);
        defer program.deinit();
        const words = try relation.evaluate(allocator, program.value, assignment.value);
        try std.testing.expectEqualSlices(u32, &.{ sums[0], sums[1], sums[2], sums[3], products[0], products[1], products[2], products[3] }, &words);
        const sealed = try proveSealedAndInspect(allocator, source, air_bytes, assignment.value);
        defer allocator.free(sealed.bytes);
        try verifyEmbedded(source, air_bytes, allocator, words, sealed.bytes);
        var changed_words = words;
        changed_words[0] = (changed_words[0] + 1) % core.fields.m31.Modulus;
        if (verifyEmbedded(source, air_bytes, allocator, changed_words, sealed.bytes)) |_| {
            return error.AcceptedChangedSelectedFeederClaim;
        } else |_| {}

        // The semantic evaluator rejects a non-bit before proof construction;
        // the direct circuit independently enforces b² = b on that input.
        if (bit == 0) {
            const invalid = try std.mem.replaceOwned(u8, allocator, assignment_bytes, "\"bit\":[0]", "\"bit\":[2]");
            defer allocator.free(invalid);
            var invalid_assignment = try relation.parseAssignment(allocator, invalid);
            defer invalid_assignment.deinit();
            try std.testing.expectError(error.InvalidSelector, proveSealedAndInspect(allocator, source, air_bytes, invalid_assignment.value));
        }
    }
}

test "mixed selected feeder native proof with two live selects sharing one private bit" {
    const allocator = std.heap.smp_allocator;
    const source = @embedFile("../../examples/boundary/private_two_selected_chip_feeder.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    const p: u64 = core.fields.m31.Modulus;
    const x = [4]u32{ 0, 1, core.fields.m31.Modulus - 1, 7 };
    const y = [4]u32{ 2, 3, 5, 11 };
    const profile = try inspectProfile(allocator, source, air_bytes);
    try std.testing.expectEqual(@as(u8, 2), profile.schedule.call_count);
    // The first select is the second chip's input. The second select remains
    // live because both public outputs consume it.
    try std.testing.expect(profile.schedule.calls[1].input[0] > profile.schedule.calls[0].output[0]);

    var first = x;
    for (0..16) |_| for (&first) |*word| {
        word.* = @intCast((@as(u64, word.*) * word.* + 13) % p);
    };
    var branch_words: [2][8]u32 = undefined;
    for (0..2) |bit| {
        var feed: [4]u32 = undefined;
        for (&feed, x, y, first) |*word, left, right, computed| {
            word.* = @intCast((if (bit == 0)
                @as(u64, computed) + left
            else
                @as(u64, computed) * right) % p);
        }
        var second = feed;
        for (0..16) |_| for (&second) |*word| {
            word.* = @intCast((@as(u64, word.*) * word.* + 17) % p);
        };
        var sum: [4]u32 = undefined;
        var product: [4]u32 = undefined;
        for (second, x, y, first, &sum, &product) |computed, left, right, a, *s, *m| {
            const chosen: u64 = if (bit == 0)
                @as(u64, computed) + right
            else
                @as(u64, computed) * left;
            const reduced = chosen % p;
            s.* = @intCast((reduced + a) % p);
            m.* = @intCast((reduced * computed) % p);
        }
        const expected = [8]u32{ sum[0], sum[1], sum[2], sum[3], product[0], product[1], product[2], product[3] };
        branch_words[bit] = expected;
        const assignment_bytes = try std.fmt.allocPrint(allocator, "{{\"public_inputs\":{{}},\"private_inputs\":{{\"x\":[0,1,{d},7],\"y\":[2,3,5,11],\"bit\":[{d}]}},\"public_outputs\":{{\"sum\":[{d},{d},{d},{d}],\"product\":[{d},{d},{d},{d}]}}}}", .{ core.fields.m31.Modulus - 1, bit, sum[0], sum[1], sum[2], sum[3], product[0], product[1], product[2], product[3] });
        defer allocator.free(assignment_bytes);
        var assignment = try relation.parseAssignment(allocator, assignment_bytes);
        defer assignment.deinit();
        var program = try relation.parseProgram(allocator, source);
        defer program.deinit();
        const words = try relation.evaluate(allocator, program.value, assignment.value);
        try std.testing.expectEqualSlices(u32, &expected, &words);
        const sealed = try proveSealedAndInspect(allocator, source, air_bytes, assignment.value);
        defer allocator.free(sealed.bytes);
        try verifyEmbedded(source, air_bytes, allocator, words, sealed.bytes);

        // Changing either selected public result must fail with the original proof.
        for ([_]usize{ 0, 4 }) |index| {
            var changed_words = words;
            changed_words[index] = (changed_words[index] + 1) % core.fields.m31.Modulus;
            if (verifyEmbedded(source, air_bytes, allocator, changed_words, sealed.bytes)) |_| {
                return error.AcceptedChangedTwoSelectPublicClaim;
            } else |_| {}
        }
        // A changed claimed sum in the envelope must not verify, even though
        // its public output words and source identity still match.
        const changed_proof = try allocator.dupe(u8, sealed.bytes);
        defer allocator.free(changed_proof);
        changed_proof[fixed_header_len] ^= 1;
        if (verifyEmbedded(source, air_bytes, allocator, words, changed_proof)) |_| {
            return error.AcceptedChangedTwoSelectProofClaim;
        } else |_| {}

        // Keep the original output claim while changing the private bit. The
        // semantic gate rejects the witness before any native proof is made.
        const flipped = try std.mem.replaceOwned(u8, allocator, assignment_bytes, if (bit == 0) "\"bit\":[0]" else "\"bit\":[1]", if (bit == 0) "\"bit\":[1]" else "\"bit\":[0]");
        defer allocator.free(flipped);
        var flipped_assignment = try relation.parseAssignment(allocator, flipped);
        defer flipped_assignment.deinit();
        try std.testing.expectError(error.PublicOutputMismatch, proveSealedAndInspect(allocator, source, air_bytes, flipped_assignment.value));
        const nonbit = try std.mem.replaceOwned(u8, allocator, assignment_bytes, if (bit == 0) "\"bit\":[0]" else "\"bit\":[1]", "\"bit\":[2]");
        defer allocator.free(nonbit);
        var nonbit_assignment = try relation.parseAssignment(allocator, nonbit);
        defer nonbit_assignment.deinit();
        try std.testing.expectError(error.InvalidSelector, proveSealedAndInspect(allocator, source, air_bytes, nonbit_assignment.value));
    }
    try std.testing.expect(!std.meta.eql(branch_words[0], branch_words[1]));
}
