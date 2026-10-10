//! Experimental source-pinned V4 proof bytes for bounded 1..8-call S31.
//!
//! The verifier entrypoint embeds source and official AIR at compile time.
//! Source admission, typed manifest, live AIR/PCS preflight and public output
//! checks run before bounded postcard decoding. This is a transparent proof
//! profile: `private` is a language visibility marker, not witness secrecy.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("interop_postcard");
const relation = @import("../language/relation.zig");
const binding = @import("bounded_compiled_binding.zig");
const engine = cpu.experimental_direct_many_arithmetic;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const magic = "S31MNY04";
const fixed_header_len = magic.len + 1 + 1 + 2 + 32 + 32 + 32 + 8;
const max_wire_bytes: usize = 16 << 20;

fn headerLen(sum_count: usize) usize {
    return fixed_header_len + 16 * sum_count;
}

fn publicValues(words: [8]u32) ![8]QM31 {
    var result: [8]QM31 = undefined;
    for (words, &result) |word, *value| {
        if (word >= core.fields.m31.Modulus) return error.InvalidManyPublicStatement;
        value.* = QM31.fromBase(M31.fromCanonical(word));
    }
    return result;
}

/// Construct a canonical V4 envelope from an admitted source and witness.
/// The caller must use a concurrency-safe allocator for native AIR workers.
pub fn proveSealed(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    assignment: relation.Assignment,
) ![]u8 {
    var inspected = try binding.inspectMany(allocator, source, air_bytes);
    defer inspected.deinit();
    const identity = inspected.selected_schedule.circuitIdentity();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment);
    const public_values = try publicValues(words);
    var witness = try binding.compileManyWitness(allocator, source, assignment, inspected.topology);
    defer witness.deinit();
    var air = try engine.parseBundle(allocator, air_bytes);
    defer air.deinit();
    var proof = try engine.proveSelected(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit),
        witness.values(),
        &air,
        &inspected.selected_schedule,
    );
    defer proof.deinit();
    if (proof.sum_count != inspected.selected_schedule.geometry.live.count or
        proof.output_values.len != public_values.len or
        !std.meta.eql(proof.circuit_hash, identity))
        return error.InvalidManyProofIdentity;
    for (proof.output_values, &public_values) |actual, expected|
        if (!actual.eql(expected)) return error.InvalidManyPublicStatement;

    var bytes: std.ArrayList(u8) = .empty;
    errdefer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, magic);
    try bytes.append(allocator, inspected.selected_schedule.geometry.call_count);
    try bytes.append(allocator, @intCast(proof.sum_count));
    try bytes.appendSlice(allocator, &.{ 0, 0 });
    try bytes.appendSlice(allocator, &inspected.selected_schedule.geometry.source_digest);
    try bytes.appendSlice(allocator, &inspected.selected_schedule.manifest_digest);
    try bytes.appendSlice(allocator, &identity);
    var nonce: [8]u8 = undefined;
    std.mem.writeInt(u64, &nonce, proof.interaction_pow_nonce, .little);
    try bytes.appendSlice(allocator, &nonce);
    for (proof.claimed_sums[0..proof.sum_count]) |sum| {
        for (sum.toM31Array()) |limb| {
            var word: [4]u8 = undefined;
            std.mem.writeInt(u32, &word, limb.toU32(), .little);
            try bytes.appendSlice(allocator, &word);
        }
    }
    try postcard.serializeProof(H, bytes.writer(allocator), proof.stark_proof.proof);
    if (bytes.items.len > max_wire_bytes) return error.InvalidManyNativeEnvelope;
    return bytes.toOwnedSlice(allocator);
}

/// Compile-time source and AIR are the verifier's authority. No caller may
/// supply a different source, manifest, PCS profile, or component roster.
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
        !std.mem.eql(u8, raw[0..magic.len], magic))
        return error.InvalidManyNativeEnvelope;
    const n_calls = raw[magic.len];
    const sum_count = raw[magic.len + 1];
    if (n_calls == 0 or n_calls > cpu.private_many_boundary.max_calls or
        sum_count != 1 + 2 * @as(usize, n_calls) or
        raw[magic.len + 2] != 0 or raw[magic.len + 3] != 0 or
        raw.len < headerLen(sum_count))
        return error.InvalidManyNativeEnvelope;
    var inspected = try binding.inspectMany(allocator, source, air_bytes);
    defer inspected.deinit();
    const identity = inspected.selected_schedule.circuitIdentity();
    if (inspected.selected_schedule.geometry.call_count != n_calls or
        inspected.selected_schedule.geometry.slot_count != sum_count or
        inspected.selected_schedule.geometry.live.count != sum_count)
        return error.InvalidManyNativeEnvelope;
    var at: usize = magic.len + 4;
    if (!std.mem.eql(u8, raw[at..][0..32], &inspected.selected_schedule.geometry.source_digest))
        return error.InvalidManyNativeEnvelope;
    at += 32;
    if (!std.mem.eql(u8, raw[at..][0..32], &inspected.selected_schedule.manifest_digest))
        return error.InvalidManyNativeEnvelope;
    at += 32;
    if (!std.mem.eql(u8, raw[at..][0..32], &identity))
        return error.InvalidManyNativeEnvelope;
    at += 32;
    const nonce = std.mem.readInt(u64, raw[at..][0..8], .little);
    at += 8;
    const outputs = try publicValues(public_words);
    var sums = [_]QM31{QM31.zero()} ** cpu.private_many_boundary.max_components;
    for (sums[0..sum_count]) |*sum| {
        var limbs: [4]u32 = undefined;
        for (&limbs) |*limb| {
            limb.* = std.mem.readInt(u32, raw[at..][0..4], .little);
            if (limb.* >= core.fields.m31.Modulus) return error.InvalidManyNativeEnvelope;
            at += 4;
        }
        sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    if (at != headerLen(sum_count)) return error.InvalidManyNativeEnvelope;
    var topology = try binding.compileManyTopology(allocator, source, inspected.topology);
    defer topology.deinit();
    var air = try engine.parseBundle(allocator, air_bytes);
    defer air.deinit();
    const pcs = inspected.selected_schedule.geometry.live.pcs;
    const geometry = inspected.selected_schedule.geometry.live;
    // The roster and PCS shape are derived before any proof allocation.
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
        .sample_width_limits = geometry.sample_width_limits,
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
    if (stream.pos != raw.len - at) return error.InvalidManyNativeEnvelope;
    try engine.verifySelectedBorrowed(
        allocator,
        circuit.common.preprocessed.CircuitView.fromBuilder(&topology.circuit),
        &air,
        &inspected.selected_schedule,
        public_words,
        .{
            .output_values = &outputs,
            .interaction_pow_nonce = nonce,
            .claimed_sums = sums,
            .sum_count = sum_count,
            .stark_proof = &stark,
            .circuit_hash = identity,
        },
    );
}

test "bounded sealed V4 many one-call envelope verifies and rejects canonical header mutations" {
    const allocator = std.heap.smp_allocator;
    const source = @embedFile("../examples/boundary/private_many1.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    var assignment = try relation.parseAssignment(allocator, @embedFile("../examples/boundary/private_many1.valid.json"));
    defer assignment.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment.value);
    const raw = try proveSealed(allocator, source, air_bytes, assignment.value);
    defer allocator.free(raw);
    try std.testing.expectEqual(@as(u8, 1), raw[magic.len]);
    try std.testing.expectEqual(@as(u8, 3), raw[magic.len + 1]);
    try verifyEmbedded(source, air_bytes, allocator, words, raw);
    var changed_words = words;
    changed_words[0] += 1;
    if (verifyEmbedded(source, air_bytes, allocator, changed_words, raw)) |_| return error.AcceptedChangedPublicStatement else |_| {}
    const changed_source = source ++ " ";
    try std.testing.expectError(error.InvalidManyNativeEnvelope, verifyEmbedded(changed_source, air_bytes, allocator, words, raw));

    const changed = try allocator.dupe(u8, raw);
    defer allocator.free(changed);
    for ([_]usize{ 0, magic.len, magic.len + 1, magic.len + 2, magic.len + 4, magic.len + 36, magic.len + 68 }) |index| {
        @memcpy(changed, raw);
        changed[index] ^= 1;
        try std.testing.expectError(error.InvalidManyNativeEnvelope, verifyEmbedded(source, air_bytes, allocator, words, changed));
    }
    for (0..3) |sum_index| {
        @memcpy(changed, raw);
        const index = fixed_header_len + 16 * sum_index;
        changed[index] ^= 1;
        if (verifyEmbedded(source, air_bytes, allocator, words, changed)) |_| return error.AcceptedChangedClaimedSum else |_| {}
    }
    @memcpy(changed, raw);
    std.mem.writeInt(u32, changed[fixed_header_len..][0..4], core.fields.m31.Modulus, .little);
    try std.testing.expectError(error.InvalidManyNativeEnvelope, verifyEmbedded(source, air_bytes, allocator, words, changed));
    try std.testing.expectError(error.InvalidManyNativeEnvelope, verifyEmbedded(source, air_bytes, allocator, words, raw[0..fixed_header_len]));
    const with_trailing = try std.mem.concat(allocator, u8, &.{ raw, &.{0} });
    defer allocator.free(with_trailing);
    if (verifyEmbedded(source, air_bytes, allocator, words, with_trailing)) |_| return error.AcceptedTrailingProofByte else |_| {}
    // The postcard decoder permits overlong LEB128, so shape preflight must
    // reject an alternate encoding of its first length before allocating.
    const proof_at = headerLen(3);
    try std.testing.expectEqual(@as(u8, 26), raw[proof_at]);
    const overlong = try allocator.alloc(u8, raw.len + 1);
    defer allocator.free(overlong);
    @memcpy(overlong[0..proof_at], raw[0..proof_at]);
    overlong[proof_at] = 0x9a;
    overlong[proof_at + 1] = 0;
    @memcpy(overlong[proof_at + 2 ..], raw[proof_at + 1 ..]);
    try std.testing.expectError(error.NonCanonicalVarint, verifyEmbedded(source, air_bytes, allocator, words, overlong));
}

test "V4 native count matrix proves 2 through 8 calls and rejects each claimed sum mutation" {
    const allocator = std.heap.smp_allocator;
    const air_bytes = @embedFile("s31_air_programs");
    // This oracle uses ordinary u64 modular arithmetic, independently of
    // S31 relation evaluation and the engine's M31 field implementation.
    const p: u64 = 2147483647;
    const initial = [4]u64{ 3, 5, 7, 11 };
    const pinned_5_to_7 = [3][8]u32{
        .{ 489847162, 58371116, 422257245, 1460185845, 1469541477, 291855555, 808317019, 1029658645 },
        .{ 1901382382, 2115332761, 496715432, 1820666583, 1409179843, 1986729192, 1329524328, 699979469 },
        .{ 1890162284, 1349810231, 481975622, 711744516, 1375519549, 306600189, 1226345658, 1386738614 },
    };
    for ([_]usize{ 2, 3, 4, 5, 6, 7, 8 }) |n| {
        var source_list: std.ArrayList(u8) = .empty;
        defer source_list.deinit(allocator);
        try source_list.appendSlice(allocator,
            \\{"version":1,"name":"many_matrix","inputs":[{"name":"x","kind":"m31","length":4,"visibility":"private"}],"nodes":[
        );
        var final = initial;
        for (0..n) |id| {
            const previous = if (id == 0) "x" else try std.fmt.allocPrint(allocator, "r{d}", .{id - 1});
            defer if (id != 0) allocator.free(previous);
            const node = try std.fmt.allocPrint(
                allocator,
                "{{\"name\":\"r{d}\",\"op\":\"repeat\",\"lhs\":\"{s}\",\"rounds\":16,\"body\":[{{\"op\":\"square\"}},{{\"op\":\"add_const\",\"constant\":{d}}}]}},",
                .{ id, previous, 13 + id },
            );
            defer allocator.free(node);
            try source_list.appendSlice(allocator, node);
            const constant: u64 = 13 + id;
            for (&final) |*value| for (0..16) |_| {
                value.* = (value.* * value.* + constant) % p;
            };
        }
        const suffix = try std.fmt.allocPrint(
            allocator,
            "{{\"name\":\"sum\",\"op\":\"add\",\"lhs\":\"r{d}\",\"rhs\":\"x\"}},{{\"name\":\"product\",\"op\":\"mul\",\"lhs\":\"r{d}\",\"rhs\":\"x\"}}],\"assertions\":[],\"public_outputs\":[\"sum\",\"product\"]}}",
            .{ n - 1, n - 1 },
        );
        defer allocator.free(suffix);
        try source_list.appendSlice(allocator, suffix);
        const source = source_list.items;
        var sums: [4]u32 = undefined;
        var products: [4]u32 = undefined;
        for (0..4) |lane| {
            sums[lane] = @intCast((final[lane] + initial[lane]) % p);
            products[lane] = @intCast((final[lane] * initial[lane]) % p);
        }
        const assignment_json = try std.fmt.allocPrint(
            allocator,
            "{{\"public_inputs\":{{}},\"private_inputs\":{{\"x\":[3,5,7,11]}},\"public_outputs\":{{\"sum\":[{d},{d},{d},{d}],\"product\":[{d},{d},{d},{d}]}}}}",
            .{ sums[0], sums[1], sums[2], sums[3], products[0], products[1], products[2], products[3] },
        );
        defer allocator.free(assignment_json);
        var assignment = try relation.parseAssignment(allocator, assignment_json);
        defer assignment.deinit();
        const words = sums ++ products;
        if (n >= 5 and n <= 7)
            try std.testing.expectEqualSlices(u32, &pinned_5_to_7[n - 5], &words);
        const raw = try proveSealed(allocator, source, air_bytes, assignment.value);
        defer allocator.free(raw);
        try std.testing.expectEqual(@as(u8, @intCast(n)), raw[magic.len]);
        try std.testing.expectEqual(@as(u8, @intCast(1 + 2 * n)), raw[magic.len + 1]);
        try verifySourceBound(allocator, source, air_bytes, words, raw);
        const changed = try allocator.dupe(u8, raw);
        defer allocator.free(changed);
        for (0..1 + 2 * n) |sum_index| {
            @memcpy(changed, raw);
            changed[fixed_header_len + 16 * sum_index] ^= 1;
            if (verifySourceBound(allocator, source, air_bytes, words, changed)) |_| return error.AcceptedChangedClaimedSum else |_| {}
        }
    }
}

test "bounded sealed V4 rejects resealed reordered calls and endpoint addresses" {
    const allocator = std.heap.smp_allocator;
    const source = @embedFile("../examples/boundary/private_pair16_32.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    var assignment = try relation.parseAssignment(allocator, @embedFile("../examples/boundary/private_pair16_32.valid.json"));
    defer assignment.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const words = try relation.evaluate(allocator, parsed.value, assignment.value);
    const raw = try proveSealed(allocator, source, air_bytes, assignment.value);
    defer allocator.free(raw);
    try verifySourceBound(allocator, source, air_bytes, words, raw);
    var original = try binding.inspectMany(allocator, source, air_bytes);
    defer original.deinit();
    const reordered =
        \\{"version":1,"name":"private_pair16_32","inputs":[{"name":"left","kind":"m31","length":4,"visibility":"private"},{"name":"right","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"right_final","op":"repeat","lhs":"right","rounds":32,"body":[{"op":"square"},{"op":"add_const","constant":17}]},{"name":"left_final","op":"repeat","lhs":"left","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},{"name":"sum","op":"add","lhs":"left_final","rhs":"right_final"},{"name":"product","op":"mul","lhs":"left_final","rhs":"right_final"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    const moved_endpoints =
        \\{"version":1,"name":"private_pair16_32","inputs":[{"name":"right","kind":"m31","length":4,"visibility":"private"},{"name":"left","kind":"m31","length":4,"visibility":"private"}],"nodes":[{"name":"left_final","op":"repeat","lhs":"left","rounds":16,"body":[{"op":"square"},{"op":"add_const","constant":13}]},{"name":"right_final","op":"repeat","lhs":"right","rounds":32,"body":[{"op":"square"},{"op":"add_const","constant":17}]},{"name":"sum","op":"add","lhs":"left_final","rhs":"right_final"},{"name":"product","op":"mul","lhs":"left_final","rhs":"right_final"}],"assertions":[],"public_outputs":["sum","product"]}
    ;
    for ([_][]const u8{ reordered, moved_endpoints }, 0..) |changed_source, case_index| {
        var changed_binding = try binding.inspectMany(allocator, changed_source, air_bytes);
        defer changed_binding.deinit();
        if (case_index == 0) {
            try std.testing.expect(original.topology.calls[0].constant != changed_binding.topology.calls[0].constant);
        } else {
            try std.testing.expect(!std.meta.eql(original.topology.calls[0].input, changed_binding.topology.calls[0].input));
        }
        const resealed = try allocator.dupe(u8, raw);
        defer allocator.free(resealed);
        @memcpy(resealed[magic.len + 4 ..][0..32], &changed_binding.topology.source_sha256);
        @memcpy(resealed[magic.len + 36 ..][0..32], &changed_binding.manifest_precommitment);
        @memcpy(resealed[magic.len + 68 ..][0..32], &changed_binding.circuit_identity);
        if (verifySourceBound(allocator, changed_source, air_bytes, words, resealed)) |_| return error.AcceptedResealedWrongSource else |_| {}
    }
}
