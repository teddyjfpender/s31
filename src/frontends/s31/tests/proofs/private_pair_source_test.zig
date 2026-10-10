const std = @import("std");
const relation = @import("../../language/relation.zig");
const pair_source = @import("../../runtime/pair_source_binding.zig");
const native_pair = @import("../../runtime/pair_native_package.zig");
const manifest = @import("../../runtime/component_manifest.zig");
const pair = @import("stwo_circuit_cpu_integration").private_pair_boundary;
const pair_engine = @import("s31_pair_engine");

fn handRepeat(start: u32, constant: u32, rounds: u32) u32 {
    const modulus: u64 = 2147483647;
    var value: u64 = start;
    for (0..rounds) |_| value = (value * value + constant) % modulus;
    return @intCast(value);
}

test "sealed pair native proof accepts 16+32 and rejects key, claim, and envelope mutations" {
    const a = std.testing.allocator;
    const source = @embedFile("../../examples/boundary/private_pair16_32.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    var parsed = try relation.parseProgram(a, source);
    defer parsed.deinit();
    var assignment = try relation.parseAssignment(a, @embedFile("../../examples/boundary/private_pair16_32.valid.json"));
    defer assignment.deinit();
    const words = try relation.evaluate(a, parsed.value, assignment.value);
    const key = try native_pair.sealKey(a, source, air_bytes);
    defer a.free(key);
    var timer = try std.time.Timer.start();
    const raw = try native_pair.proveSealed(a, source, air_bytes, key, assignment.value);
    const prove_ns = timer.read();
    defer a.free(raw);
    timer.reset();
    try native_pair.verifySealed(a, source, air_bytes, key, words, raw);
    const verify_ns = timer.read();
    var binding = try pair_source.derive(a, source, air_bytes, 1);
    defer binding.deinit();
    std.debug.print("pair 16+32: proof_bytes={d} circuit_rows={d} chip_rows=16+32 bridge_rows=16+16 prove_ns={d} verify_ns={d}\n", .{
        raw.len,
        @as(usize, 1) << @intCast(binding.trace_log_size),
        prove_ns,
        verify_ns,
    });

    const changed_source = try std.fmt.allocPrint(a, "{s}\n", .{source});
    defer a.free(changed_source);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, changed_source, air_bytes, key, words, raw));
    const changed_key = try a.dupe(u8, key);
    defer a.free(changed_key);
    changed_key[0] = if (changed_key[0] == '{') '[' else '{';
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, changed_key, words, raw));
    var wrong_words = words;
    wrong_words[5] = (wrong_words[5] + 1) % 2147483647;
    try std.testing.expectError(error.InvalidPairPublicStatement, native_pair.verifySealed(a, source, air_bytes, key, wrong_words, raw));

    const changed_raw = try a.dupe(u8, raw);
    defer a.free(changed_raw);
    changed_raw[0] ^= 1;
    try std.testing.expectError(error.InvalidPairNativeEnvelope, native_pair.verifySealed(a, source, air_bytes, key, words, changed_raw));
    @memcpy(changed_raw, raw);
    std.mem.writeInt(u32, changed_raw[16..][0..4], 2147483647, .little);
    try std.testing.expectError(error.InvalidPairNativeEnvelope, native_pair.verifySealed(a, source, air_bytes, key, words, changed_raw));
    @memcpy(changed_raw, raw);
    changed_raw[8] ^= 1;
    if (native_pair.verifySealed(a, source, air_bytes, key, words, changed_raw)) |_| return error.TestUnexpectedResult else |_| {}
    @memcpy(changed_raw, raw);
    changed_raw[raw.len - 1] ^= 1;
    if (native_pair.verifySealed(a, source, air_bytes, key, words, changed_raw)) |_| return error.TestUnexpectedResult else |_| {}
}

test "two-call source derives canonical plan and five-role V3 manifest" {
    const a = std.testing.allocator;
    const source = @embedFile("../../examples/boundary/private_pair16_32.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    var binding = try pair_source.derive(a, source, air_bytes, 1);
    defer binding.deinit();
    try std.testing.expectEqual(@as(u32, 0), binding.plan.calls[0].call_id);
    try std.testing.expectEqual(@as(u32, 1), binding.plan.calls[1].call_id);
    try std.testing.expectEqual(@as(u32, 16), binding.plan.calls[0].rounds);
    try std.testing.expectEqual(@as(u32, 32), binding.plan.calls[1].rounds);
    try std.testing.expectEqual(@as(usize, 5), binding.generated.value.components.len);
    try std.testing.expectEqual(@as(u32, 5), binding.generated.value.claimed_sums);
    try std.testing.expectEqual(@as(usize, 46), pair.main_width);
    try std.testing.expectEqual(@as(usize, 64), pair.interaction_width);
    try std.testing.expectEqualStrings("s31-component-manifest-direct-pair-v1", binding.generated.value.schema);
    try std.testing.expectEqual(binding.precommitment_digest, manifest.pairPrecommitmentDigest(binding.generated.value));
    try std.testing.expectEqual(binding.effective_digest, manifest.pairEffectiveSourceDigest(binding.source_digest, binding.generated.value));
    try std.testing.expectError(error.UnsupportedPairPcsProfile, pair_source.derive(a, source, air_bytes, 2));

    var changed = binding.generated.value;
    changed.pair_calls[0].input[0] += 1;
    var changed_digest = manifest.pairPrecommitmentDigest(changed);
    try std.testing.expect(!std.mem.eql(u8, &binding.precommitment_digest, &changed_digest));
    try std.testing.expect(!(try manifest.matchesPair(a, binding.generated.value, changed)));
    changed = binding.generated.value;
    changed.pair_calls[0].call_id = 1;
    changed.pair_calls[1].call_id = 0;
    changed_digest = manifest.pairPrecommitmentDigest(changed);
    try std.testing.expect(!std.mem.eql(u8, &binding.precommitment_digest, &changed_digest));
    changed = binding.generated.value;
    const altered_components = try a.dupe(manifest.Component, changed.components);
    defer a.free(altered_components);
    altered_components[1].claimed_sum_index = 2;
    changed.components = altered_components;
    changed_digest = manifest.pairPrecommitmentDigest(changed);
    try std.testing.expect(!std.mem.eql(u8, &binding.precommitment_digest, &changed_digest));

    var assignment = try relation.parseAssignment(a, @embedFile("../../examples/boundary/private_pair16_32.valid.json"));
    defer assignment.deinit();
    var witness = try pair_source.compileWitness(a, source, assignment.value, &binding);
    defer witness.deinit();
    try std.testing.expect(std.meta.eql(binding.plan, witness.plan));
    try pair_source.verifySourceBinding(a, source, air_bytes, &binding);

    // Three independent views of the public claim: a short arithmetic oracle,
    // the source evaluator, and the circuit's eight reserved output wires.
    var parsed = try relation.parseProgram(a, source);
    defer parsed.deinit();
    const evaluated = try relation.evaluate(a, parsed.value, assignment.value);
    const left_inputs = [_]u32{ 3, 3, 7, 11 };
    const right_inputs = [_]u32{ 2, 4, 6, 8 };
    for (left_inputs, right_inputs, 0..) |left, right, lane| {
        const a_end = handRepeat(left, 13, 16);
        const b_end = handRepeat(right, 17, 32);
        const sum: u32 = @intCast((@as(u64, a_end) + b_end) % 2147483647);
        const product: u32 = @intCast((@as(u64, a_end) * b_end) % 2147483647);
        try std.testing.expectEqual(left, (try witness.context.values()[binding.plan.calls[0].input[lane]].tryIntoM31()).toU32());
        try std.testing.expectEqual(right, (try witness.context.values()[binding.plan.calls[1].input[lane]].tryIntoM31()).toU32());
        try std.testing.expectEqual(a_end, (try witness.context.values()[binding.plan.calls[0].output[lane]].tryIntoM31()).toU32());
        try std.testing.expectEqual(b_end, (try witness.context.values()[binding.plan.calls[1].output[lane]].tryIntoM31()).toU32());
        try std.testing.expectEqual(sum, evaluated[lane]);
        try std.testing.expectEqual(product, evaluated[4 + lane]);
        try std.testing.expectEqual(sum, (try witness.context.values()[3 + lane].tryIntoM31()).toU32());
        try std.testing.expectEqual(product, (try witness.context.values()[7 + lane].tryIntoM31()).toU32());
    }

    // A caller can reseal a forged manifest in memory, but it cannot change
    // the Plan the native verifier derives from the actual source.
    var forged = binding;
    forged.plan.calls[0].call_id = 1;
    forged.plan.calls[1].call_id = 0;
    forged.generated.value.pair_calls[0].call_id = 1;
    forged.generated.value.pair_calls[1].call_id = 0;
    forged.precommitment_digest = manifest.pairPrecommitmentDigest(forged.generated.value);
    forged.effective_digest = manifest.pairEffectiveSourceDigest(forged.source_digest, forged.generated.value);
    try std.testing.expectError(error.PairPlanMismatch, pair_source.compileWitness(a, source, assignment.value, &forged));
    try std.testing.expectError(error.PairSourceBindingMismatch, pair_source.verifySourceBinding(a, source, air_bytes, &forged));

    // A metadata-only alteration leaves Plan and circuit root unchanged, so
    // witness compilation alone accepts it. Source reconstruction still
    // rejects the rehashed five-component manifest before proof admission.
    var forged_metadata = binding;
    const forged_components = try a.dupe(manifest.Component, binding.generated.value.components);
    defer a.free(forged_components);
    forged_components[3].random_coefficient_offset += 1;
    forged_metadata.generated.value.components = forged_components;
    forged_metadata.precommitment_digest = manifest.pairPrecommitmentDigest(forged_metadata.generated.value);
    forged_metadata.effective_digest = manifest.pairEffectiveSourceDigest(forged_metadata.source_digest, forged_metadata.generated.value);
    var metadata_witness = try pair_source.compileWitness(a, source, assignment.value, &forged_metadata);
    defer metadata_witness.deinit();
    try std.testing.expectError(error.PairSourceBindingMismatch, pair_source.verifySourceBinding(a, source, air_bytes, &forged_metadata));

    // Reseal both the V3 digest and the circuit hash in a serialized key.
    // Native admission compares exact source-derived key bytes before it
    // even examines the (empty) proof envelope supplied here.
    const key_bytes = try native_pair.sealKey(a, source, air_bytes);
    defer a.free(key_bytes);
    var parsed_key = try std.json.parseFromSlice(native_pair.Key, a, key_bytes, .{});
    defer parsed_key.deinit();
    const key_components = try a.dupe(manifest.Component, parsed_key.value.component_manifest.components);
    defer a.free(key_components);
    key_components[3].random_coefficient_offset += 1;
    parsed_key.value.component_manifest.components = key_components;
    const changed_precommit = manifest.pairPrecommitmentDigest(parsed_key.value.component_manifest);
    const changed_precommit_hex = std.fmt.bytesToHex(changed_precommit, .lower);
    parsed_key.value.manifest_precommitment_sha256 = &changed_precommit_hex;
    var converted: pair_engine.Plan = .{ .calls = undefined };
    for (binding.plan.calls, &converted.calls) |call, *slot| slot.* = .{
        .call_id = call.call_id,
        .rounds = call.rounds,
        .constant = call.constant,
        .input = call.input,
        .output = call.output,
    };
    const changed_hash = pair_engine.identityHash(pair.effectiveDigest(binding.source_digest, changed_precommit), binding.preprocessed_root, binding.trace_log_size, 1, converted);
    const changed_hash_hex = std.fmt.bytesToHex(changed_hash, .lower);
    parsed_key.value.circuit_hash = &changed_hash_hex;
    parsed_key.value.component_manifest.circuit_hash = &changed_hash_hex;
    const resealed_key = try std.json.Stringify.valueAlloc(a, parsed_key.value, .{});
    defer a.free(resealed_key);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, resealed_key, evaluated, ""));

    const changed_source = try std.fmt.allocPrint(a, "{s}\n", .{source});
    defer a.free(changed_source);
    try std.testing.expectError(error.PairSourceMismatch, pair_source.compileWitness(a, changed_source, assignment.value, &binding));
}
