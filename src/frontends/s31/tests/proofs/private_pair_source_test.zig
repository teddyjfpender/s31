const std = @import("std");
const relation = @import("../../language/relation.zig");
const pair_source = @import("../../runtime/pair_source_binding.zig");
const native_pair = @import("../../runtime/pair_native_package.zig");
const manifest = @import("../../runtime/component_manifest.zig");
const pair = @import("stwo_circuit_cpu_integration").private_pair_boundary;
const pair_engine = @import("stwo_circuit_cpu_integration").experimental_direct_pair_arithmetic;

fn handRepeat(start: u32, constant: u32, rounds: u32) u32 {
    const modulus: u64 = 2147483647;
    var value: u64 = start;
    for (0..rounds) |_| value = (value * value + constant) % modulus;
    return @intCast(value);
}

fn resealPairKey(a: std.mem.Allocator, original: native_pair.Key, altered: manifest.PairManifest, binding: *const pair_source.Binding) ![]u8 {
    var key = original;
    key.component_manifest = altered;
    const digest = manifest.pairPrecommitmentDigest(altered);
    const digest_hex = std.fmt.bytesToHex(digest, .lower);
    key.manifest_precommitment_sha256 = &digest_hex;
    var plan: pair_engine.Plan = .{ .calls = undefined };
    for (binding.plan.calls, &plan.calls) |call, *slot| slot.* = .{
        .call_id = call.call_id,
        .rounds = call.rounds,
        .constant = call.constant,
        .input = call.input,
        .output = call.output,
    };
    const hash = pair_engine.identityHash(pair.effectiveDigest(binding.source_digest, digest), binding.preprocessed_root, binding.trace_log_size, 1, plan);
    const hash_hex = std.fmt.bytesToHex(hash, .lower);
    key.circuit_hash = &hash_hex;
    key.component_manifest.circuit_hash = &hash_hex;
    return std.json.Stringify.valueAlloc(a, key, .{});
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
    try std.testing.expectError(error.InvalidPairNativeEnvelope, native_pair.verifySealed(a, source, air_bytes, key, words, ""));
    try std.testing.expectError(error.InvalidPairNativeEnvelope, native_pair.verifySealed(a, source, air_bytes, key, words, "S31NAT8P"));

    const changed_source = try std.fmt.allocPrint(a, "{s}\n", .{source});
    defer a.free(changed_source);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, changed_source, air_bytes, key, words, raw));
    const changed_key = try a.dupe(u8, key);
    defer a.free(changed_key);
    changed_key[0] = if (changed_key[0] == '{') '[' else '{';
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, changed_key, words, raw));
    var wrong_words = words;
    wrong_words[5] = (wrong_words[5] + 1) % 2147483647;
    // The public words enter the transcript before the interaction nonce;
    // changing them may fail at that nonce before later statement checks.
    if (native_pair.verifySealed(a, source, air_bytes, key, wrong_words, raw)) |_| return error.TestUnexpectedResult else |_| {}

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

    // Postcard's general decoder accepts overlong LEB128. The allocation-free
    // source-shaped preflight must reject 26 as 0x9a,0x00 before decoding.
    const header_len = "S31NAT8P".len + 8 + 5 * 16;
    try std.testing.expectEqual(@as(u8, 26), raw[header_len]);
    const overlong = try a.alloc(u8, raw.len + 1);
    defer a.free(overlong);
    @memcpy(overlong[0..header_len], raw[0..header_len]);
    overlong[header_len] = 0x9a;
    overlong[header_len + 1] = 0;
    @memcpy(overlong[header_len + 2 ..], raw[header_len + 1 ..]);
    try std.testing.expectError(error.NonCanonicalVarint, native_pair.verifySealed(a, source, air_bytes, key, words, overlong));

    // Swap both canonical call tags, then reseal the typed manifest digest
    // and circuit identity as an attacker controlling a serialized key might.
    // Source reconstruction still rejects the byte-entry before proof parse.
    var parsed_key = try std.json.parseFromSlice(native_pair.Key, a, key, .{});
    defer parsed_key.deinit();
    parsed_key.value.component_manifest.pair_calls[0].call_id = 1;
    parsed_key.value.component_manifest.pair_calls[1].call_id = 0;
    const swapped_precommit = manifest.pairPrecommitmentDigest(parsed_key.value.component_manifest);
    const swapped_precommit_hex = std.fmt.bytesToHex(swapped_precommit, .lower);
    parsed_key.value.manifest_precommitment_sha256 = &swapped_precommit_hex;
    var swapped_plan: pair_engine.Plan = .{ .calls = undefined };
    for (binding.plan.calls, &swapped_plan.calls) |call, *slot| slot.* = .{
        .call_id = 1 - call.call_id,
        .rounds = call.rounds,
        .constant = call.constant,
        .input = call.input,
        .output = call.output,
    };
    const swapped_hash = pair_engine.identityHash(pair.effectiveDigest(binding.source_digest, swapped_precommit), binding.preprocessed_root, binding.trace_log_size, 1, swapped_plan);
    const swapped_hash_hex = std.fmt.bytesToHex(swapped_hash, .lower);
    parsed_key.value.circuit_hash = &swapped_hash_hex;
    parsed_key.value.component_manifest.circuit_hash = &swapped_hash_hex;
    const swapped_key = try std.json.Stringify.valueAlloc(a, parsed_key.value, .{});
    defer a.free(swapped_key);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, swapped_key, words, raw));
}

test "sealed pair native long-round lifting keeps preprocessed root and proof aligned" {
    const a = std.testing.allocator;
    const original = @embedFile("../../examples/boundary/private_pair16_32.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    const first = try std.mem.replaceOwned(u8, a, original, "\"rounds\": 16", "\"rounds\": 1024");
    defer a.free(first);
    const source = try std.mem.replaceOwned(u8, a, first, "\"rounds\": 32", "\"rounds\": 4096");
    defer a.free(source);
    const left_input = [_]u32{ 3, 3, 7, 11 };
    const right_input = [_]u32{ 2, 4, 6, 8 };
    var sums: [4]u32 = undefined;
    var products: [4]u32 = undefined;
    for (left_input, right_input, 0..) |left, right, lane| {
        const left_end = handRepeat(left, 13, 1024);
        const right_end = handRepeat(right, 17, 4096);
        sums[lane] = @intCast((@as(u64, left_end) + right_end) % 2147483647);
        products[lane] = @intCast((@as(u64, left_end) * right_end) % 2147483647);
    }
    const outputs_json = try std.json.Stringify.valueAlloc(a, .{ .sum = sums, .product = products }, .{});
    defer a.free(outputs_json);
    const assignment_json = try std.fmt.allocPrint(
        a,
        "{{\"public_inputs\":{{}},\"private_inputs\":{{\"left\":[3,3,7,11],\"right\":[2,4,6,8]}},\"public_outputs\":{s}}}",
        .{outputs_json},
    );
    defer a.free(assignment_json);
    var assignment = try relation.parseAssignment(a, assignment_json);
    defer assignment.deinit();
    var parsed = try relation.parseProgram(a, source);
    defer parsed.deinit();
    const words = try relation.evaluate(a, parsed.value, assignment.value);
    var binding = try pair_source.derive(a, source, air_bytes, 1);
    defer binding.deinit();
    try std.testing.expect(binding.trace_log_size < 12);
    try std.testing.expectEqual(@as(u32, 1024), binding.plan.calls[0].rounds);
    try std.testing.expectEqual(@as(u32, 4096), binding.plan.calls[1].rounds);
    const key = try native_pair.sealKey(a, source, air_bytes);
    defer a.free(key);
    const raw = try native_pair.proveSealed(a, source, air_bytes, key, assignment.value);
    defer a.free(raw);
    try native_pair.verifySealed(a, source, air_bytes, key, words, raw);
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
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));
    changed = binding.generated.value;
    const altered_components = try a.dupe(manifest.Component, changed.components);
    defer a.free(altered_components);
    altered_components[1].claimed_sum_index = 2;
    changed.components = altered_components;
    changed_digest = manifest.pairPrecommitmentDigest(changed);
    try std.testing.expect(!std.mem.eql(u8, &binding.precommitment_digest, &changed_digest));

    // A native component cannot borrow the bundled AIR slot or another
    // component's proof/sum position, even with a rehashed manifest.
    const wrong_name = try a.dupe(manifest.Component, binding.generated.value.components);
    defer a.free(wrong_name);
    wrong_name[1].name = "unregistered_native_air";
    changed = binding.generated.value;
    changed.components = wrong_name;
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));
    try std.testing.expect(!(try manifest.matchesPair(a, changed, binding.generated.value)));
    const wrong_role = try a.dupe(manifest.Component, binding.generated.value.components);
    defer a.free(wrong_role);
    std.mem.swap(manifest.Component, &wrong_role[1], &wrong_role[3]);
    changed.components = wrong_role;
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));
    try std.testing.expect(!(try manifest.matchesPair(a, changed, binding.generated.value)));

    // Geometry and lookup dependencies are checked as a typed roster, before
    // an attacker-controlled serialized key is compared with the source.
    const wrong_geometry = try a.dupe(manifest.Component, binding.generated.value.components);
    defer a.free(wrong_geometry);
    changed.components = wrong_geometry;
    const original_chip = wrong_geometry[1];
    wrong_geometry[1].main_trace_span = .{ .tree = 1, .start = 0, .end = 9 };
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));
    wrong_geometry[1] = original_chip;
    wrong_geometry[1].evaluation_log_size += 1;
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));
    wrong_geometry[1] = original_chip;
    wrong_geometry[3].lookup_relation_ids = &.{pair.relation_id};
    try std.testing.expectError(error.InvalidPairComponentManifest, manifest.validatePairSourceRoster(changed));

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
    var fake_raw = [_]u8{0} ** ("S31NAT8P".len + 8 + 5 * 16);
    @memcpy(fake_raw[0.."S31NAT8P".len], "S31NAT8P");
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, resealed_key, evaluated, &fake_raw));

    var pristine = try std.json.parseFromSlice(native_pair.Key, a, key_bytes, .{});
    defer pristine.deinit();
    const renamed = try a.dupe(manifest.Component, pristine.value.component_manifest.components);
    defer a.free(renamed);
    renamed[1].name = "unregistered_native_air";
    var altered = pristine.value.component_manifest;
    altered.components = renamed;
    const renamed_key = try resealPairKey(a, pristine.value, altered, &binding);
    defer a.free(renamed_key);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, renamed_key, evaluated, &fake_raw));
    const swapped_roles = try a.dupe(manifest.Component, pristine.value.component_manifest.components);
    defer a.free(swapped_roles);
    std.mem.swap(manifest.Component, &swapped_roles[1], &swapped_roles[3]);
    altered.components = swapped_roles;
    const swapped_roles_key = try resealPairKey(a, pristine.value, altered, &binding);
    defer a.free(swapped_roles_key);
    try std.testing.expectError(error.InvalidPairVerificationKey, native_pair.verifySealed(a, source, air_bytes, swapped_roles_key, evaluated, &fake_raw));

    const changed_source = try std.fmt.allocPrint(a, "{s}\n", .{source});
    defer a.free(changed_source);
    try std.testing.expectError(error.PairSourceMismatch, pair_source.compileWitness(a, changed_source, assignment.value, &binding));
}
