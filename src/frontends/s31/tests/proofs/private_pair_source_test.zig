const std = @import("std");
const relation = @import("../../language/relation.zig");
const pair_source = @import("../../runtime/pair_source_binding.zig");
const manifest = @import("../../runtime/component_manifest.zig");
const pair = @import("stwo_circuit_cpu_integration").private_pair_boundary;

fn handRepeat(start: u32, constant: u32, rounds: u32) u32 {
    const modulus: u64 = 2147483647;
    var value: u64 = start;
    for (0..rounds) |_| value = (value * value + constant) % modulus;
    return @intCast(value);
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

    const changed_source = try std.fmt.allocPrint(a, "{s}\n", .{source});
    defer a.free(changed_source);
    try std.testing.expectError(error.PairSourceMismatch, pair_source.compileWitness(a, changed_source, assignment.value, &binding));
}
