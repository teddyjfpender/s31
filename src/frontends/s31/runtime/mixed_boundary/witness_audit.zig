//! Source-bound N=4 mixed witness and native base-trace audit.
//!
//! This consumes a witness and checks concrete circuit/chip/bridge handoffs.
//! It emits no proof and is not a verifier. Native N=4 proof admission still
//! requires a separately reviewed engine prover, transcript, and verifier.
const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const relation = @import("../../language/relation.zig");
const binding = @import("../bounded_compiled_binding.zig");
const mixed = @import("inspection.zig");
const descriptor = @import("descriptor.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
pub const n_calls = 4;

pub const Handoff = struct {
    input: [4]u32,
    output: [4]u32,
};

pub const Audit = struct {
    source_sha256: [32]u8,
    manifest_sha256: [32]u8,
    descriptor_sha256: [32]u8,
    public_words: [8]u32,
    calls: [n_calls]Handoff,
};

/// Rebuild source and live handles before reading a value. Both supplied
/// metadata objects are treated as untrusted and checked against source.
pub fn inspectN4Witness(
    allocator: std.mem.Allocator,
    source: []const u8,
    air_bytes: []const u8,
    selected: *const mixed.SelectedSchedule,
    supplied_descriptor: *const descriptor.Descriptor,
    assignment: relation.Assignment,
) !Audit {
    if (selected.call_count != n_calls or selected.slot_count != 1 + 2 * n_calls)
        return error.UnsupportedMixedWitnessCount;
    if (!try mixed.matchesSource(allocator, selected, source, air_bytes))
        return error.InvalidMixedWitnessSelection;
    try descriptor.requireSource(allocator, supplied_descriptor, source, air_bytes);
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const public_words = try relation.evaluate(allocator, parsed.value, assignment);
    const topology = try binding.compileSourceTopology(allocator, source);
    if (topology.call_count != n_calls or
        !std.meta.eql(topology.source_sha256, selected.source_sha256) or
        !std.meta.eql(topology.canonical_ir_sha256, selected.canonical_ir_sha256) or
        !std.meta.eql(topology.fixed_root, selected.fixed_root))
        return error.InvalidMixedWitnessSelection;
    for (topology.callSlice(), selected.calls[0..n_calls]) |compiled, source_call| {
        if (compiled.call_id != source_call.call_id or
            compiled.source_node_id != source_call.source_node_id or
            compiled.input_node_id != source_call.input_node_id or
            compiled.rounds != source_call.rounds or
            compiled.constant != source_call.constant or
            !std.meta.eql(compiled.input, source_call.input) or
            !std.meta.eql(compiled.output, source_call.output))
            return error.InvalidMixedWitnessSelection;
    }
    var witness = try binding.compileManyWitness(allocator, source, assignment, topology);
    defer witness.deinit();
    const view = circuit.common.preprocessed.CircuitView.fromBuilder(&witness.circuit);
    var plan: cpu.private_many_boundary.Plan = .{ .count = n_calls };
    for (selected.calls[0..n_calls], plan.calls[0..n_calls]) |call, *out| {
        if (call.constant >= core.fields.m31.Modulus) return error.InvalidMixedWitnessSelection;
        out.* = .{
            .call_id = call.call_id,
            .rounds = call.rounds,
            .constant = M31.fromCanonical(call.constant),
            .input = call.input,
            .output = call.output,
        };
    }
    var pp = try plan.preprocessed(allocator, view);
    defer pp.deinit(allocator);
    if (!std.meta.eql(try pp.preprocessedRoot(allocator, 1), selected.fixed_root))
        return error.InvalidMixedWitnessSelection;
    var base = try circuit.witness.direct_arithmetic.writeBase(allocator, witness.values(), &pp);
    defer base.deinit();
    if (base.output_values.len != public_words.len) return error.WrongMixedPublicHandoff;
    for (base.output_values, public_words) |actual, expected| {
        const word = actual.tryIntoM31() catch return error.WrongMixedPublicHandoff;
        if (word.toU32() != expected) return error.WrongMixedPublicHandoff;
    }
    const calls = try auditHandoffs(allocator, selected, witness.values());
    return .{
        .source_sha256 = selected.source_sha256,
        .manifest_sha256 = selected.digest,
        .descriptor_sha256 = supplied_descriptor.digest,
        .public_words = public_words,
        .calls = calls,
    };
}

/// Used after the source and witness topology have been independently checked.
/// Kept private so a caller cannot treat a handoff check as proof admission.
fn auditHandoffs(allocator: std.mem.Allocator, selected: *const mixed.SelectedSchedule, values: []const QM31) ![n_calls]Handoff {
    if (selected.call_count != n_calls or selected.slot_count != 1 + 2 * n_calls)
        return error.UnsupportedMixedWitnessCount;
    var result: [n_calls]Handoff = undefined;
    for (selected.calls[0..n_calls], &result, 0..) |call, *out, id| {
        if (call.call_id != id or call.constant >= core.fields.m31.Modulus)
            return error.InvalidMixedWitnessSelection;
        const wanted_chip: mixed.SourceKind = if (id < 2) .pair_chip else .many_chip;
        const wanted_bridge: mixed.SourceKind = if (id < 2) .pair_bridge else .many_bridge;
        if (selected.slots[1 + 2 * id].source_kind != wanted_chip or
            selected.slots[2 + 2 * id].source_kind != wanted_bridge)
            return error.InvalidMixedWitnessSelection;
        var input: [4]M31 = undefined;
        var output: [4]M31 = undefined;
        for (0..4) |lane| {
            if (call.input[lane] >= values.len or call.output[lane] >= values.len)
                return error.InvalidMixedHandoffAddress;
            input[lane] = values[call.input[lane]].tryIntoM31() catch return error.NonBaseMixedHandoff;
            output[lane] = values[call.output[lane]].tryIntoM31() catch return error.NonBaseMixedHandoff;
        }
        var chip_base = if (id < 2)
            try cpu.tagged_pair_chip.writeBase(allocator, input, M31.fromCanonical(call.constant), call.rounds)
        else
            try cpu.tagged_many_chip.writeBase(allocator, input, M31.fromCanonical(call.constant), call.rounds);
        defer chip_base.deinit();
        const log_size = try cpu.repeated_step_chip.validateRounds(call.rounds);
        if (chip_base.columns.len != 9 or chip_base.final.len != 4)
            return error.InvalidMixedChipBase;
        var state: [4]u32 = undefined;
        for (input, &state) |word, *slot| slot.* = word.toU32();
        for (0..call.rounds) |step| {
            const row = cpu.repeated_step_chip.storageIndex(step, log_size);
            if (chip_base.columns[0].values[row].toU32() != step)
                return error.InvalidMixedChipBase;
            for (&state, 0..) |*word, lane| {
                if (chip_base.columns[1 + lane].values[row].toU32() != word.*)
                    return error.InvalidMixedChipBase;
                // Independent integer recurrence in the prime field.
                word.* = @intCast((@as(u64, word.*) * word.* + call.constant) % core.fields.m31.Modulus);
                if (chip_base.columns[5 + lane].values[row].toU32() != word.*)
                    return error.InvalidMixedChipBase;
            }
        }
        for (output, state, 0..) |word, expected, lane| {
            if (word.toU32() != expected or chip_base.final[lane].toU32() != expected)
                return error.WrongMixedHandoff;
        }
        if (id < 2) {
            var bridge = try cpu.tagged_pair_bridge.writeBase(allocator, values, .{
                .call_id = call.call_id,
                .rounds = call.rounds,
                .constant = M31.fromCanonical(call.constant),
                .input = call.input,
                .output = call.output,
            });
            defer bridge.deinit();
            try checkBridgeBase(bridge.columns, input, output);
        } else {
            var bridge = try cpu.tagged_many_bridge.writeBase(allocator, values, .{
                .call_id = call.call_id,
                .rounds = call.rounds,
                .constant = M31.fromCanonical(call.constant),
                .input = call.input,
                .output = call.output,
            });
            defer bridge.deinit();
            try checkBridgeBase(bridge.columns, input, output);
        }
        for (0..4) |lane| {
            out.input[lane] = input[lane].toU32();
            out.output[lane] = output[lane].toU32();
        }
    }
    return result;
}

fn checkBridgeBase(columns: anytype, input: [4]M31, output: [4]M31) !void {
    if (columns.len != 8) return error.InvalidMixedBridgeBase;
    for (columns, 0..) |column, index| {
        if (column.values.len != 16) return error.InvalidMixedBridgeBase;
        const expected = if (index < 4) input[index] else output[index - 4];
        for (column.values) |word|
            if (!word.eql(expected)) return error.InvalidMixedBridgeBase;
    }
}

test "mixed N4 witness audit checks circuit chip and bridge handoffs" {
    const a = std.testing.allocator;
    const source = @embedFile("../../examples/boundary/mixed_four.s31.json");
    const air_bytes = @embedFile("s31_air_programs");
    const assignment_bytes = @embedFile("../../examples/boundary/mixed_four.valid.json");
    var parsed_assignment = try relation.parseAssignment(a, assignment_bytes);
    defer parsed_assignment.deinit();
    const selected = try mixed.inspectSource(a, source, air_bytes);
    const source_descriptor = try descriptor.fromSchedule(&selected);
    const audit = try inspectN4Witness(a, source, air_bytes, &selected, &source_descriptor, parsed_assignment.value);
    try std.testing.expectEqual(@as(u32, 80), selected.main_columns);
    try std.testing.expectEqual(@as(u32, 120), selected.interaction_columns);
    try std.testing.expectEqualSlices(u32, &.{ 2094051178, 181768886, 881143857, 2099579072, 1987186231, 908844405, 1873039656, 1620533201 }, &audit.public_words);
    for (1..n_calls) |id|
        try std.testing.expectEqualDeep(audit.calls[id - 1].output, audit.calls[id].input);
    try std.testing.expectEqualSlices(u32, &.{ 2094051175, 181768881, 881143850, 2099579061 }, &audit.calls[3].output);

    // Change a compiled endpoint value without changing its source address.
    const topology = try binding.compileSourceTopology(a, source);
    var witness = try binding.compileManyWitness(a, source, parsed_assignment.value, topology);
    defer witness.deinit();
    const values = try a.dupe(QM31, witness.values());
    defer a.free(values);
    const output_address = selected.calls[3].output[0];
    values[output_address] = QM31.fromBase(M31.fromCanonical(audit.calls[3].output[0] + 1));
    try std.testing.expectError(error.WrongMixedHandoff, auditHandoffs(a, &selected, values));
    @memcpy(values, witness.values());
    const input_address = selected.calls[3].input[0];
    values[input_address] = QM31.fromBase(M31.fromCanonical(audit.calls[3].input[0] + 1));
    if (auditHandoffs(a, &selected, values)) |_| return error.AcceptedWrongMixedInput else |_| {}

    var changed_selection = selected;
    changed_selection.slots[7].source_kind = .pair_chip;
    try std.testing.expectError(error.InvalidMixedWitnessSelection, inspectN4Witness(a, source, air_bytes, &changed_selection, &source_descriptor, parsed_assignment.value));
    changed_selection = selected;
    std.mem.swap(mixed.Slot, &changed_selection.slots[7], &changed_selection.slots[8]);
    try std.testing.expectError(error.InvalidMixedWitnessSelection, inspectN4Witness(a, source, air_bytes, &changed_selection, &source_descriptor, parsed_assignment.value));
    changed_selection = selected;
    changed_selection.calls[3].input[0] += 1;
    try std.testing.expectError(error.InvalidMixedWitnessSelection, inspectN4Witness(a, source, air_bytes, &changed_selection, &source_descriptor, parsed_assignment.value));

    var changed_descriptor = source_descriptor;
    changed_descriptor.entries[7].source.native_air.program_binding_sha256[0] ^= 1;
    changed_descriptor.digest = try @import("../component_descriptor_contract.zig").digest(changed_descriptor.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, inspectN4Witness(a, source, air_bytes, &selected, &changed_descriptor, parsed_assignment.value));
    changed_descriptor = source_descriptor;
    std.mem.swap(@import("../component_descriptor_contract.zig").Source, &changed_descriptor.entries[7].source, &changed_descriptor.entries[8].source);
    changed_descriptor.digest = try @import("../component_descriptor_contract.zig").digest(changed_descriptor.roster());
    try std.testing.expectError(error.InvalidMixedDescriptor, inspectN4Witness(a, source, air_bytes, &selected, &changed_descriptor, parsed_assignment.value));

    const altered_source = try std.mem.replaceOwned(u8, a, source, "\"constant\": 16", "\"constant\": 17");
    defer a.free(altered_source);
    try std.testing.expect(!std.mem.eql(u8, source, altered_source));
    try std.testing.expectError(error.InvalidMixedWitnessSelection, inspectN4Witness(a, altered_source, air_bytes, &selected, &source_descriptor, parsed_assignment.value));

    const bad_public = try std.mem.replaceOwned(u8, a, assignment_bytes, "2094051178", "2094051179");
    defer a.free(bad_public);
    try std.testing.expect(!std.mem.eql(u8, assignment_bytes, bad_public));
    var bad_assignment = try relation.parseAssignment(a, bad_public);
    defer bad_assignment.deinit();
    if (inspectN4Witness(a, source, air_bytes, &selected, &source_descriptor, bad_assignment.value)) |_| return error.AcceptedWrongMixedPublicOutput else |_| {}
}
