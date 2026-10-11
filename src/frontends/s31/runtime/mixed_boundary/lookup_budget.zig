//! Checked lookup-count envelope for the closed pair/many mixed registry.
//!
//! These are upper bounds on one conditional algebraic failure event, not a
//! proof-system security level. See the lookup-compression worksheet.
const std = @import("std");
const P: u64 = (1 << 31) - 1;
pub const max_calls: usize = 8;
pub const max_circuit_rows: usize = 1 << 16;
pub const max_chip_rounds: u64 = 1 << 18;
pub const public_output_addresses: usize = 9; // eight words and reserved u
pub const bridge_rows: u64 = 16;

pub const Budget = struct {
    circuit_rows: u64,
    chip_rounds: u64,
    call_count: u64,
    output_addresses: u64,
    /// Upper bound on all Gate, chip, bridge and public lookup occurrences.
    event_occurrences: u64,
    /// Sum of absolute signed weights after multiplying the closure by 16.
    integerized_absolute_weight: u64,
    /// Numerator of the conditional direct bound (7*T - 6)/QM31.order.
    conditional_lookup_numerator: u64,
};

/// `rows` is the source-rebuilt CircuitView.nQm31OpsRows(), `output_count`
/// is CircuitView.output.len, and `rounds` follow source-selected call order.
/// The caller must also match these counts to the live registered AIR slots.
pub fn evaluate(rows: usize, output_count: usize, rounds: []const u32) !Budget {
    if (rows < 16 or rows > max_circuit_rows or !std.math.isPowerOfTwo(rows) or
        output_count != public_output_addresses or rounds.len == 0 or rounds.len > max_calls)
        return error.InvalidMixedLookupGeometry;
    var total_rounds: u64 = 0;
    for (rounds) |count| {
        if (count < 16 or count > 32768 or !std.math.isPowerOfTwo(count))
            return error.InvalidMixedLookupGeometry;
        total_rounds = try std.math.add(u64, total_rounds, count);
    }
    if (total_rounds > max_chip_rounds) return error.InvalidMixedLookupGeometry;
    return calculate(@intCast(rows), total_rounds, @intCast(rounds.len), @intCast(output_count));
}

fn calculate(rows: u64, rounds: u64, calls: u64, outputs: u64) !Budget {
    // Three Gate terms per circuit row, two chip terms per round, ten bridge
    // terms on each of 16 rows per call, and one term per output address.
    var occurrences = try std.math.mul(u64, 3, rows);
    occurrences = try std.math.add(u64, occurrences, try std.math.mul(u64, 2, rounds));
    occurrences = try std.math.add(u64, occurrences, try std.math.mul(u64, 10 * bridge_rows, calls));
    occurrences = try std.math.add(u64, occurrences, outputs);
    // Circuit: 4R + O + 8N; chip: 2S; public statement: O.
    // The bridge has 10*16*N unit terms after multiplying by 16.
    var unscaled = try std.math.mul(u64, 4, rows);
    unscaled = try std.math.add(u64, unscaled, try std.math.mul(u64, 8, calls));
    unscaled = try std.math.add(u64, unscaled, try std.math.mul(u64, 2, outputs));
    unscaled = try std.math.add(u64, unscaled, try std.math.mul(u64, 2, rounds));
    const scaled = try std.math.mul(u64, 16, unscaled);
    const weight = try std.math.add(u64, scaled, try std.math.mul(u64, 10 * bridge_rows, calls));
    if (weight >= P) return error.MixedLookupWeightReachesCharacteristic;
    const numerator = try std.math.sub(u64, try std.math.mul(u64, 7, occurrences), 6);
    return .{
        .circuit_rows = rows,
        .chip_rounds = rounds,
        .call_count = calls,
        .output_addresses = outputs,
        .event_occurrences = occurrences,
        .integerized_absolute_weight = weight,
        .conditional_lookup_numerator = numerator,
    };
}

test "closed N1 and N8 envelopes count every bridge row" {
    const one = try evaluate(16, 9, &.{16});
    try std.testing.expectEqual(@as(u64, 249), one.event_occurrences);
    try std.testing.expectEqual(@as(u64, 2112), one.integerized_absolute_weight);
    const max_rounds = [_]u32{32768} ** 8;
    const eight = try evaluate(1 << 16, 9, &max_rounds);
    try std.testing.expectEqual(@as(u64, 722185), eight.event_occurrences);
    try std.testing.expectEqual(@as(u64, 12585504), eight.integerized_absolute_weight);
    try std.testing.expectEqual(@as(u64, 5055289), eight.conditional_lookup_numerator);
    try std.testing.expect(eight.integerized_absolute_weight < P);
}

test "lookup envelope rejects output, row and round geometry" {
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(16, 8, &.{16}));
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(16, 10, &.{16}));
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(17, 9, &.{16}));
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(1 << 17, 9, &.{16}));
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(16, 9, &.{}));
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(16, 9, &.{15}));
    const nine_rounds = [_]u32{16} ** 9;
    try std.testing.expectError(error.InvalidMixedLookupGeometry, evaluate(16, 9, &nine_rounds));
}

test "lookup integer arithmetic rejects characteristic crossing and overflow" {
    try std.testing.expectError(error.MixedLookupWeightReachesCharacteristic, calculate(1 << 28, 0, 1, 9));
    try std.testing.expectError(error.Overflow, calculate(std.math.maxInt(u64), 0, 1, 9));
}
