//! Native finite differential for the first four Gate circle-basis slots.
const std = @import("std");
const core = @import("stwo_core");
const circle_poly = @import("stwo_prover_engine").poly.circle.poly;
const M31 = core.fields.m31.M31;

const tuples = [_][4]u32{
    .{ 0, 0, 0, 0 },
    .{ 1, 0, 0, 0 },
    .{ 0, 1, 0, 0 },
    .{ 0, 0, 1, 0 },
    .{ 0, 0, 0, 1 },
    .{ 7, 11, 13, 17 },
    .{ 2147483646, 2147483645, 123456789, 987654321 },
};

test "Gate log-4 four-slot native FFT refines point evaluator" {
    const allocator = std.testing.allocator;
    const domain = core.poly.circle.canonic.CanonicCoset.new(4).circleDomain();
    const one = M31.fromCanonical(1);
    const zero = M31.zero();

    for (tuples) |tuple| {
        var coeffs = [_]M31{zero} ** 16;
        for (tuple, 0..) |word, slot| coeffs[slot] = M31.fromCanonical(word);
        const polynomial = try circle_poly.CircleCoefficients.initBorrowed(&coeffs);
        const evaluation = try polynomial.evaluate(allocator, domain);
        defer allocator.free(@constCast(evaluation.values));

        for (evaluation.values, 0..) |value, row| {
            const point = domain.at(core.utils.bitReverseIndex(row, 4));
            const direct = coeffs[0].add(coeffs[1].mul(point.y))
                .add(coeffs[2].add(coeffs[3].mul(point.y)).mul(point.x));
            try std.testing.expect(value.eql(direct));
        }

        var recovered = try circle_poly.interpolateFromEvaluation(
            allocator,
            evaluation,
        );
        defer recovered.deinit(allocator);
        try std.testing.expectEqualSlices(M31, &coeffs, recovered.coefficients());

        // A single altered committed source row cannot remain in this
        // four-slot subspace; interpolation must expose a high slot.
        const altered = try allocator.dupe(M31, evaluation.values);
        defer allocator.free(altered);
        altered[0] = altered[0].add(one);
        var altered_coeffs = try circle_poly.interpolateFromEvaluation(
            allocator,
            .{ .domain = domain, .values = altered },
        );
        defer altered_coeffs.deinit(allocator);
        var found_high = false;
        for (altered_coeffs.coefficients()[4..]) |coefficient| {
            found_high = found_high or !coefficient.eql(zero);
        }
        try std.testing.expect(found_high);
    }
}
