//! Finite source-height differential: native FFT rows, inverse FFT, and the
//! independent subset-product circle basis agree on dense coefficient words.
const std = @import("std");
const core = @import("stwo_core");
const circle_poly = @import("stwo_prover_engine").poly.circle.poly;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

fn referenceFactors(
    point: core.circle.CirclePointQM31,
    coefficient_log: u32,
    out: *[core.circle.M31_CIRCLE_LOG_ORDER]QM31,
) []const QM31 {
    out[0] = point.y;
    var x = point.x;
    for (1..coefficient_log) |bit| {
        out[bit] = x;
        const squared = x.square();
        x = squared.add(squared).sub(QM31.one());
    }
    return out[0..coefficient_log];
}

fn independentDot(coefficients: []const M31, factors: []const QM31) QM31 {
    var result = QM31.zero();
    for (coefficients, 0..) |coefficient, index| {
        var basis = QM31.one();
        for (factors, 0..) |factor, bit| {
            if (((index >> @intCast(bit)) & 1) != 0) basis = basis.mul(factor);
        }
        result = result.add(basis.mulM31(coefficient));
    }
    return result;
}

fn checkHeight(allocator: std.mem.Allocator, coefficient_log: u32) !void {
    const count: usize = @as(usize, 1) << @intCast(coefficient_log);
    const coefficients = try allocator.alloc(M31, count);
    defer allocator.free(coefficients);

    // Every slot is occupied, including the highest native circle-basis slot.
    for (coefficients, 0..) |*coefficient, index| {
        const value: u32 = @intCast((index *% 104729 +% 12345) % core.fields.m31.Modulus);
        coefficient.* = M31.fromCanonical(value);
    }
    const polynomial = try circle_poly.CircleCoefficients.initBorrowed(coefficients);
    const domain = core.poly.circle.canonic.CanonicCoset.new(coefficient_log).circleDomain();
    const rows = try polynomial.evaluate(allocator, domain);
    defer allocator.free(@constCast(rows.values));
    try std.testing.expectEqual(count, rows.values.len);

    var recovered = try circle_poly.interpolateFromEvaluation(allocator, rows);
    defer recovered.deinit(allocator);
    try std.testing.expectEqualSlices(M31, coefficients, recovered.coefficients());

    const selected_rows = [_]usize{ 0, 1, count / 3, count / 2, count - 1 };
    for (selected_rows) |row| {
        const domain_point = domain.at(core.utils.bitReverseIndex(row, coefficient_log));
        const point: core.circle.CirclePointQM31 = .{
            .x = QM31.fromBase(domain_point.x),
            .y = QM31.fromBase(domain_point.y),
        };
        var factor_buffer: [core.circle.M31_CIRCLE_LOG_ORDER]QM31 = undefined;
        const factors = referenceFactors(point, coefficient_log, &factor_buffer);
        var native_factor_buffer: [core.circle.M31_CIRCLE_LOG_ORDER]QM31 = undefined;
        const native_factors = circle_poly.fillEvalFactorsForPoint(
            point, coefficient_log, &native_factor_buffer,
        );
        for (factors, native_factors) |expected_factor, native_factor| {
            try std.testing.expect(expected_factor.eql(native_factor));
        }
        const expected = independentDot(coefficients, factors);
        try std.testing.expect(expected.eql(QM31.fromBase(rows.values[row])));
        try std.testing.expect(expected.eql(recovered.evalAtPoint(point)));
    }

    // Sampled values use secure-field points outside the M31 source domain.
    const secure_point = core.circle.SECURE_FIELD_CIRCLE_GEN;
    var secure_factor_buffer: [core.circle.M31_CIRCLE_LOG_ORDER]QM31 = undefined;
    const secure_factors = referenceFactors(
        secure_point, coefficient_log, &secure_factor_buffer,
    );
    try std.testing.expect(independentDot(coefficients, secure_factors)
        .eql(recovered.evalAtPoint(secure_point)));
}

test "P05 sparse source FFT provenance differential at all accepted heights" {
    const allocator = std.testing.allocator;
    // Extended source heights 5, 11, and 17 have coefficient logs 4, 10, 16.
    for ([_]u32{ 4, 10, 16 }) |coefficient_log| try checkHeight(allocator, coefficient_log);
}
