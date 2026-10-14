//! A finite, pinned-native Gate countercheck. The source column is M31 x^2
//! on the exact 16-row canonical log-4 domain, outside the first four circle
//! coefficient slots. Its correct two-point OOD claim nevertheless makes the
//! own quotient affine in x,y on all rows. This is not an accepting PCS proof.
const std = @import("std");
const core = @import("stwo_core");
const prover_engine = @import("stwo_prover_engine");

const M31 = core.fields.m31.M31;
const CM31 = core.fields.cm31.CM31;
const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointM31;

fn lift(a: CM31) QM31 {
    return .{ .c0 = a, .c1 = CM31.zero() };
}

fn fitAffine(points: [16]Point, values: [16]CM31) ![3]CM31 {
    var matrix: [3][4]CM31 = undefined;
    for (0..3) |row| {
        matrix[row] = .{
            CM31.one(), CM31.fromBase(points[row].x),
            CM31.fromBase(points[row].y), values[row],
        };
    }
    for (0..3) |col| {
        var pivot = col;
        while (pivot < 3 and matrix[pivot][col].isZero()) : (pivot += 1) {}
        if (pivot == 3) return error.SingularRows;
        std.mem.swap([4]CM31, &matrix[pivot], &matrix[col]);
        const inv = try matrix[col][col].inv();
        for (0..4) |j| matrix[col][j] = matrix[col][j].mul(inv);
        for (0..3) |row| {
            if (row == col) continue;
            const factor = matrix[row][col];
            for (0..4) |j| matrix[row][j] = matrix[row][j].sub(factor.mul(matrix[col][j]));
        }
    }
    return .{ matrix[0][3], matrix[1][3], matrix[2][3] };
}

test "Gate quotient-only x-square source escapes four slots" {
    const domain = core.poly.circle.CanonicCoset.new(4).circleDomain();
    const sample = core.circle.SECURE_FIELD_CIRCLE_GEN.mul(17);
    try std.testing.expect(sample.isOnCircle());
    try std.testing.expect(!sample.y.c1.isZero());
    const claim = sample.x.mul(sample.x);

    var points: [16]Point = undefined;
    var source: [16]M31 = undefined;
    for (0..16) |row| {
        const p = domain.at(core.utils.bitReverseIndex(row, 4));
        points[row] = p;
        source[row] = p.x.mul(p.x);
    }
    const evaluation = try prover_engine.poly.circle.CircleEvaluation.init(domain, &source);
    var source_poly = try prover_engine.poly.circle.poly.interpolateFromEvaluation(
        std.testing.allocator, evaluation,
    );
    defer source_poly.deinit(std.testing.allocator);
    try std.testing.expect(source_poly.evalAtPoint(sample).eql(claim));
    // The native interpolation is exactly (slot_0 + slot_4)/2, so slot 4
    // lies outside the admitted four-coefficient source space.
    const half = M31.fromCanonical(1073741824);
    for (source_poly.coefficients(), 0..) |coefficient, index| {
        const expected = if (index == 0 or index == 4) half else M31.zero();
        try std.testing.expect(coefficient.eql(expected));
    }

    const x0 = sample.x.c0;
    const x1 = sample.x.c1;
    const y0 = sample.y.c0;
    const y1 = sample.y.c1;
    const line = try core.constraints.complexConjugateLineCoeffs(sample, claim, QM31.one());
    const scale = QM31.fromU32Unchecked(0, 0, 1, 0).mulCM31(y1.neg().add(y1.neg()));
    var own: [16]CM31 = undefined;
    for (points, 0..) |p, row| {
        const interpolation = claim.c0.add(claim.c1.mul(
            try CM31.fromBase(p.y).sub(y0).div(y1),
        ));
        const denominator = x0.sub(CM31.fromBase(p.x)).mul(y1)
            .sub(y0.sub(CM31.fromBase(p.y)).mul(x1));
        try std.testing.expect(!denominator.isZero());
        own[row] = try CM31.fromBase(source[row]).sub(interpolation).div(denominator);
        const native_numerator = line.c.mulM31(source[row])
            .sub(line.a.mulM31(p.y)).sub(line.b);
        const native_quotient = try native_numerator.div(lift(denominator));
        try std.testing.expect(native_quotient.eql(scale.mulCM31(own[row])));
    }
    const quotient = try fitAffine(points, own);
    const expected_quotient = [3]CM31{
        CM31.fromU32Unchecked(1777893936, 1429241158),
        CM31.fromU32Unchecked(1978046109, 742432526),
        CM31.fromU32Unchecked(1340263512, 1618953911),
    };
    for (quotient, expected_quotient) |actual, expected| {
        try std.testing.expect(actual.eql(expected));
    }
    // This is exactly the fifth-coordinate obstruction proved in Lean.
    const edge_correction = y1.mul(quotient[1]).add(x1.mul(quotient[2]));
    try std.testing.expect(!edge_correction.isZero());
    for (points, own) |p, value| {
        const expected = quotient[0].add(quotient[1].mulM31(p.x))
            .add(quotient[2].mulM31(p.y));
        try std.testing.expect(value.eql(expected));
    }
}
