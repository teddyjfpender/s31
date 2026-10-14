//! Finite Gate four-coefficient/two-point quotient check against the pinned
//! stwo-zig fields, circle domain, and conjugate-line numerator. This is not
//! an accepted CAS05 proof or a compiler-to-committed-column refinement.
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

fn sourceM31(c: [4]M31, x: M31, y: M31) M31 {
    return c[0].add(c[1].mul(y)).add(x.mul(c[2].add(c[3].mul(y))));
}

fn sourceQM31(c: [4]M31, x: QM31, y: QM31) QM31 {
    return QM31.fromBase(c[0]).add(y.mulM31(c[1]))
        .add(x.mul(QM31.fromBase(c[2]).add(y.mulM31(c[3]))));
}

fn rowQuotient(sample: core.circle.CirclePointQM31, value: QM31, p: Point, word: M31) !struct { own: CM31, scaled: QM31 } {
    const x0 = sample.x.c0;
    const x1 = sample.x.c1;
    const y0 = sample.y.c0;
    const y1 = sample.y.c1;
    if (y1.isZero()) return error.DegenerateLine;
    const interpolation = value.c0.add(value.c1.mul(try CM31.fromBase(p.y).sub(y0).div(y1)));
    const denominator = x0.sub(CM31.fromBase(p.x)).mul(y1)
        .sub(y0.sub(CM31.fromBase(p.y)).mul(x1));
    if (denominator.isZero()) return error.ZeroDenominator;
    const own = try CM31.fromBase(word).sub(interpolation).div(denominator);

    const coeffs = try core.constraints.complexConjugateLineCoeffs(sample, value, QM31.one());
    const numerator = coeffs.c.mulM31(word).sub(coeffs.a.mulM31(p.y)).sub(coeffs.b);
    const scaled = try numerator.div(lift(denominator));
    const u = QM31.fromU32Unchecked(0, 0, 1, 0);
    const factor = u.mulCM31(y1.neg().add(y1.neg()));
    try std.testing.expect(scaled.eql(factor.mulCM31(own)));
    return .{ .own = own, .scaled = scaled };
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

fn affineAt(coeffs: [3]CM31, p: Point) CM31 {
    return coeffs[0].add(coeffs[1].mulM31(p.x)).add(coeffs[2].mulM31(p.y));
}

test "Gate four-slot correct two-point claim has radius-one own quotient on all 16 rows" {
    const coefficients = [4]M31{
        M31.fromCanonical(3), M31.fromCanonical(5),
        M31.fromCanonical(7), M31.fromCanonical(11),
    };
    const sample = core.circle.SECURE_FIELD_CIRCLE_GEN.mul(17);
    try std.testing.expect(sample.isOnCircle());
    try std.testing.expect(!sample.y.c1.isZero());
    const claim = sourceQM31(coefficients, sample.x, sample.y);
    const native_poly = try prover_engine.poly.circle.CircleCoefficients.initBorrowed(&coefficients);
    try std.testing.expect(native_poly.evalAtPoint(sample).eql(claim));
    const domain = core.poly.circle.CanonicCoset.new(4).circleDomain();
    const native_evaluation = try native_poly.evaluate(std.testing.allocator, domain);
    defer std.testing.allocator.free(@constCast(native_evaluation.values));
    var points: [16]Point = undefined;
    var own_rows: [16]CM31 = undefined;
    for (0..16) |row| {
        const p = domain.at(core.utils.bitReverseIndex(row, 4));
        const word = sourceM31(coefficients, p.x, p.y);
        try std.testing.expect(native_evaluation.values[row].eql(word));
        const answer = try rowQuotient(sample, claim, p, word);
        points[row] = p;
        own_rows[row] = answer.own;
    }
    const quotient = try fitAffine(points, own_rows);
    const expected_quotient = [3]CM31{
        CM31.fromU32Unchecked(163111111, 1581935086),
        CM31.fromU32Unchecked(289486897, 1518859802),
        CM31.fromU32Unchecked(283670729, 1724306845),
    };
    for (quotient, expected_quotient) |actual, expected| {
        try std.testing.expect(actual.eql(expected));
    }
    // A+B*x+C*y spans the Laurent support [-1,1].
    for (points, own_rows) |p, actual| {
        try std.testing.expect(actual.eql(affineAt(quotient, p)));
    }
    // The x coefficient is nonzero: this own quotient is outside the naive
    // two-slot circle span {1,y}. Radius one is necessary for this witness.
    try std.testing.expect(!quotient[1].isZero());
    const two_slot_y = try own_rows[1].sub(own_rows[0]).div(
        CM31.fromBase(points[1].y.sub(points[0].y)),
    );
    const two_slot_constant = own_rows[0].sub(two_slot_y.mulM31(points[0].y));
    var two_slot_fails = false;
    for (points, own_rows) |p, actual| {
        if (!actual.eql(two_slot_constant.add(two_slot_y.mulM31(p.y)))) two_slot_fails = true;
    }
    try std.testing.expect(two_slot_fails);

    // A wrong OOD value destroys the claimed degree implication on the same
    // sixteen source rows; fitting any three rows cannot fit the whole domain.
    const wrong_claim = claim.add(QM31.one());
    var wrong_rows: [16]CM31 = undefined;
    for (points, 0..) |p, row| {
        wrong_rows[row] = (try rowQuotient(sample, wrong_claim, p,
            sourceM31(coefficients, p.x, p.y))).own;
    }
    const wrong_fit = try fitAffine(points, wrong_rows);
    var found_failure = false;
    for (points, wrong_rows) |p, actual| {
        if (!actual.eql(affineAt(wrong_fit, p))) found_failure = true;
    }
    try std.testing.expect(found_failure);
}
