const std = @import("std");
const core = @import("stwo_core");
const circle_poly = @import("stwo_prover").poly.circle.poly;

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

fn independentDot(coefficients: []const M31, factors: []const QM31) QM31 {
    var result = QM31.zero();
    for (coefficients, 0..) |coefficient, index| {
        var weight = QM31.one();
        for (0..4) |bit| {
            if (((index >> @intCast(bit)) & 1) != 0) weight = weight.mul(factors[bit]);
        }
        result = result.add(weight.mulM31(coefficient));
    }
    return result;
}

test "P05 h5 five-column native plan executes packed group and scalar tail" {
    var words: [5][16]M31 = undefined;
    var polys: [5]circle_poly.CircleCoefficients = undefined;
    var outputs: [5][2]QM31 = undefined;
    var output_views: [5][]QM31 = undefined;
    const flat_factors = [_]QM31{
        QM31.fromBase(M31.fromCanonical(2)),
        QM31.fromBase(M31.fromCanonical(3)),
        QM31.fromBase(M31.fromCanonical(5)),
        QM31.fromBase(M31.fromCanonical(7)),
        QM31.fromBase(M31.fromCanonical(11)),
        QM31.fromBase(M31.fromCanonical(13)),
        QM31.fromBase(M31.fromCanonical(17)),
        QM31.fromBase(M31.fromCanonical(19)),
    };
    for (&words, 0..) |*word, column| {
        for (word, 0..) |*coefficient, index| {
            coefficient.* = M31.fromCanonical(@intCast((column + 1) * (index + 3)));
        }
        polys[column] = try circle_poly.CircleCoefficients.initBorrowed(word);
        output_views[column] = &outputs[column];
    }
    var basis_scratch: [32]QM31 = undefined;
    circle_poly.CircleCoefficients.evalManyAtPointsWithFlatFactors(
        &polys,
        &flat_factors,
        &output_views,
        &basis_scratch,
    );
    for (&words, 0..) |*word, column| {
        for (0..2) |point| {
            const point_factors = flat_factors[point * 4 ..][0..4];
            try std.testing.expect(outputs[column][point].eql(independentDot(word, point_factors)));
        }
    }
    try std.testing.expectError(
        circle_poly.PolyError.InvalidLength,
        circle_poly.CircleCoefficients.initBorrowed(words[0][0..15]),
    );
}
