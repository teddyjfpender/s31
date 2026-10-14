const std = @import("std");
const core = @import("stwo_core");
const point_eval = @import("point_eval");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const modulus = core.fields.m31.Modulus;

const H5 = struct {
    pub const factor_count = 4;
    pub const coefficient_count = 16;

    pub fn checkedEval(
        coefficients: []const M31,
        factors: []const QM31,
        basis: []QM31,
    ) error{ShapeMismatch}!QM31 {
        if (coefficients.len != coefficient_count or
            factors.len != factor_count or
            basis.len != coefficient_count) return error.ShapeMismatch;
        point_eval.fillSubsetProductBasis(factors, basis);
        return point_eval.evalWithSubsetProductBasis(coefficients, basis);
    }
};

fn independentBasis(factors: []const QM31, index: usize) QM31 {
    var value = QM31.one();
    for (0..H5.factor_count) |bit| {
        if (((index >> @intCast(bit)) & 1) != 0) {
            value = value.mul(factors[bit]);
        }
    }
    return value;
}

fn independentDot(coefficients: []const M31, factors: []const QM31) QM31 {
    var value = QM31.zero();
    for (coefficients, 0..) |coefficient, index| {
        value = value.add(independentBasis(factors, index).mulM31(coefficient));
    }
    return value;
}

test "P05 h5 native subset basis and scalar dot refine all 16 source slots" {
    const expected_previous = [_]usize{ 0, 0, 0, 2, 0, 4, 4, 6, 0, 8, 8, 10, 8, 12, 12, 14 };
    const expected_factor_index = [_]usize{ 0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0 };
    for (1..H5.coefficient_count) |index| {
        try std.testing.expectEqual(expected_previous[index], index & (index - 1));
        try std.testing.expectEqual(expected_factor_index[index], @as(usize, @intCast(@ctz(index))));
        try std.testing.expect(expected_previous[index] < index);
    }

    var rng = std.Random.DefaultPrng.init(0x5035_16b1_5d07);
    const random = rng.random();
    for (0..64) |case_index| {
        var factors: [H5.factor_count]QM31 = undefined;
        var coefficients: [H5.coefficient_count]M31 = undefined;
        for (&factors) |*factor| {
            var limbs: [4]M31 = undefined;
            for (&limbs) |*limb| limb.* = M31.fromCanonical(random.uintLessThan(u32, modulus));
            factor.* = QM31.fromM31Array(limbs);
        }
        for (&coefficients) |*coefficient| {
            coefficient.* = M31.fromCanonical(if (case_index == 0)
                modulus - 1
            else
                random.uintLessThan(u32, modulus));
        }
        var basis: [H5.coefficient_count]QM31 = undefined;
        const actual = try H5.checkedEval(&coefficients, &factors, &basis);
        for (basis, 0..) |entry, index| {
            try std.testing.expect(entry.eql(independentBasis(&factors, index)));
        }
        try std.testing.expect(actual.eql(independentDot(&coefficients, &factors)));
    }
}

test "P05 h5 candidate boundary rejects bad lengths and detects bit-order mutation" {
    const zero = M31.zero();
    const one = M31.one();
    var coefficients = [_]M31{zero} ** H5.coefficient_count;
    coefficients[1] = one;
    const factors = [_]QM31{
        QM31.fromBase(M31.fromCanonical(2)),
        QM31.fromBase(M31.fromCanonical(3)),
        QM31.fromBase(M31.fromCanonical(5)),
        QM31.fromBase(M31.fromCanonical(7)),
    };
    var basis: [H5.coefficient_count]QM31 = undefined;
    try std.testing.expectError(error.ShapeMismatch, H5.checkedEval(coefficients[0..15], &factors, &basis));
    try std.testing.expectError(error.ShapeMismatch, H5.checkedEval(&coefficients, factors[0..3], &basis));
    try std.testing.expectError(error.ShapeMismatch, H5.checkedEval(&coefficients, &factors, basis[0..15]));
    const actual = try H5.checkedEval(&coefficients, &factors, &basis);
    try std.testing.expect(actual.eql(factors[0]));
    try std.testing.expect(!actual.eql(factors[1]));
}
