const std = @import("std");
const core = @import("stwo_core");
const point_eval = @import("point_eval");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const modulus = core.fields.m31.Modulus;
const pack_width = core.fields.m31.PACK_WIDTH;

fn checkedBasisAndDot(
    log_size: u32,
    coefficients: []const M31,
    factors: []const QM31,
    basis: []QM31,
) error{ShapeMismatch}!QM31 {
    if (log_size != 10 and log_size != 16) return error.ShapeMismatch;
    const length = @as(usize, 1) << @intCast(log_size);
    if (coefficients.len != length or factors.len != log_size or basis.len != length)
        return error.ShapeMismatch;
    point_eval.fillSubsetProductBasis(factors, basis);
    return point_eval.evalWithSubsetProductBasis(coefficients, basis);
}

fn referenceWeight(factors: []const QM31, index: usize) QM31 {
    var result = QM31.one();
    for (factors, 0..) |factor, bit| {
        if (((index >> @intCast(bit)) & 1) != 0) result = result.mul(factor);
    }
    return result;
}

fn referenceDot(coefficients: []const M31, factors: []const QM31) QM31 {
    var result = QM31.zero();
    for (coefficients, 0..) |coefficient, index| {
        result = result.add(referenceWeight(factors, index).mulM31(coefficient));
    }
    return result;
}

fn fillFactors(random: std.Random, factors: []QM31, case_index: usize) void {
    for (factors, 0..) |*factor, bit| {
        if (case_index == 0) {
            // Nonconstant base factors make bit-order errors visible.
            factor.* = QM31.fromBase(M31.fromCanonical(@intCast(bit + 2)));
        } else {
            var limbs: [4]M31 = undefined;
            for (&limbs) |*limb| limb.* = M31.fromCanonical(random.uintLessThan(u32, modulus));
            factor.* = QM31.fromM31Array(limbs);
        }
    }
}

test "P05 general native basis and scalar evaluator at accepted logs 10 and 16" {
    const allocator = std.testing.allocator;
    var rng = std.Random.DefaultPrng.init(0x5035_16b1_5106);
    const random = rng.random();
    for ([_]u32{ 10, 16 }) |log_size| {
        const length = @as(usize, 1) << @intCast(log_size);
        const coefficients = try allocator.alloc(M31, length);
        defer allocator.free(coefficients);
        const basis = try allocator.alloc(QM31, length);
        defer allocator.free(basis);
        var factor_storage: [16]QM31 = undefined;
        const factors = factor_storage[0..log_size];

        for (0..2) |case_index| {
            fillFactors(random, factors, case_index);
            for (coefficients) |*coefficient| {
                coefficient.* = M31.fromCanonical(if (case_index == 0)
                    modulus - 1
                else
                    random.uintLessThan(u32, modulus));
            }
            const actual = try checkedBasisAndDot(log_size, coefficients, factors, basis);
            for (basis, 0..) |cell, index| {
                if (index > 0) {
                    const previous = index & (index - 1);
                    const bit: usize = @intCast(@ctz(index));
                    const quotient = previous >> @intCast(bit + 1);
                    try std.testing.expect(previous < index);
                    try std.testing.expect(bit < log_size);
                    try std.testing.expect(quotient < (@as(usize, 1) << @intCast(log_size - bit - 1)));
                    try std.testing.expectEqual(previous, quotient << @intCast(bit + 1));
                    try std.testing.expectEqual(index, previous + (@as(usize, 1) << @intCast(bit)));
                    try std.testing.expect(cell.eql(basis[previous].mul(factors[bit])));
                }
                try std.testing.expect(cell.eql(referenceWeight(factors, index)));
            }
            const expected = referenceDot(coefficients, factors);
            try std.testing.expect(actual.eql(expected));
            try std.testing.expect(point_eval.evalAtPointIterative(coefficients, factors, log_size).eql(expected));

            if (log_size == 16) {
                var low: [1 << 10]QM31 = undefined;
                var high: [1 << 6]QM31 = undefined;
                point_eval.fillSubsetProductBasis(factors[0..10], &low);
                point_eval.fillSubsetProductBasis(factors[10..16], &high);
                try std.testing.expect(point_eval.evalWithSplitProductBasis(coefficients, &low, &high).eql(expected));
                for (basis, 0..) |cell, index| {
                    try std.testing.expect(cell.eql(low[index & 1023].mul(high[index >> 10])));
                }
            }
        }
    }
}

test "P05 general packed batch evaluators agree with independent words" {
    const allocator = std.testing.allocator;
    for ([_]u32{ 10, 16 }) |log_size| {
        const length = @as(usize, 1) << @intCast(log_size);
        const storage = try allocator.alloc(M31, pack_width * length);
        defer allocator.free(storage);
        const basis = try allocator.alloc(QM31, length);
        defer allocator.free(basis);
        var factor_storage: [16]QM31 = undefined;
        const factors = factor_storage[0..log_size];
        for (factors, 0..) |*factor, bit| {
            const limbs = [4]M31{
                M31.fromCanonical(@intCast(bit + 2)),
                M31.fromCanonical(@intCast(bit + 3)),
                M31.fromCanonical(@intCast(bit + 5)),
                M31.fromCanonical(@intCast(bit + 7)),
            };
            factor.* = QM31.fromM31Array(limbs);
        }
        point_eval.fillSubsetProductBasis(factors, basis);
        var columns: [pack_width][]const M31 = undefined;
        for (&columns, 0..) |*column, lane| {
            const word = storage[lane * length ..][0..length];
            for (word, 0..) |*coefficient, index| {
                coefficient.* = M31.fromCanonical(@intCast((lane + 1) * (index + 3) % modulus));
            }
            column.* = word;
        }
        const batched = point_eval.evalBatchWithSubsetProductBasis(columns, basis);
        for (columns, batched) |column, value| {
            try std.testing.expect(value.eql(referenceDot(column, factors)));
        }
        if (log_size == 16) {
            var low: [1 << 10]QM31 = undefined;
            var high: [1 << 6]QM31 = undefined;
            point_eval.fillSubsetProductBasis(factors[0..10], &low);
            point_eval.fillSubsetProductBasis(factors[10..16], &high);
            const split = point_eval.evalBatchWithSplitProductBasis(columns, &low, &high);
            for (columns, split) |column, value| {
                try std.testing.expect(value.eql(referenceDot(column, factors)));
            }
        }
    }
}

test "P05 general candidate boundary rejects lengths and detects a high-bit mutation" {
    const allocator = std.testing.allocator;
    const coefficients = try allocator.alloc(M31, 1 << 16);
    defer allocator.free(coefficients);
    const basis = try allocator.alloc(QM31, 1 << 16);
    defer allocator.free(basis);
    @memset(coefficients, M31.zero());
    coefficients[1 << 15] = M31.one();
    var factors: [16]QM31 = undefined;
    for (&factors, 0..) |*factor, bit| {
        factor.* = QM31.fromBase(M31.fromCanonical(@intCast(bit + 2)));
    }
    try std.testing.expectError(error.ShapeMismatch, checkedBasisAndDot(17, coefficients, &factors, basis));
    try std.testing.expectError(error.ShapeMismatch, checkedBasisAndDot(16, coefficients[0 .. (1 << 16) - 1], &factors, basis));
    try std.testing.expectError(error.ShapeMismatch, checkedBasisAndDot(16, coefficients, factors[0..15], basis));
    try std.testing.expectError(error.ShapeMismatch, checkedBasisAndDot(16, coefficients, &factors, basis[0 .. (1 << 16) - 1]));
    const actual = try checkedBasisAndDot(16, coefficients, &factors, basis);
    try std.testing.expect(actual.eql(factors[15]));
    try std.testing.expect(!actual.eql(factors[14]));
}
