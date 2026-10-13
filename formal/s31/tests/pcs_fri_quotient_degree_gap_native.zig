//! Executable P05 inference counterexample using the pinned native row quotient.
//!
//! This constructs values, not a Merkle/FRI proof. It demonstrates that the
//! native row quotient being in L'_(N/2) does not imply its original M31
//! column is in L'_(N/2), for several actual canonical circle domains.
//! It does not show that a forged proof is accepted.

const std = @import("std");
const core = @import("stwo_core");

const M31 = core.fields.m31.M31;
const CM31 = core.fields.cm31.CM31;
const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;
const TreeVec = core.pcs.TreeVec;

fn lift(value: CM31) QM31 {
    return .{ .c0 = value, .c1 = CM31.zero() };
}

const Line = struct {
    a: CM31,
    b: CM31,
    c: CM31,

    fn fromSample(sample: Point) Line {
        const prx = sample.x.c0;
        const pry = sample.y.c0;
        const pix = sample.x.c1;
        const piy = sample.y.c1;
        return .{
            .a = prx.mul(piy).sub(pry.mul(pix)),
            .b = piy.neg(),
            .c = pix,
        };
    }

    fn at(self: Line, x: M31, y: M31) CM31 {
        return self.a.add(self.b.mulM31(x)).add(self.c.mulM31(y));
    }

    fn atSecure(self: Line, point: Point) QM31 {
        return lift(self.a).add(point.x.mulCM31(self.b)).add(point.y.mulCM31(self.c));
    }

    /// In `D * conjugate(D)` reduce `y²` to `1-x²`. After multiplying by
    /// x^(N/4-2), this becomes the x^(N/4) coefficient outside L'_(N/2).
    fn normX2Coeff(self: Line) CM31 {
        return self.b.mul(self.b.complexConjugate())
            .sub(self.c.mul(self.c.complexConjugate()));
    }
};

fn fromBase(comptime F: type, value: M31) F {
    if (F == M31) return value;
    if (F == QM31) return QM31.fromBase(value);
    @compileError("unsupported field in degree witness");
}

/// Independently test L'_(N/2) = span{x^j, y*x^j | 0 <= j < N/4}
/// on the N-point canonical domain. An inconsistent augmented system rejects.
fn inLPrime(
    comptime F: type,
    comptime log_rows: u32,
    points: [@as(usize, 1) << @intCast(log_rows)]core.circle.CirclePointM31,
    values: [@as(usize, 1) << @intCast(log_rows)]F,
) !bool {
    const n: usize = @as(usize, 1) << @intCast(log_rows);
    const bound = n / 2;
    var rows: [n][bound + 1]F = undefined;
    for (points, values, 0..) |point, value, i| {
        var power = M31.one();
        for (0..bound / 2) |j| {
            rows[i][2 * j] = fromBase(F, power);
            rows[i][2 * j + 1] = fromBase(F, power.mul(point.y));
            power = power.mul(point.x);
        }
        rows[i][bound] = value;
    }
    var pivot_row: usize = 0;
    for (0..bound) |col| {
        var found = pivot_row;
        while (found < n and rows[found][col].isZero()) : (found += 1) {}
        if (found == n) continue;
        std.mem.swap([bound + 1]F, &rows[pivot_row], &rows[found]);
        const inverse = try rows[pivot_row][col].inv();
        for (0..bound + 1) |j| rows[pivot_row][j] = rows[pivot_row][j].mul(inverse);
        for (0..n) |i| {
            if (i == pivot_row) continue;
            const factor = rows[i][col];
            for (0..bound + 1) |j| {
                rows[i][j] = rows[i][j].sub(factor.mul(rows[pivot_row][j]));
            }
        }
        pivot_row += 1;
    }
    for (rows) |row| {
        var zero_left = true;
        for (row[0..bound]) |entry| zero_left = zero_left and entry.isZero();
        if (zero_left and !row[bound].isZero()) return false;
    }
    return true;
}

fn checkDomain(comptime log_rows: u32) !void {
    const n: usize = @as(usize, 1) << @intCast(log_rows);
    const allocator = std.testing.allocator;
    const sample = core.circle.SECURE_FIELD_CIRCLE_GEN.mul(17);
    const line = Line.fromSample(sample);
    try std.testing.expect(line.atSecure(sample).isZero());
    try std.testing.expect(!line.normX2Coeff().isZero());
    _ = try line.normX2Coeff().tryIntoM31();

    const domain = core.poly.circle.CanonicCoset.new(log_rows).circleDomain();
    var points: [n]core.circle.CirclePointM31 = undefined;
    var original: [n]M31 = undefined;
    var expected_quotient: [n]QM31 = undefined;
    const alpha = QM31.fromU32Unchecked(2, 3, 5, 7);
    // The first (and only) sample receives random_coeff^0 = 1.
    const line_coeff = try core.constraints.complexConjugateLineCoeffs(
        sample,
        QM31.zero(),
        QM31.one(),
    );
    for (0..n) |i| {
        const point = domain.at(core.utils.bitReverseIndex(i, log_rows));
        points[i] = point;
        const denominator = line.at(point.x, point.y);
        try std.testing.expect(!denominator.isZero());
        var monomial = M31.one();
        for (0..n / 4 - 2) |_| monomial = monomial.mul(point.x);
        original[i] = (try denominator.mul(denominator.complexConjugate())
            .tryIntoM31()).mul(monomial);
        expected_quotient[i] = line_coeff.c
            .mulCM31(denominator.complexConjugate()).mulM31(monomial);
    }
    try std.testing.expect(!(try inLPrime(M31, log_rows, points, original)));

    // A nominal N/2-row source column is lifted to N verifier query rows.
    var logs_one = [_]u32{log_rows - 1};
    var logs = [_][]u32{&logs_one};
    var one_sample = [_]Point{sample};
    var point_columns = [_][]Point{&one_sample};
    var point_trees = [_][][]Point{&point_columns};
    var one_value = [_]QM31{QM31.zero()};
    var value_columns = [_][]QM31{&one_value};
    var value_trees = [_][][]QM31{&value_columns};
    var query_columns = [_][]M31{&original};
    var query_trees = [_][][]M31{&query_columns};
    var query_positions: [n]usize = undefined;
    for (0..n) |i| query_positions[i] = i;
    const native_quotient = try core.pcs.quotients.friAnswers(
        allocator,
        TreeVec([]u32).initOwned(&logs),
        TreeVec([][]Point).initOwned(&point_trees),
        TreeVec([][]QM31).initOwned(&value_trees),
        alpha,
        &query_positions,
        TreeVec([][]M31).initOwned(&query_trees),
        log_rows,
    );
    defer allocator.free(native_quotient);
    for (native_quotient, expected_quotient) |actual, expected| {
        try std.testing.expect(actual.eql(expected));
    }
    var quotient_rows: [n]QM31 = undefined;
    for (native_quotient, 0..) |value, i| quotient_rows[i] = value;
    try std.testing.expect(try inLPrime(QM31, log_rows, points, quotient_rows));
    // Expected quotient is c * conjugate(D) * x^(N/4-2), inside L'_(N/2).
}

test "P05 native quotient degree does not imply original degree across domains" {
    inline for (.{ 3, 4, 5 }) |log_rows| try checkDomain(log_rows);
}
