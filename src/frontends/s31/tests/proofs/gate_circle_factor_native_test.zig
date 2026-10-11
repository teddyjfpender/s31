//! Independent QM31 recurrence check for the selected Gate composition factor.
//! This exercises the native circle implementation, not PCS authentication.
const std = @import("std");
const circle = @import("stwo_circle");
const QM31 = @TypeOf(circle.SECURE_FIELD_CIRCLE_GEN.x);

test "Gate OODS seed point and repeated-double x recurrence" {
    const seeds = [_]QM31{
        QM31.zero(),
        QM31.one(),
        QM31.fromU32Unchecked(2, 0, 0, 0),
        QM31.fromU32Unchecked(3, 5, 7, 11),
    };
    for (seeds) |seed| {
        const square = seed.mul(seed);
        const inverse = try square.add(QM31.one()).inv();
        const point = try circle.secureFieldPointFromRandomSeedChecked(seed);
        try std.testing.expect(point.x.eql(QM31.one().sub(square).mul(inverse)));
        try std.testing.expect(point.y.eql(seed.add(seed).mul(inverse)));
        try std.testing.expect(point.isOnCircle());

        var expected_x = point.x;
        for (0..12) |n| {
            const actual = point.repeatedDouble(@intCast(n)).x;
            try std.testing.expect(actual.eql(expected_x));
            const square_x = expected_x.mul(expected_x);
            expected_x = square_x.add(square_x).sub(QM31.one());
        }
    }
}

test "Gate OODS seed rational-map exceptional value is rejected" {
    const square_root_of_minus_one = QM31.fromU32Unchecked(0, 1, 0, 0);
    try std.testing.expectError(error.DivisionByZero,
        circle.secureFieldPointFromRandomSeedChecked(square_root_of_minus_one));
}
