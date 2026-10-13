//! Raw DEEP admission controls on a constant-polynomial PCS row fixture.
const std = @import("std");
const core = @import("stwo_core");
const admission = @import("deep_capture_admission");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;

test "FRI raw DEEP custody rejects changed capture fields" {
    const allocator = std.testing.allocator;
    var column_logs = [_]u32{2};
    var logs = [_][]u32{&column_logs};
    var point = [_]Point{core.circle.SECURE_FIELD_CIRCLE_GEN.mul(17)};
    var columns = [_][]Point{&point};
    var points = [_][][]Point{&columns};
    var samples = [_]QM31{QM31.fromBase(M31.fromCanonical(7))};
    const raw = [_]usize{ 0, 1, 0 };
    var opened = [_]M31{M31.fromCanonical(7)} ** raw.len;
    var deep = [_]QM31{QM31.zero()} ** raw.len;
    const alpha = QM31.fromU32Unchecked(2, 3, 5, 7);

    try admission.validate(allocator, 2, &raw, &logs, &points,
        &samples, &opened, &deep, alpha);

    deep[2] = QM31.one();
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, &opened, &deep, alpha));
    deep[2] = QM31.zero();

    opened[2] = M31.fromCanonical(8);
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, &opened, &deep, alpha));
    opened[2] = M31.fromCanonical(7);

    samples[0] = QM31.fromBase(M31.fromCanonical(8));
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, &opened, &deep, alpha));
    samples[0] = QM31.fromBase(M31.fromCanonical(7));

    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, opened[0..2], &deep, alpha));
}

test "FRI raw DEEP custody preserves unequal rows and duplicate slots" {
    const allocator = std.testing.allocator;
    var column_logs = [_]u32{ 2, 2 };
    var logs = [_][]u32{&column_logs};
    var point0 = [_]Point{core.circle.SECURE_FIELD_CIRCLE_GEN.mul(17)};
    var point1 = [_]Point{core.circle.SECURE_FIELD_CIRCLE_GEN.mul(21)};
    var columns = [_][]Point{ &point0, &point1 };
    var points = [_][][]Point{&columns};
    var samples = [_]QM31{
        QM31.fromBase(M31.fromCanonical(7)),
        QM31.fromBase(M31.fromCanonical(9)),
    };
    const raw = [_]usize{ 2, 0, 2 };
    var opened = [_]M31{
        M31.fromCanonical(7), M31.fromCanonical(8), M31.fromCanonical(7),
        M31.fromCanonical(10), M31.fromCanonical(11), M31.fromCanonical(10),
    };
    const alpha = QM31.fromU32Unchecked(2, 3, 5, 7);
    var sample_columns = [_][]QM31{ samples[0..1], samples[1..2] };
    var sample_trees = [_][][]QM31{&sample_columns};
    var query_columns = [_][]M31{ opened[0..3], opened[3..6] };
    var query_trees = [_][][]M31{&query_columns};
    const expected = try core.pcs.quotients.friAnswers(
        allocator,
        core.pcs.TreeVec([]u32).initOwned(&logs),
        core.pcs.TreeVec([][]Point).initOwned(&points),
        core.pcs.TreeVec([][]QM31).initOwned(&sample_trees),
        alpha,
        &raw,
        core.pcs.TreeVec([][]M31).initOwned(&query_trees),
        2,
    );
    defer allocator.free(expected);
    try std.testing.expect(expected[0].eql(expected[2]));
    try std.testing.expect(!expected[0].eql(expected[1]));
    try admission.validate(allocator, 2, &raw, &logs, &points,
        &samples, &opened, expected, alpha);

    var changed_raw = raw;
    changed_raw[2] = 1;
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &changed_raw, &logs, &points,
            &samples, &opened, expected, alpha));

    const first = expected[0];
    expected[0] = expected[1];
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, &opened, expected, alpha));
    expected[0] = first;

    const opening = opened[5];
    opened[5] = M31.fromCanonical(12);
    try std.testing.expectError(error.InvalidDeepCapture,
        admission.validate(allocator, 2, &raw, &logs, &points,
            &samples, &opened, expected, alpha));
    opened[5] = opening;
}
