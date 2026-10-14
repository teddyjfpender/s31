//! A raw OOD point can pass the native two-point line guard while its
//! lower-height projection cannot define that same line.
const std = @import("std");
const core = @import("stwo_core");

test "P05 projected OOD guard rejects a raw-admissible lower-height point" {
    const q: u128 = core.fields.m31.Modulus;
    const index = (q * q + 1) / 2;
    const raw = core.circle.secureFieldPoint(index);
    try std.testing.expect(raw.isOnCircle());
    try std.testing.expect(raw.x.c0.isZero());
    try std.testing.expect(raw.y.c0.isZero());
    try std.testing.expect(!raw.y.eql(raw.y.complexConjugate()));
    const seed = try raw.y.div(core.fields.qm31.QM31.one().add(raw.x));
    const recovered = try core.circle.secureFieldPointFromRandomSeedChecked(seed);
    try std.testing.expect(raw.eql(recovered));
    _ = try core.constraints.complexConjugateLineCoeffs(
        raw,
        core.fields.qm31.QM31.one(),
        core.fields.qm31.QM31.one(),
    );

    for ([_]u32{ 1, 6, 12 }) |fold_count| {
        const projected = raw.repeatedDouble(fold_count);
        try std.testing.expect(projected.isOnCircle());
        try std.testing.expect(projected.y.eql(projected.y.complexConjugate()));
        try std.testing.expectError(
            error.DegenerateLine,
            core.constraints.complexConjugateLineCoeffs(
                projected,
                core.fields.qm31.QM31.one(),
                core.fields.qm31.QM31.one(),
            ),
        );
    }

    // The actual native quotient-answer entry point also rejects the h11
    // projected point before accepting a queried quotient row.
    const projected = raw.repeatedDouble(6);
    var logs_data = [_]u32{11};
    var logs = [_][]u32{logs_data[0..]};
    var points_data = [_]core.circle.CirclePointQM31{projected};
    var points_cols = [_][]core.circle.CirclePointQM31{points_data[0..]};
    var points_trees = [_][][]core.circle.CirclePointQM31{points_cols[0..]};
    var values_data = [_]core.fields.qm31.QM31{core.fields.qm31.QM31.one()};
    var values_cols = [_][]core.fields.qm31.QM31{values_data[0..]};
    var values_trees = [_][][]core.fields.qm31.QM31{values_cols[0..]};
    var queried_data = [_]core.fields.m31.M31{core.fields.m31.M31.one()};
    var queried_cols = [_][]core.fields.m31.M31{queried_data[0..]};
    var queried_trees = [_][][]core.fields.m31.M31{queried_cols[0..]};
    try std.testing.expectError(error.DegenerateLine, core.pcs.quotients.friAnswers(
        std.testing.allocator,
        core.pcs.TreeVec([]u32).initOwned(logs[0..]),
        core.pcs.TreeVec([][]core.circle.CirclePointQM31).initOwned(points_trees[0..]),
        core.pcs.TreeVec([][]core.fields.qm31.QM31).initOwned(values_trees[0..]),
        core.fields.qm31.QM31.one(),
        &[_]usize{0},
        core.pcs.TreeVec([][]core.fields.m31.M31).initOwned(queried_trees[0..]),
        17,
    ));
}
