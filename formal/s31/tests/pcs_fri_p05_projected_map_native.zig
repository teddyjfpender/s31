//! Source-bound finite differential for the accepted sparse Gate OOD map.
//! This checks captured claim coordinates, native mask offsets, prover point
//! normalization, and legacy periodicity. It proves no sampling law or degree bound.
const std = @import("std");
const core = @import("stwo_core");
const geometry = @import("stwo_cairo").witness.resident_geometry;
const point_eval = @import("stwo_point_eval");

const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;
const TreeVec = core.pcs.TreeVec;

const Column = struct {
    root_index: usize,
    column_index: usize,
    extended_log_size: u32,
    ood_claims: usize,
    first_claim_index: usize,
};
const Claim = struct {
    root_index: usize,
    column_index: usize,
    sample_index: usize,
    extended_log_size: u32,
    point_x_limbs: [4]u32,
    point_y_limbs: [4]u32,
    value_limbs: [4]u32,
};
const Evidence = struct {
    package_checks: struct { key_sha256: []const u8, proof_sha256: []const u8 },
    accepted_ood_claim_map_sha256: []const u8,
    accepted_capture: struct {
        composition_log_degree_bound: u32,
        composition_log_split: u32,
        trace_lifting_log_size: u32,
        oods_seed_limbs: [4]u32,
        oods_point_x_limbs: [4]u32,
        oods_point_y_limbs: [4]u32,
        root_columns: [4]usize,
        root_ood_claims: [4]usize,
        columns: []Column,
        claims: []Claim,
    },
    native_to_paper_batch_width_M: ?usize,
    native_proven_security_bits: ?u32,
    proven_release_admissible: bool,
};

fn field(limbs: [4]u32) QM31 {
    return QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);
}

fn point(x: [4]u32, y: [4]u32) Point {
    return .{ .x = field(x), .y = field(y) };
}

fn circleDouble(p: Point) Point {
    return .{
        .x = p.x.square().sub(p.y.square()),
        .y = p.x.mul(p.y).add(p.x.mul(p.y)),
    };
}

fn independentProjection(p: Point, folds: u32) Point {
    var result = p;
    for (0..folds) |_| result = circleDouble(result);
    return result;
}

fn checkedColumn(
    allocator: std.mem.Allocator,
    column: Column,
    claims: []const Claim,
    base: Point,
    step: Point,
) !void {
    if (claims.len != column.ood_claims or (claims.len != 1 and claims.len != 2))
        return error.ClaimShapeMismatch;
    var offsets = std.ArrayList(i32).empty;
    defer offsets.deinit(allocator);
    if (claims.len == 2) try offsets.append(allocator, -1);
    try offsets.append(allocator, 0);
    // This is the production Cairo mask geometry primitive used by the
    // selected verifier, with the accepted AIR instruction offsets.
    const columns = try geometry.pointsFromOffsets(allocator, &[_]std.ArrayList(i32){offsets}, base, step);
    defer geometry.freePointTree(allocator, columns);
    for (claims, columns[0], 0..) |claim, expected, sample| {
        if (claim.root_index != column.root_index or
            claim.column_index != column.column_index or
            claim.sample_index != sample or
            claim.extended_log_size != column.extended_log_size or
            !point(claim.point_x_limbs, claim.point_y_limbs).eql(expected))
            return error.ClaimPointMismatch;
    }
}

fn checkPeriodicity(
    allocator: std.mem.Allocator,
    column: Column,
    claims: []const Claim,
    lifting_log: u32,
) !void {
    var points = [_]Point{
        point(claims[0].point_x_limbs, claims[0].point_y_limbs),
        point(claims[1].point_x_limbs, claims[1].point_y_limbs),
    };
    var values = [_]QM31{ field(claims[0].value_limbs), field(claims[1].value_limbs) };
    var point_cols = [_][]Point{points[0..]};
    var point_trees = [_][][]Point{point_cols[0..]};
    var value_cols = [_][]QM31{values[0..]};
    var value_trees = [_][][]QM31{value_cols[0..]};
    var logs = [_]u32{column.extended_log_size};
    var log_trees = [_][]u32{logs[0..]};
    const lambda = QM31.fromU32Unchecked(7, 0, 0, 0);
    var expanded = try core.pcs.quotients.buildSamplesWithRandomnessAndPeriodicity(
        allocator,
        TreeVec([][]Point).initOwned(point_trees[0..]),
        TreeVec([][]QM31).initOwned(value_trees[0..]),
        TreeVec([]u32).initOwned(log_trees[0..]),
        lifting_log,
        lambda,
    );
    defer expanded.deinitDeep(allocator);
    const out = expanded.items[0][0];
    if (out.len != 3) return error.PeriodicityShapeMismatch;
    const period_m31 = core.poly.circle.canonic.CanonicCoset.new(lifting_log)
        .step().repeatedDouble(column.extended_log_size);
    const period = Point{ .x = QM31.fromBase(period_m31.x), .y = QM31.fromBase(period_m31.y) };
    const expected = points[1].add(period);
    if (!out[0].point.eql(expected) or !out[0].value.eql(values[1]) or
        !out[1].point.eql(points[0]) or !out[1].value.eql(values[0]) or
        !out[2].point.eql(points[1]) or !out[2].value.eql(values[1]) or
        !out[0].random_coeff.eql(QM31.one()) or
        !out[1].random_coeff.eql(lambda) or
        !out[2].random_coeff.eql(lambda.mul(lambda)))
        return error.PeriodicityMismatch;
    const folds = lifting_log - column.extended_log_size;
    const normalized = independentProjection(expected, folds);
    if (!normalized.eql(point_eval.repeatedDoubleOnCircleQM31(expected, folds)))
        return error.PeriodicityProjectionMismatch;
    // The lifted periodic point is a distinct h11/h5 sample, but its
    // h-local normalization aliases the base explicit claim.
    if (!normalized.eql(independentProjection(points[1], folds)))
        return error.PeriodicityProjectionMismatch;
    if (column.extended_log_size == lifting_log) {
        if (!expected.eql(points[1])) return error.PeriodicityMismatch;
    } else if (expected.eql(points[1])) return error.PeriodicityMismatch;
}

test "P05 accepted sparse OOD points refine native mask and prover projections" {
    const allocator = std.testing.allocator;
    const json = try std.fs.cwd().readFileAlloc(allocator, "design/s31/security/evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json", 1 << 20);
    defer allocator.free(json);
    var parsed = try std.json.parseFromSlice(Evidence, allocator, json, .{ .ignore_unknown_fields = true });
    defer parsed.deinit();
    const evidence = parsed.value;
    try std.testing.expectEqualStrings("7d4cdaab4e446aaa2c357e28f077e469412f45a17c660e8d4434cca216dccfc7", evidence.package_checks.key_sha256);
    try std.testing.expectEqualStrings("04eaca23d8a6c7fc977b24a3d925aaabcbb727fa4fa30f30c81864e24a158e39", evidence.package_checks.proof_sha256);
    try std.testing.expectEqualStrings("d0dfd3b36e3abc181e90ee0456ca2760602636fc5c2c378572d84b99e26ed5f5", evidence.accepted_ood_claim_map_sha256);
    try std.testing.expect(evidence.native_to_paper_batch_width_M == null);
    try std.testing.expect(evidence.native_proven_security_bits == null);
    try std.testing.expect(!evidence.proven_release_admissible);
    const capture = evidence.accepted_capture;
    try std.testing.expectEqual(@as(usize, 61), capture.columns.len);
    try std.testing.expectEqual(@as(usize, 73), capture.claims.len);
    try std.testing.expectEqualSlices(usize, &.{ 12, 17, 24, 8 }, &capture.root_columns);
    try std.testing.expectEqualSlices(usize, &.{ 12, 17, 36, 8 }, &capture.root_ood_claims);
    try std.testing.expectEqual(@as(u32, 17), capture.trace_lifting_log_size);
    const mask_log = core.verifier_types.compositionMaskLogSize(
        capture.composition_log_degree_bound,
        capture.composition_log_split,
    ) orelse return error.InvalidMaskLog;
    try std.testing.expectEqual(@as(u32, 16), mask_log);
    const base = try core.circle.secureFieldPointFromRandomSeedChecked(field(capture.oods_seed_limbs));
    try std.testing.expect(base.eql(point(capture.oods_point_x_limbs, capture.oods_point_y_limbs)));
    const step_m31 = core.poly.circle.canonic.CanonicCoset.new(mask_log).step();
    const step = Point{ .x = QM31.fromBase(step_m31.x), .y = QM31.fromBase(step_m31.y) };
    var claim_cursor: usize = 0;
    var counts = [_]usize{ 0, 0, 0 };
    var shifted = [_]usize{ 0, 0, 0 };
    var root_columns = [_]usize{ 0, 0, 0, 0 };
    var root_claims = [_]usize{ 0, 0, 0, 0 };
    for (capture.columns) |column| {
        try std.testing.expectEqual(claim_cursor, column.first_claim_index);
        if (column.root_index >= root_columns.len) return error.InvalidRoot;
        try std.testing.expectEqual(root_columns[column.root_index], column.column_index);
        root_columns[column.root_index] += 1;
        root_claims[column.root_index] += column.ood_claims;
        const should_shift = column.root_index == 2 and
            ((column.column_index >= 4 and column.column_index <= 7) or
                (column.column_index >= 16 and column.column_index <= 23));
        try std.testing.expectEqual(@as(usize, if (should_shift) 2 else 1), column.ood_claims);
        const bucket: usize = switch (column.extended_log_size) {
            17 => 0,
            11 => 1,
            5 => 2,
            else => return error.InvalidHeight,
        };
        const end = claim_cursor + column.ood_claims;
        if (end > capture.claims.len) return error.ClaimShapeMismatch;
        const claims = capture.claims[claim_cursor..end];
        try checkedColumn(allocator, column, claims, base, step);
        counts[bucket] += claims.len;
        if (claims.len == 2) {
            shifted[bucket] += 1;
            try checkPeriodicity(allocator, column, claims, capture.trace_lifting_log_size);
        }
        for (claims) |claim| {
            const p = point(claim.point_x_limbs, claim.point_y_limbs);
            const folds = capture.trace_lifting_log_size - column.extended_log_size;
            const native = p.repeatedDouble(folds);
            try std.testing.expect(native.eql(independentProjection(p, folds)));
            try std.testing.expect(native.eql(point_eval.repeatedDoubleOnCircleQM31(p, folds)));
            try std.testing.expect(native.isOnCircle());
            _ = try core.constraints.complexConjugateLineCoeffs(native, field(claim.value_limbs), QM31.one());
        }
        claim_cursor = end;
    }
    try std.testing.expectEqual(capture.claims.len, claim_cursor);
    try std.testing.expectEqualSlices(usize, &capture.root_columns, &root_columns);
    try std.testing.expectEqualSlices(usize, &capture.root_ood_claims, &root_claims);
    try std.testing.expectEqualSlices(usize, &.{ 18, 32, 23 }, &counts);
    try std.testing.expectEqualSlices(usize, &.{ 4, 4, 4 }, &shifted);

    // Fail-closed finite controls for the exact accepted capture and order.
    const first = capture.columns[0];
    const first_claim = capture.claims[first.first_claim_index];
    var bad_claim = first_claim;
    bad_claim.point_x_limbs[0] +%= 1;
    try std.testing.expectError(error.ClaimPointMismatch, checkedColumn(allocator, first, &.{bad_claim}, base, step));
    var bad_height = first;
    bad_height.extended_log_size = 11;
    try std.testing.expectError(error.ClaimPointMismatch, checkedColumn(allocator, bad_height, &.{first_claim}, base, step));
    try std.testing.expectError(error.ClaimPointMismatch, checkedColumn(allocator, first, &.{first_claim}, base.double(), step));
    for (capture.columns) |column| {
        if (column.ood_claims != 2) continue;
        const pair = capture.claims[column.first_claim_index..][0..2];
        try std.testing.expectError(error.ClaimPointMismatch, checkedColumn(allocator, column, &.{ pair[1], pair[0] }, base, step));
        const wrong_step_m31 = core.poly.circle.canonic.CanonicCoset.new(mask_log - 1).step();
        const wrong_step = Point{ .x = QM31.fromBase(wrong_step_m31.x), .y = QM31.fromBase(wrong_step_m31.y) };
        try std.testing.expectError(error.ClaimPointMismatch, checkedColumn(allocator, column, pair, base, wrong_step));
        break;
    }
}
