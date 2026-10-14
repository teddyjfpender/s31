//! Accepted sparse Gate claim points through the native coefficient plan.
//! This is a finite source-bound differential, not a verifier soundness proof.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover");

const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;
const plans = prover.pcs.sampled_coefficient_plans;

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
};
const Evidence = struct {
    package_checks: struct { key_sha256: []const u8, proof_sha256: []const u8 },
    accepted_ood_claim_map_sha256: []const u8,
    accepted_capture: struct {
        trace_lifting_log_size: u32,
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

fn claimPoint(claim: Claim) Point {
    return .{ .x = field(claim.point_x_limbs), .y = field(claim.point_y_limbs) };
}

fn independentDouble(point: Point) Point {
    const x = point.x;
    const y = point.y;
    return .{
        .x = x.square().add(x.square()).sub(QM31.one()),
        .y = x.mul(y).add(x.mul(y)),
    };
}

fn independentProjection(raw: Point, count: u32) Point {
    var point = raw;
    for (0..count) |_| point = independentDouble(point);
    return point;
}

fn auditPlan(
    plan: *const plans.CoefficientEvalPlan,
    raw_points: []const Point,
    coeff_log: u32,
    folds: u32,
) !void {
    if (plan.coeff_log_size != coeff_log or plan.fold_count != folds or
        plan.normalized_points.len != raw_points.len or
        plan.flat_factors.len != raw_points.len * coeff_log)
        return error.PlanShapeMismatch;
    for (raw_points, 0..) |raw, point_index| {
        const projected = independentProjection(raw, folds);
        if (!projected.isOnCircle() or !plan.normalized_points[point_index].eql(projected))
            return error.PlanPointMismatch;
        var x = projected.x;
        for (0..coeff_log) |bit| {
            const expected = if (bit == 0) projected.y else x;
            if (!plan.flat_factors[point_index * coeff_log + bit].eql(expected))
                return error.PlanFactorMismatch;
            if (bit != 0) x = x.square().add(x.square()).sub(QM31.one());
        }
    }
}

test "P05 accepted sparse OOD plans bind projected points to all factor slots" {
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
    try std.testing.expectEqual(@as(u32, 17), capture.trace_lifting_log_size);
    try std.testing.expectEqual(@as(usize, 61), capture.columns.len);
    try std.testing.expectEqual(@as(usize, 73), capture.claims.len);

    var claim_cursor: usize = 0;
    var columns_at_height = [_]usize{ 0, 0, 0 };
    var claims_at_height = [_]usize{ 0, 0, 0 };
    var ran_negative_controls = false;
    var plan_index = std.AutoHashMap(u64, usize).init(allocator);
    defer plan_index.deinit();
    var plan_entries = std.ArrayList(plans.CoefficientEvalPlan).empty;
    defer plans.deinitCoefficientEvalPlans(allocator, &plan_entries);
    for (capture.columns) |column| {
        try std.testing.expectEqual(claim_cursor, column.first_claim_index);
        const bucket: usize = switch (column.extended_log_size) {
            17 => 0,
            11 => 1,
            5 => 2,
            else => return error.InvalidHeight,
        };
        const coeff_log = column.extended_log_size - 1;
        const fold_count = capture.trace_lifting_log_size - column.extended_log_size;
        const end = claim_cursor + column.ood_claims;
        if (end > capture.claims.len or (column.ood_claims != 1 and column.ood_claims != 2))
            return error.ClaimShapeMismatch;
        const column_claims = capture.claims[claim_cursor..end];
        var raw_points: [2]Point = undefined;
        for (column_claims, 0..) |claim, sample| {
            if (claim.root_index != column.root_index or claim.column_index != column.column_index or
                claim.sample_index != sample or claim.extended_log_size != column.extended_log_size)
                return error.ClaimOrderMismatch;
            raw_points[sample] = claimPoint(claim);
        }
        const plan = try plans.getOrCreateCoefficientEvalPlan(
            allocator,
            &plan_index,
            &plan_entries,
            coeff_log,
            fold_count,
            raw_points[0..column.ood_claims],
            null,
        );
        try auditPlan(plan, raw_points[0..column.ood_claims], coeff_log, fold_count);

        const direct = try allocator.alloc(QM31, column.ood_claims * coeff_log);
        defer allocator.free(direct);
        prover.poly.circle.poly.fillEvalFactorsForPointsFolded(
            raw_points[0..column.ood_claims],
            fold_count,
            coeff_log,
            direct,
        );
        for (direct, plan.flat_factors) |expected, actual|
            try std.testing.expect(expected.eql(actual));

        if (!ran_negative_controls and column.ood_claims == 2 and coeff_log == 10) {
            try std.testing.expectError(error.PlanShapeMismatch, auditPlan(plan, raw_points[0..2], coeff_log - 1, fold_count));
            try std.testing.expectError(error.PlanShapeMismatch, auditPlan(plan, raw_points[0..2], coeff_log, fold_count + 1));
            const changed = raw_points[0];
            raw_points[0] = raw_points[1];
            try std.testing.expectError(error.PlanPointMismatch, auditPlan(plan, raw_points[0..2], coeff_log, fold_count));
            raw_points[0] = changed;
            const last = plan.flat_factors.len - 1;
            const saved = plan.flat_factors[last];
            plan.flat_factors[last] = saved.add(QM31.one());
            try std.testing.expectError(error.PlanFactorMismatch, auditPlan(plan, raw_points[0..2], coeff_log, fold_count));
            plan.flat_factors[last] = saved;
            ran_negative_controls = true;
        }
        columns_at_height[bucket] += 1;
        claims_at_height[bucket] += column.ood_claims;
        claim_cursor = end;
    }
    try std.testing.expect(ran_negative_controls);
    try std.testing.expectEqual(capture.claims.len, claim_cursor);
    try std.testing.expectEqualSlices(usize, &.{ 14, 28, 19 }, &columns_at_height);
    try std.testing.expectEqualSlices(usize, &.{ 18, 32, 23 }, &claims_at_height);
}
