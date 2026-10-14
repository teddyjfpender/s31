//! The one accepted sparse Gate proof's OOD coordinates, claims, and one
//! authenticated source row per column exercise exact H3 quotient arithmetic.
//! This checks sampled rows only. It does not certify a committed quotient
//! oracle, a degree bound, a paper batch width, or security bits.
const std = @import("std");
const core = @import("stwo_core");
const own = @import("s31_own_adapter");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;

const Column = struct {
    root_index: usize,
    column_index: usize,
    extended_log_size: u32,
    ood_claims: usize,
    first_claim_index: usize,
    source_value_at_first_raw_query: u32,
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
        trace_lifting_log_size: u32,
        first_raw_lifted_query_position: usize,
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

fn point(claim: Claim) Point {
    return .{ .x = field(claim.point_x_limbs), .y = field(claim.point_y_limbs) };
}

fn nativeAnswer(
    alloc: std.mem.Allocator,
    lifting_log: u32,
    source_log: u32,
    raw: usize,
    source: M31,
    points: []Point,
    values: []QM31,
    alpha: QM31,
) !QM31 {
    var logs_data = [_]u32{source_log};
    var logs = [_][]u32{logs_data[0..]};
    var point_columns = [_][]Point{points};
    var point_trees = [_][][]Point{point_columns[0..]};
    var value_columns = [_][]QM31{values};
    var value_trees = [_][][]QM31{value_columns[0..]};
    var source_data = [_]M31{source};
    var source_columns = [_][]M31{source_data[0..]};
    var source_trees = [_][][]M31{source_columns[0..]};
    const queries = [_]usize{raw};
    const answers = try core.pcs.quotients.friAnswers(
        alloc,
        core.pcs.TreeVec([]u32).initOwned(logs[0..]),
        core.pcs.TreeVec([][]Point).initOwned(point_trees[0..]),
        core.pcs.TreeVec([][]QM31).initOwned(value_trees[0..]),
        alpha,
        &queries,
        core.pcs.TreeVec([][]M31).initOwned(source_trees[0..]),
        lifting_log,
    );
    defer alloc.free(answers);
    try std.testing.expectEqual(@as(usize, 1), answers.len);
    return answers[0];
}

test "P05 accepted sparse H3 two-point own quotient rows match native PCS" {
    const alloc = std.testing.allocator;
    const json = try std.fs.cwd().readFileAlloc(alloc, "design/s31/security/evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json", 1 << 20);
    defer alloc.free(json);
    var parsed = try std.json.parseFromSlice(Evidence, alloc, json, .{ .ignore_unknown_fields = true });
    defer parsed.deinit();
    const evidence = parsed.value;
    try std.testing.expectEqualStrings(
        "7d4cdaab4e446aaa2c357e28f077e469412f45a17c660e8d4434cca216dccfc7",
        evidence.package_checks.key_sha256,
    );
    try std.testing.expectEqualStrings(
        "04eaca23d8a6c7fc977b24a3d925aaabcbb727fa4fa30f30c81864e24a158e39",
        evidence.package_checks.proof_sha256,
    );
    try std.testing.expectEqualStrings(
        "d0dfd3b36e3abc181e90ee0456ca2760602636fc5c2c378572d84b99e26ed5f5",
        evidence.accepted_ood_claim_map_sha256,
    );
    try std.testing.expect(evidence.native_to_paper_batch_width_M == null);
    try std.testing.expect(evidence.native_proven_security_bits == null);
    try std.testing.expect(!evidence.proven_release_admissible);
    const shape = evidence.accepted_capture;
    try std.testing.expectEqual(@as(usize, 61), shape.columns.len);
    try std.testing.expectEqual(@as(usize, 73), shape.claims.len);
    try std.testing.expectEqual(@as(u32, 17), shape.trace_lifting_log_size);
    // Independent pinned digest of the exact authenticated row roster:
    // LE32(lifting log) || LE64(raw query) || 61 LE32 source values.
    var row_hash = std.crypto.hash.sha2.Sha256.init(.{});
    var log_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &log_bytes, shape.trace_lifting_log_size, .little);
    row_hash.update(&log_bytes);
    var raw_bytes: [8]u8 = undefined;
    std.mem.writeInt(u64, &raw_bytes, shape.first_raw_lifted_query_position, .little);
    row_hash.update(&raw_bytes);
    for (shape.columns) |column| {
        var value_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &value_bytes, column.source_value_at_first_raw_query, .little);
        row_hash.update(&value_bytes);
    }
    var row_digest: [32]u8 = undefined;
    row_hash.final(&row_digest);
    try std.testing.expectEqualStrings(
        "cb93d734058ac7f0cca69838e265e4447d9a5f26b67aa28d012c1426ddb9f5d7",
        &std.fmt.bytesToHex(row_digest, .lower),
    );
    const domain_size: usize = @as(usize, 1) << @intCast(shape.trace_lifting_log_size);
    try std.testing.expect(shape.first_raw_lifted_query_position < domain_size);
    const row = core.poly.circle.canonic.CanonicCoset.new(shape.trace_lifting_log_size)
        .circleDomain().at(core.utils.bitReverseIndex(
        shape.first_raw_lifted_query_position,
        shape.trace_lifting_log_size,
    ));
    var next_claim: usize = 0;
    var count_by_log = [_]usize{ 0, 0, 0 };
    var periodicity_count: usize = 0;
    const alpha = QM31.fromU32Unchecked(7, 0, 0, 0);
    for (shape.columns) |column| {
        try std.testing.expectEqual(next_claim, column.first_claim_index);
        try std.testing.expect(column.ood_claims == 1 or column.ood_claims == 2);
        const bucket: usize = switch (column.extended_log_size) {
            17 => 0,
            11 => 1,
            5 => 2,
            else => return error.UnexpectedAcceptedHeight,
        };
        count_by_log[bucket] += column.ood_claims;
        try std.testing.expect(column.source_value_at_first_raw_query < core.fields.m31.Modulus);
        const source = M31.fromCanonical(column.source_value_at_first_raw_query);
        const raw_one = [_]usize{shape.first_raw_lifted_query_position};
        const projected = try core.pcs.utils.prepareTreeQueryPositions(alloc, &raw_one, shape.trace_lifting_log_size, column.extended_log_size);
        defer alloc.free(projected);
        try std.testing.expectEqual(@as(usize, 1), projected.len);
        const source_row = core.poly.circle.canonic.CanonicCoset.new(column.extended_log_size)
            .circleDomain().at(core.utils.bitReverseIndex(projected[0], column.extended_log_size));
        // One accepted lifted query projects to this exact source-domain row.
        // This finite check is not a universal native projection refinement.
        try std.testing.expect(row.repeatedDouble(shape.trace_lifting_log_size - column.extended_log_size).eql(source_row));
        var column_points: [2]Point = undefined;
        var column_values: [2]QM31 = undefined;
        var direct: [2]QM31 = undefined;
        var normalized_points: [2]Point = undefined;
        var normalized_direct: [2]QM31 = undefined;
        for (0..column.ood_claims) |sample| {
            const claim = shape.claims[next_claim];
            try std.testing.expectEqual(column.root_index, claim.root_index);
            try std.testing.expectEqual(column.column_index, claim.column_index);
            try std.testing.expectEqual(column.extended_log_size, claim.extended_log_size);
            try std.testing.expectEqual(sample, claim.sample_index);
            const p = point(claim);
            const v = field(claim.value_limbs);
            const quotient = try own.ownQuotientAt(p, v, source, row);
            if (column.root_index == 2 and column.column_index == 20) {
                try std.testing.expectEqual(@as(u32, 422774917), row.x.v);
                try std.testing.expectEqual(@as(u32, 1575360667), row.y.v);
                try std.testing.expectEqual(@as(usize, 90528), shape.first_raw_lifted_query_position);
                try std.testing.expectEqual(@as(u32, 449376028), source.v);
                const want: [2][4]u32 = .{
                    .{ 0, 0, 1541021748, 1079523661 },
                    .{ 0, 0, 1882278765, 392788821 },
                };
                const limbs = quotient.toM31Array();
                for (limbs, want[sample]) |got, expected|
                    try std.testing.expectEqual(expected, got.v);
            }
            // Isolate this exact claim from native batching to compare its
            // independent production PCS row-evaluation implementation.
            var one_point = [_]Point{p};
            var one_value = [_]QM31{v};
            const native = try nativeAnswer(alloc, shape.trace_lifting_log_size, column.extended_log_size, shape.first_raw_lifted_query_position, source, one_point[0..], one_value[0..], QM31.one());
            try std.testing.expect(quotient.eql(native));
            column_points[sample] = p;
            column_values[sample] = v;
            direct[sample] = quotient;
            const normalized = p.repeatedDouble(shape.trace_lifting_log_size - column.extended_log_size);
            const normalized_quotient = try own.ownQuotientAt(normalized, v, source, source_row);
            var one_normalized_point = [_]Point{normalized};
            const native_normalized = try nativeAnswer(alloc, column.extended_log_size, column.extended_log_size, projected[0], source, one_normalized_point[0..], one_value[0..], QM31.one());
            try std.testing.expect(normalized_quotient.eql(native_normalized));
            normalized_points[sample] = normalized;
            normalized_direct[sample] = normalized_quotient;
            next_claim += 1;
        }
        if (column.ood_claims == 2) {
            const shift = core.poly.circle.canonic.CanonicCoset.new(shape.trace_lifting_log_size)
                .step().repeatedDouble(column.extended_log_size);
            const periodic = column_points[1].add(.{
                .x = QM31.fromBase(shift.x),
                .y = QM31.fromBase(shift.y),
            });
            const periodic_quotient = try own.ownQuotientAt(periodic, column_values[1], source, row);
            const native = try nativeAnswer(alloc, shape.trace_lifting_log_size, column.extended_log_size, shape.first_raw_lifted_query_position, source, column_points[0..2], column_values[0..2], alpha);
            const expected = periodic_quotient.add(direct[0].mul(alpha))
                .add(direct[1].mul(alpha.square()));
            try std.testing.expect(expected.eql(native));
            const source_shift = core.poly.circle.canonic.CanonicCoset.new(column.extended_log_size)
                .step().repeatedDouble(column.extended_log_size);
            const source_periodic = normalized_points[1].add(.{
                .x = QM31.fromBase(source_shift.x),
                .y = QM31.fromBase(source_shift.y),
            });
            const normalized_periodic_quotient = try own.ownQuotientAt(source_periodic, column_values[1], source, source_row);
            const native_source = try nativeAnswer(alloc, column.extended_log_size, column.extended_log_size, projected[0], source, normalized_points[0..2], column_values[0..2], alpha);
            const expected_source = normalized_periodic_quotient
                .add(normalized_direct[0].mul(alpha))
                .add(normalized_direct[1].mul(alpha.square()));
            try std.testing.expect(expected_source.eql(native_source));
            periodicity_count += 1;
        }
    }
    try std.testing.expectEqual(shape.claims.len, next_claim);
    try std.testing.expectEqualSlices(usize, &[_]usize{ 18, 32, 23 }, &count_by_log);
    try std.testing.expectEqual(@as(usize, 12), periodicity_count);
}
