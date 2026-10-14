//! Four independent roots and raw query slots exercise the experimental P05
//! original-word adapter. No STARK proof bytes or acceptance claim are made.
const std = @import("std");
const core = @import("stwo_core");
const adapter = @import("s31_adapter");
const own = @import("s31_own_adapter");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Path = core.vcs_lifted.verifier.MerklePathCapture(H);

fn leaf(value: u32) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(&[_]M31{M31.fromCanonical(value)});
    return hasher.finalize();
}

test "P05 original batch reconstructs four independently rooted trees at two heights" {
    const alloc = std.testing.allocator;
    // Tree order is the existing Gate order: fixed, main, interaction,
    // composition. Both high-height values include the composition word.
    const rows = [4][4]u32{
        .{ 2, 3, 2, 3 },
        .{ 4, 5, 6, 7 },
        .{ 8, 9, 8, 9 },
        .{ 10, 11, 12, 13 },
    };
    var raw = [_]usize{ 0, 1, 2, 0 };
    var unique = [_]usize{ 0, 1, 2 };
    var roots: [4]H.Hash = undefined;
    var positions: [4][4]usize = undefined;
    var siblings: [4][8]H.Hash = undefined;
    var paths: [4]Path = undefined;
    var values: [16]M31 = undefined;
    for (rows, 0..) |row, tree| {
        var leaves: [4]H.Hash = undefined;
        for (row, 0..) |value, i| leaves[i] = leaf(value);
        const left = H.hashChildren(.{ .left = leaves[0], .right = leaves[1] });
        const right = H.hashChildren(.{ .left = leaves[2], .right = leaves[3] });
        roots[tree] = H.hashChildren(.{ .left = left, .right = right });
        for (raw, 0..) |position, slot| {
            positions[tree][slot] = position;
            siblings[tree][2 * slot] = leaves[position ^ 1];
            siblings[tree][2 * slot + 1] = if (position < 2) right else left;
            values[tree * raw.len + slot] = M31.fromCanonical(row[position]);
        }
        paths[tree] = .{
            .positions = positions[tree][0..],
            .path_depth = 2,
            .siblings = siblings[tree][0..],
        };
    }
    var log_arrays = [4][1]u32{ .{1}, .{2}, .{1}, .{2} };
    var logs: [4][]u32 = undefined;
    for (&log_arrays, &logs) |*one, *slice| slice.* = one[0..];
    var capture: core.verifier.ProofCapture(H) = undefined;
    capture.queries = .{ .raw = raw[0..], .unique = unique[0..] };
    capture.commitments = roots[0..];
    capture.column_log_sizes = logs[0..];
    capture.queried_values = values[0..];
    capture.trace_paths = paths[0..];
    capture.deep_randomness = QM31.fromU32Unchecked(7, 0, 0, 0);
    const fri = try core.pcs.config_v2.FriConfigV2.init(0, 0, 1, 4, 1);
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndLiftingSize(fri, 2);

    var batches = try adapter.reconstruct(alloc, pcs, &roots, &capture);
    defer batches.deinit(alloc);
    try std.testing.expectEqual(@as(usize, 2), batches.by_height.len);
    try std.testing.expectEqual(@as(u32, 2), batches.by_height[0].column_log_size);
    try std.testing.expectEqual(@as(u32, 1), batches.by_height[1].column_log_size);
    for (batches.by_height) |batch| {
        try std.testing.expectEqual(@as(usize, 2), batch.column_count);
    }
    try std.testing.expectEqualSlices(usize, &raw, batches.by_height[0].projected_positions);
    try std.testing.expectEqualSlices(usize, &[_]usize{ 0, 1, 0, 0 }, batches.by_height[1].projected_positions);
    const expected_high = [_]QM31{
        QM31.fromU32Unchecked(74, 0, 0, 0),
        QM31.fromU32Unchecked(82, 0, 0, 0),
        QM31.fromU32Unchecked(90, 0, 0, 0),
        QM31.fromU32Unchecked(74, 0, 0, 0),
    };
    const expected_low = [_]QM31{
        QM31.fromU32Unchecked(58, 0, 0, 0),
        QM31.fromU32Unchecked(66, 0, 0, 0),
        QM31.fromU32Unchecked(58, 0, 0, 0),
        QM31.fromU32Unchecked(58, 0, 0, 0),
    };
    for (expected_high, batches.by_height[0].original_values) |want, got|
        try std.testing.expect(want.eql(got));
    for (expected_low, batches.by_height[1].original_values) |want, got|
        try std.testing.expect(want.eql(got));

    // Each native explicit mask sample owns a distinct conjugate two-point
    // quotient. Composition has two samples and therefore one extra native
    // periodicity sample, emitted before its two explicit samples.
    const gen = core.circle.SECURE_FIELD_CIRCLE_GEN;
    var p0 = [_]core.circle.CirclePointQM31{gen.mul(7)};
    var p1 = [_]core.circle.CirclePointQM31{gen.mul(11)};
    var p2 = [_]core.circle.CirclePointQM31{gen.mul(17)};
    var p3 = [_]core.circle.CirclePointQM31{ gen.mul(19), gen.mul(23) };
    var t0 = [_][]core.circle.CirclePointQM31{p0[0..]};
    var t1 = [_][]core.circle.CirclePointQM31{p1[0..]};
    var t2 = [_][]core.circle.CirclePointQM31{p2[0..]};
    var t3 = [_][]core.circle.CirclePointQM31{p3[0..]};
    var points = [_][][]core.circle.CirclePointQM31{ t0[0..], t1[0..], t2[0..], t3[0..] };
    var claims = [_]QM31{
        QM31.fromU32Unchecked(14, 0, 0, 0),
        QM31.fromU32Unchecked(15, 0, 0, 0),
        QM31.fromU32Unchecked(16, 0, 0, 0),
        QM31.fromU32Unchecked(17, 0, 0, 0),
        QM31.fromU32Unchecked(18, 0, 0, 0),
    };
    capture.sampled_points = points[0..];
    capture.sampled_values = claims[0..];
    const expected_claims = [_]own.ExpectedClaim{
        .{ .tree_index = 0, .column_index = 0, .sample_index = 0, .source_log_size = 1, .point = p0[0], .value = claims[0] },
        .{ .tree_index = 1, .column_index = 0, .sample_index = 0, .source_log_size = 2, .point = p1[0], .value = claims[1] },
        .{ .tree_index = 2, .column_index = 0, .sample_index = 0, .source_log_size = 1, .point = p2[0], .value = claims[2] },
        .{ .tree_index = 3, .column_index = 0, .sample_index = 0, .source_log_size = 2, .point = p3[0], .value = claims[3] },
        .{ .tree_index = 3, .column_index = 0, .sample_index = 1, .source_log_size = 2, .point = p3[1], .value = claims[4] },
    };
    var pair_words = try own.reconstruct(alloc, pcs, &roots, &capture, &expected_claims);
    defer pair_words.deinit(alloc);
    try std.testing.expectEqual(@as(usize, 6), pair_words.words.len);
    try std.testing.expectEqual(own.SampleKind.periodic, pair_words.words[3].kind);
    try std.testing.expectEqual(@as(usize, 3), pair_words.words[3].tree_index);
    try std.testing.expectEqual(own.SampleKind.explicit, pair_words.words[4].kind);
    try std.testing.expectEqual(own.SampleKind.explicit, pair_words.words[5].kind);
    try std.testing.expectEqualSlices(usize, &[_]usize{ 0, 1, 0, 0 }, pair_words.words[0].projected_positions);
    // One isolated own quotient is exactly the pinned native friAnswers law
    // with one source column, one OOD point, and coefficient one.
    var one_logs = [_][]u32{log_arrays[0][0..]};
    var one_points_cols = [_][]core.circle.CirclePointQM31{p0[0..]};
    var one_points = [_][][]core.circle.CirclePointQM31{one_points_cols[0..]};
    var one_claim_col = [_]QM31{claims[0]};
    var one_claim_cols = [_][]QM31{one_claim_col[0..]};
    var one_claim_trees = [_][][]QM31{one_claim_cols[0..]};
    var one_query_cols = [_][]M31{values[0..raw.len]};
    var one_query_trees = [_][][]M31{one_query_cols[0..]};
    const native_q = try core.pcs.quotients.friAnswers(
        alloc,
        core.pcs.TreeVec([]u32).initOwned(one_logs[0..]),
        core.pcs.TreeVec([][]core.circle.CirclePointQM31).initOwned(one_points[0..]),
        core.pcs.TreeVec([][]QM31).initOwned(one_claim_trees[0..]),
        QM31.one(),
        raw[0..],
        core.pcs.TreeVec([][]M31).initOwned(one_query_trees[0..]),
        2,
    );
    defer alloc.free(native_q);
    for (native_q, pair_words.words[0].quotient_values) |want, got|
        try std.testing.expect(want.eql(got));

    // The composition column's two explicit masks cause the native extra
    // periodicity sample. Their exact native order is periodic, 0, 1.
    var composition_logs = [_][]u32{log_arrays[3][0..]};
    var composition_points_cols = [_][]core.circle.CirclePointQM31{p3[0..]};
    var composition_points = [_][][]core.circle.CirclePointQM31{composition_points_cols[0..]};
    var composition_claim_cols = [_][]QM31{claims[3..5]};
    var composition_claim_trees = [_][][]QM31{composition_claim_cols[0..]};
    var composition_query_cols = [_][]M31{values[3 * raw.len .. 4 * raw.len]};
    var composition_query_trees = [_][][]M31{composition_query_cols[0..]};
    const alpha = QM31.fromU32Unchecked(7, 0, 0, 0);
    const composition_native = try core.pcs.quotients.friAnswers(
        alloc,
        core.pcs.TreeVec([]u32).initOwned(composition_logs[0..]),
        core.pcs.TreeVec([][]core.circle.CirclePointQM31).initOwned(composition_points[0..]),
        core.pcs.TreeVec([][]QM31).initOwned(composition_claim_trees[0..]),
        alpha,
        raw[0..],
        core.pcs.TreeVec([][]M31).initOwned(composition_query_trees[0..]),
        2,
    );
    defer alloc.free(composition_native);
    for (composition_native, 0..) |want, slot| {
        const got = pair_words.words[3].quotient_values[slot]
            .add(pair_words.words[4].quotient_values[slot].mul(alpha))
            .add(pair_words.words[5].quotient_values[slot].mul(alpha.square()));
        try std.testing.expect(want.eql(got));
    }
    std.mem.swap(QM31, &claims[3], &claims[4]);
    try std.testing.expectError(error.InvalidP05ClaimRoster, own.reconstruct(alloc, pcs, &roots, &capture, &expected_claims));
    std.mem.swap(QM31, &claims[3], &claims[4]);
    var wrong_height_claims = expected_claims;
    wrong_height_claims[0].source_log_size = 2;
    try std.testing.expectError(error.InvalidP05ClaimRoster, own.reconstruct(alloc, pcs, &roots, &capture, &wrong_height_claims));
    var wrong_point_claims = expected_claims;
    wrong_point_claims[3].point = p3[1];
    try std.testing.expectError(error.InvalidP05ClaimRoster, own.reconstruct(alloc, pcs, &roots, &capture, &wrong_point_claims));
    const domain = core.poly.circle.canonic.CanonicCoset.new(2).circleDomain();
    const row0 = domain.at(core.utils.bitReverseIndex(raw[0], 2));
    const zero_divisor_point = core.circle.CirclePointQM31{
        .x = QM31.fromM31(row0.x, M31.zero(), M31.one(), M31.zero()),
        .y = QM31.fromM31(row0.y, M31.zero(), M31.one(), M31.zero()),
    };
    try std.testing.expectError(error.ZeroOwnQuotientDivisor, own.ownQuotientAt(zero_divisor_point, claims[0], values[0], row0));

    // The adapter reauthenticates every independent root before batching.
    values[0] = M31.fromCanonical(20);
    try std.testing.expectError(error.InvalidPcsLiftedCapture, adapter.reconstruct(alloc, pcs, &roots, &capture));
    values[0] = M31.fromCanonical(2);
    siblings[3][0][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture, adapter.reconstruct(alloc, pcs, &roots, &capture));
    siblings[3][0][0] ^= 1;
    positions[2][2] = 3;
    try std.testing.expectError(error.InvalidPcsLiftedCapture, adapter.reconstruct(alloc, pcs, &roots, &capture));
    positions[2][2] = 2;
    roots[3][0] ^= 1;
    try std.testing.expectError(error.InvalidPcsLiftedCapture, adapter.reconstruct(alloc, pcs, &roots, &capture));
    try std.testing.expectError(error.InvalidPcsLiftedCapture, own.reconstruct(alloc, pcs, &roots, &capture, &expected_claims));
}
