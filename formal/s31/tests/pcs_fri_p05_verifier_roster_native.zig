//! Synthetic verifier-bundle control only: no proof bytes or acceptance test.
const std = @import("std");
const core = @import("stwo_core");
const roster = @import("s31_p05_roster");
const paired = @import("s31_pair_fold");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Point = core.circle.CirclePointQM31;
const H = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;
const Path = core.vcs_lifted.verifier.MerklePathCapture(H);
const Component = core.air.components.Component;
const MaskPoints = core.air.components.MaskPoints;
const TraceLogs = core.air.components.TraceLogDegreeBounds;
const MaskValues = core.air.components.MaskValues;

const FakeAir = struct {
    fn nConstraints(_: *const anyopaque) usize {
        return 1;
    }
    fn maxConstraintLogDegreeBound(_: *const anyopaque) u32 {
        return 3;
    }
    fn compositionLogSplit(_: *const anyopaque) u32 {
        return 1;
    }
    fn traceLogDegreeBounds(_: *const anyopaque, allocator: std.mem.Allocator) !TraceLogs {
        const pp = try allocator.dupe(u32, &[_]u32{1});
        errdefer allocator.free(pp);
        const main = try allocator.dupe(u32, &[_]u32{2});
        errdefer allocator.free(main);
        const interaction = try allocator.dupe(u32, &[_]u32{1});
        errdefer allocator.free(interaction);
        return TraceLogs.initOwned(try allocator.dupe([]u32, &.{ pp, main, interaction }));
    }
    fn maskPoints(_: *const anyopaque, allocator: std.mem.Allocator, point: Point, _: u32) !MaskPoints {
        const pp = try allocator.alloc([]Point, 0);
        errdefer allocator.free(pp);
        const main_point = try allocator.dupe(Point, &[_]Point{point.add(core.circle.SECURE_FIELD_CIRCLE_GEN.mul(2))});
        errdefer allocator.free(main_point);
        const main = try allocator.dupe([]Point, &[_][]Point{main_point});
        errdefer allocator.free(main);
        const interaction_points = try allocator.dupe(Point, &[_]Point{
            point,
            point.add(core.circle.SECURE_FIELD_CIRCLE_GEN.mul(3)),
        });
        errdefer allocator.free(interaction_points);
        const interaction = try allocator.dupe([]Point, &[_][]Point{interaction_points});
        errdefer allocator.free(interaction);
        return MaskPoints.initOwned(try allocator.dupe([][]Point, &.{ pp, main, interaction }));
    }
    fn preprocessedColumnIndices(_: *const anyopaque, allocator: std.mem.Allocator) ![]usize {
        return allocator.dupe(usize, &[_]usize{0});
    }
    fn evaluateConstraintQuotientsAtPoint(
        _: *const anyopaque,
        _: Point,
        _: *const MaskValues,
        _: *core.air.accumulation.PointEvaluationAccumulator,
        _: u32,
    ) !void {}
    const vtable = core.air.components.ComponentVTable{
        .nConstraints = nConstraints,
        .maxConstraintLogDegreeBound = maxConstraintLogDegreeBound,
        .compositionLogSplit = compositionLogSplit,
        .traceLogDegreeBounds = traceLogDegreeBounds,
        .maskPoints = maskPoints,
        .preprocessedColumnIndices = preprocessedColumnIndices,
        .evaluateConstraintQuotientsAtPoint = evaluateConstraintQuotientsAtPoint,
    };
};

fn leaf(words: []const M31) H.Hash {
    var hasher = H.defaultWithInitialState();
    hasher.updateLeaf(words);
    return hasher.finalize();
}

fn word(tree: usize, column: usize, position: usize) M31 {
    const value: u32 = switch (tree) {
        0 => @intCast(2 + (position & 1)),
        1 => @intCast(4 + position),
        2 => @intCast(8 + (position & 1)),
        else => @intCast(10 + column + position),
    };
    return M31.fromCanonical(value);
}

test "P05 verifier-owned AIR and proof roster feeds native pair fold" {
    const alloc = std.testing.allocator;
    const fri = try core.pcs.config_v2.FriConfigV2.init(0, 0, 1, 2, 1);
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndLiftingSize(fri, 2);
    var raw = [_]usize{ 0, 1 };
    var unique = [_]usize{ 0, 1 };
    var logs0 = [_]u32{1};
    var logs1 = [_]u32{2};
    var logs2 = [_]u32{1};
    var logs3 = [_]u32{2} ** 8;
    var logs = [_][]u32{ &logs0, &logs1, &logs2, &logs3 };
    var roots: [4]H.Hash = undefined;
    var positions: [4][2]usize = undefined;
    var siblings: [4][4]H.Hash = undefined;
    var paths: [4]Path = undefined;
    var values: [22]M31 = undefined;
    var value_at: usize = 0;
    for (logs, 0..) |tree_logs, tree| {
        var leaves: [4]H.Hash = undefined;
        for (0..4) |pos| {
            var leaf_words: [8]M31 = undefined;
            for (tree_logs, 0..) |_, column| leaf_words[column] = word(tree, column, pos);
            leaves[pos] = leaf(leaf_words[0..tree_logs.len]);
        }
        const left = H.hashChildren(.{ .left = leaves[0], .right = leaves[1] });
        const right = H.hashChildren(.{ .left = leaves[2], .right = leaves[3] });
        roots[tree] = H.hashChildren(.{ .left = left, .right = right });
        for (tree_logs, 0..) |_, column| {
            for (raw) |pos| {
                values[value_at] = word(tree, column, pos);
                value_at += 1;
            }
        }
        for (raw, 0..) |pos, slot| {
            positions[tree][slot] = pos;
            siblings[tree][2 * slot] = leaves[pos ^ 1];
            siblings[tree][2 * slot + 1] = right;
        }
        paths[tree] = .{
            .positions = positions[tree][0..],
            .path_depth = 2,
            .siblings = siblings[tree][0..],
        };
    }
    try std.testing.expectEqual(values.len, value_at);
    const oods_seed = QM31.fromU32Unchecked(1, 2, 3, 4);
    const oods_point = try core.circle.secureFieldPointFromRandomSeedChecked(oods_seed);
    var points0 = [_]Point{oods_point};
    var points1 = [_]Point{oods_point.add(core.circle.SECURE_FIELD_CIRCLE_GEN.mul(2))};
    var points2 = [_]Point{ oods_point, oods_point.add(core.circle.SECURE_FIELD_CIRCLE_GEN.mul(3)) };
    var points3_storage: [8][1]Point = undefined;
    var points3: [8][]Point = undefined;
    for (&points3_storage, &points3) |*storage, *slot| {
        storage.* = .{oods_point};
        slot.* = storage[0..];
    }
    var cols0 = [_][]Point{points0[0..]};
    var cols1 = [_][]Point{points1[0..]};
    var cols2 = [_][]Point{points2[0..]};
    var point_trees = [_][][]Point{ &cols0, &cols1, &cols2, &points3 };
    var vals0 = [_]QM31{QM31.fromU32Unchecked(21, 0, 0, 0)};
    var vals1 = [_]QM31{QM31.fromU32Unchecked(22, 0, 0, 0)};
    var vals2 = [_]QM31{
        QM31.fromU32Unchecked(23, 0, 0, 0),
        QM31.fromU32Unchecked(24, 0, 0, 0),
    };
    var vals3_storage: [8][1]QM31 = undefined;
    var vals3: [8][]QM31 = undefined;
    for (&vals3_storage, &vals3, 0..) |*storage, *slot, i| {
        storage.* = .{QM31.fromU32Unchecked(@intCast(25 + i), 0, 0, 0)};
        slot.* = storage[0..];
    }
    var valcols0 = [_][]QM31{vals0[0..]};
    var valcols1 = [_][]QM31{vals1[0..]};
    var valcols2 = [_][]QM31{vals2[0..]};
    var value_trees = [_][][]QM31{ &valcols0, &valcols1, &valcols2, &vals3 };
    const accepted_values = core.pcs.TreeVec([][]QM31).initOwned(value_trees[0..]);
    var flat_claims: [12]QM31 = undefined;
    var flat_at: usize = 0;
    for (value_trees) |tree| for (tree) |column| for (column) |value| {
        flat_claims[flat_at] = value;
        flat_at += 1;
    };
    try std.testing.expectEqual(flat_claims.len, flat_at);
    var capture: core.verifier.ProofCapture(H) = undefined;
    capture.queries = .{ .raw = raw[0..], .unique = unique[0..] };
    capture.commitments = roots[0..];
    capture.column_log_sizes = logs[0..];
    capture.sampled_points = point_trees[0..];
    capture.sampled_values = flat_claims[0..];
    capture.queried_values = values[0..];
    capture.trace_paths = paths[0..];
    capture.oods_seed = oods_seed;
    capture.deep_randomness = QM31.fromU32Unchecked(7, 0, 0, 0);
    const FakeTree = struct { root: H.Hash, column_log_sizes: []u32, height: u32 };
    var scheme_trees: [4]FakeTree = undefined;
    for (&scheme_trees, roots, logs) |*tree, root, tree_logs| {
        tree.* = .{ .root = root, .column_log_sizes = tree_logs, .height = 2 };
    }
    var scheme = .{ .trees = .{ .items = scheme_trees[0..] }, .revision_config = pcs };
    const dummy: u8 = 0;
    const handles = [_]Component{.{ .ctx = &dummy, .vtable = &FakeAir.vtable }};
    const claims = try roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true);
    defer alloc.free(claims);
    try std.testing.expectEqual(@as(usize, 12), claims.len);
    try std.testing.expectEqual(@as(usize, 3), claims[4].tree_index);
    try std.testing.expectEqual(@as(usize, 7), claims[11].column_index);
    const fold_alpha = QM31.fromU32Unchecked(29, 0, 0, 0);
    const pair_beta = QM31.fromU32Unchecked(31, 0, 0, 0);
    var folds = try paired.reconstruct(
        alloc,
        pcs,
        &roots,
        &capture,
        scheme,
        &handles,
        accepted_values,
        true,
        fold_alpha,
        pair_beta,
    );
    defer folds.deinit(alloc);
    try std.testing.expectEqual(@as(usize, 13), folds.words.len);
    try std.testing.expectEqual(@as(usize, 7), folds.words[12].column_index);

    capture.sampled_values = flat_claims[0 .. flat_claims.len - 1];
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    try std.testing.expectError(error.InvalidP05VerifierRoster, paired.reconstruct(
        alloc,
        pcs,
        &roots,
        &capture,
        scheme,
        &handles,
        accepted_values,
        true,
        fold_alpha,
        pair_beta,
    ));
    capture.sampled_values = flat_claims[0..];
    valcols2[0] = vals2[0..1];
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    valcols2[0] = vals2[0..];
    std.mem.swap(QM31, &vals2[0], &vals2[1]);
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    std.mem.swap(QM31, &vals2[0], &vals2[1]);
    std.mem.swap(Point, &points2[0], &points2[1]);
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    try std.testing.expectError(error.InvalidP05VerifierRoster, paired.reconstruct(
        alloc,
        pcs,
        &roots,
        &capture,
        scheme,
        &handles,
        accepted_values,
        true,
        fold_alpha,
        pair_beta,
    ));
    std.mem.swap(Point, &points2[0], &points2[1]);
    flat_claims[0] = QM31.fromU32Unchecked(99, 0, 0, 0);
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    try std.testing.expectError(error.InvalidP05VerifierRoster, paired.reconstruct(
        alloc,
        pcs,
        &roots,
        &capture,
        scheme,
        &handles,
        accepted_values,
        true,
        fold_alpha,
        pair_beta,
    ));
    flat_claims[0] = vals0[0];
    logs1[0] = 1;
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    logs1[0] = 2;
    roots[3][0] ^= 1;
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
    roots[3][0] ^= 1;
    scheme.revision_config.trace_lifting_log_size += 1;
    try std.testing.expectError(error.InvalidP05VerifierRoster, roster.derive(H, alloc, pcs, scheme, &handles, accepted_values, &capture, true));
}
