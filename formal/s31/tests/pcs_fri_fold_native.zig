//! An algebraic oracle for the pinned FRI fold helpers.  The oracle does not
//! call the native butterfly or single-step fold used by the verifier.
const std = @import("std");
const core = @import("stwo_core");
const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;

fn value(i: usize) QM31 {
    const n: u32 = @intCast(i);
    return QM31.fromU32Unchecked(3 + n * 17, 5 + n * 19, 7 + n * 23, 11 + n * 29);
}

fn pair(alpha: QM31, coordinate: M31, left: QM31, right: QM31) !QM31 {
    const inverse = try coordinate.inv();
    return left.add(right).add(alpha.mul(left.sub(right).mulM31(inverse)));
}

test "FRI circle to line agrees with independent pair algebra and alpha squared accumulation" {
    const allocator = std.testing.allocator;
    const domain = core.poly.circle.canonic.CanonicCoset.new(4).circleDomain();
    const alpha = QM31.fromU32Unchecked(41, 43, 47, 53);
    var src: [16]QM31 = undefined;
    var dst: [8]QM31 = undefined;
    var expected: [8]QM31 = undefined;
    for (&src, 0..) |*entry, i| entry.* = value(i);
    for (&dst, 0..) |*entry, i| {
        entry.* = value(i + 16);
        const point_index = core.utils.bitReverseIndex(i, 3);
        const y = domain.half_coset.at(point_index).y;
        expected[i] = entry.*.mul(alpha.pow(2)).add(
            try pair(alpha, y, src[2 * i], src[2 * i + 1]),
        );
    }
    var workspace = try core.fri.FoldCircleWorkspace.init(allocator, dst.len);
    defer workspace.deinit(allocator);
    try core.fri.foldCircleIntoLineWithWorkspace(allocator, &dst, &src, domain, alpha, &workspace);
    for (dst, expected) |actual, wanted| try std.testing.expect(actual.eql(wanted));
}

test "FRI four line halvings agree with independent algebra and challenge powers" {
    const allocator = std.testing.allocator;
    var domain = try core.poly.line.LineDomain.init(core.circle.Coset.halfOdds(4));
    const original_domain = domain;
    const alpha = QM31.fromU32Unchecked(61, 67, 71, 73);
    var src: [16]QM31 = undefined;
    var modeled: [16]QM31 = undefined;
    var next: [16]QM31 = undefined;
    for (&src, 0..) |*entry, i| entry.* = value(i + 32);
    @memcpy(&modeled, &src);
    var length: usize = src.len;
    for (0..4) |step| {
        const half = length / 2;
        const challenge = alpha.pow(@as(u64, 1) << @intCast(step));
        for (0..half) |i| {
            const point_index = core.utils.bitReverseIndex(i, @intCast(std.math.log2_int(usize, half)));
            const x = domain.at(point_index);
            next[i] = try pair(challenge, x, modeled[2 * i], modeled[2 * i + 1]);
        }
        @memcpy(modeled[0..half], next[0..half]);
        length = half;
        domain = domain.double();
    }
    var workspace = try core.fri.FoldLineWorkspace.init(allocator, 8);
    defer workspace.deinit(allocator);
    const native = try core.fri.foldLineNWithWorkspace(allocator, &src, original_domain, alpha, &workspace, 4);
    defer allocator.free(native.values);
    try std.testing.expectEqual(@as(usize, 1), native.values.len);
    try std.testing.expect(native.values[0].eql(modeled[0]));
}
