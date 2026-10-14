//! Finite source check for the exact Gate log-4 canonical domain. The S31
//! gitlink pins the stwo-zig implementation compiled by this test.
const std = @import("std");
const core = @import("stwo_core");

const circle = core.circle;
const M31 = core.fields.m31.M31;
const CM31 = core.fields.cm31.CM31;

const expected_indices = [_]usize{
    67108864, 2080374784, 1140850688, 1006632960,
    603979776, 1543503872, 1677721600, 469762048,
    335544320, 1811939328, 1409286144, 738197504,
    872415232, 1275068416, 1946157056, 201326592,
};
const expected_points = [_][2]u32{
    .{ 1179735656, 1241207368 }, .{ 1179735656, 906276279 },
    .{ 967747991, 906276279 }, .{ 967747991, 1241207368 },
    .{ 1241207368, 967747991 }, .{ 1241207368, 1179735656 },
    .{ 906276279, 1179735656 }, .{ 906276279, 967747991 },
    .{ 1415090252, 2112881577 }, .{ 1415090252, 34602070 },
    .{ 732393395, 34602070 }, .{ 732393395, 2112881577 },
    .{ 2112881577, 732393395 }, .{ 2112881577, 1415090252 },
    .{ 34602070, 1415090252 }, .{ 34602070, 732393395 },
};

test "Gate log-4 native canonical rows refine finite Fourier certificate" {
    const domain = core.poly.circle.canonic.CanonicCoset.new(4).circleDomain();
    try std.testing.expectEqual(@as(usize, 16), domain.size());
    try std.testing.expect(circle.M31_CIRCLE_GEN.isOnCircle());
    try std.testing.expect(circle.M31_CIRCLE_GEN.repeatedDouble(30).eql(.{
        .x = M31.fromCanonical(2147483646), .y = M31.zero(),
    }));
    try std.testing.expect(circle.M31_CIRCLE_GEN.repeatedDouble(31).eql(circle.CirclePointM31.identity()));

    var coordinates: [16]CM31 = undefined;
    for (0..16) |row| {
        const natural = core.utils.bitReverseIndex(row, 4);
        const index = domain.indexAt(natural);
        try std.testing.expectEqual(expected_indices[row], index.v);
        const point = domain.at(natural);
        try std.testing.expectEqual(expected_points[row][0], point.x.toU32());
        try std.testing.expectEqual(expected_points[row][1], point.y.toU32());
        try std.testing.expect(point.isOnCircle());

        // CM31 is the concrete x+i*y pair used by the Laurent-coordinate
        // model; compare against field arithmetic, not just struct fields.
        const imaginary = CM31.fromU32Unchecked(0, 1);
        const actual = CM31.fromBase(point.x).add(CM31.fromBase(point.y).mul(imaginary));
        const expected = CM31.fromM31(point.x, point.y);
        try std.testing.expect(actual.eql(expected));
        coordinates[row] = actual;
        for (coordinates[0..row]) |earlier| {
            try std.testing.expect(!earlier.eql(actual));
        }
    }
}
