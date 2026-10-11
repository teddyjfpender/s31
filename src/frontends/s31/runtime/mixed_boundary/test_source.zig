//! Compact compile-time source family for bounded descriptor tests only.
const std = @import("std");

pub fn forCount(comptime count: usize) []const u8 {
    if (count < 1 or count > 8) @compileError("mixed descriptor test count must be 1..8");
    comptime var calls: []const u8 = "";
    inline for (0..count) |id| {
        const lhs = if (id == 0) "x" else std.fmt.comptimePrint("r{d}", .{id - 1});
        calls = calls ++ std.fmt.comptimePrint(
            "{{\"name\":\"r{d}\",\"op\":\"repeat\",\"lhs\":\"{s}\",\"rounds\":16,\"body\":[{{\"op\":\"square\"}},{{\"op\":\"add_const\",\"constant\":{d}}}]}},",
            .{ id, lhs, 13 + id },
        );
    }
    return "{\"version\":1,\"name\":\"mixed_descriptor_matrix\",\"inputs\":[{\"name\":\"x\",\"kind\":\"m31\",\"length\":4,\"visibility\":\"private\"}],\"nodes\":[" ++
        calls ++
        std.fmt.comptimePrint(
            "{{\"name\":\"sum\",\"op\":\"add\",\"lhs\":\"r{d}\",\"rhs\":\"x\"}},{{\"name\":\"product\",\"op\":\"mul\",\"lhs\":\"r{d}\",\"rhs\":\"x\"}}],\"assertions\":[],\"public_outputs\":[\"sum\",\"product\"]}}",
            .{ count - 1, count - 1 },
        );
}
