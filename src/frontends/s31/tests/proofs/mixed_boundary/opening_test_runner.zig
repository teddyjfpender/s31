//! A focused runner that requires exactly one expected PCS rejection per tree.
//! The stock Zig runner fails on expected verifier `std.log.err` diagnostics.
const std = @import("std");
const builtin = @import("builtin");

pub const std_options: std.Options = .{ .logFn = testLog };
pub const s31_opening_authentication = true;

var root_mismatch_logs: [3]u8 = .{ 0, 0, 0 };
var unexpected_error_logs: usize = 0;

fn testLog(comptime level: std.log.Level, comptime scope: @Type(.enum_literal), comptime format: []const u8, args: anytype) void {
    if (comptime level == .err and std.mem.eql(u8, format, "PCS Merkle verification failed for tree {d}: {s}")) {
        const tree: usize = args[0];
        if (tree < root_mismatch_logs.len and std.mem.eql(u8, args[1], "RootMismatch")) {
            root_mismatch_logs[tree] +|= 1;
            return;
        }
    }
    if (level == .err) unexpected_error_logs += 1;
    std.log.defaultLog(level, scope, format, args);
}

pub fn main() !void {
    for (builtin.test_functions) |test_fn| {
        std.testing.allocator_instance = .{};
        const result = test_fn.func();
        const leaked = std.testing.allocator_instance.deinit() == .leak;
        try result;
        if (leaked) return error.TestAllocatorLeak;
    }
    if (unexpected_error_logs != 0 or !std.mem.eql(u8, &root_mismatch_logs, &.{ 1, 1, 1 }))
        return error.UnexpectedVerifierLog;
}
