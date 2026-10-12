//! A focused runner that requires first- and last-column fixed-tree
//! rejections and main/interaction rejections for every slot, plus one
//! authentication-path rejection in each of the four commitment trees.
//! The stock Zig runner fails on expected verifier `std.log.err` diagnostics.
const std = @import("std");
const builtin = @import("builtin");

pub const std_options: std.Options = .{ .logFn = testLog };
pub const s31_opening_authentication = true;

// The test mutates two fixed openings, then fourteen main openings, then
// fourteen interaction openings, then one hash path in each tree 0 through 3.
// Check each rejection in that order, not just totals:
// aggregate counts could hide a rejection attributed to the wrong tree.
var root_mismatch_count: usize = 0;
var unexpected_error_logs: usize = 0;

fn testLog(comptime level: std.log.Level, comptime scope: @Type(.enum_literal), comptime format: []const u8, args: anytype) void {
    if (comptime level == .err and std.mem.eql(u8, format, "PCS Merkle verification failed for tree {d}: {s}")) {
        const tree: usize = args[0];
        const expected_tree: usize = if (root_mismatch_count < 2) 0 else if (root_mismatch_count < 16) 1 else if (root_mismatch_count < 30) 2 else root_mismatch_count - 30;
        if (root_mismatch_count < 34 and tree == expected_tree and std.mem.eql(u8, args[1], "RootMismatch")) {
            root_mismatch_count += 1;
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
    if (unexpected_error_logs != 0 or root_mismatch_count != 34)
        return error.UnexpectedVerifierLog;
}
