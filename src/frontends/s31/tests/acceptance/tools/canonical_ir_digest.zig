//! Minimal native oracle for the bounded source/canonical-IR differential test.
//! It invokes the same relation parser and canonical builder as the runtime.
const std = @import("std");
const s31 = @import("stwo_s31_prototype");
const relation = s31.relation;
const canonical = s31.canonical;

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 2) return error.ExpectedOneNormalizedRelationPath;
    const source = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(source);
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    var ir = try canonical.build(allocator, parsed.value);
    defer ir.deinit();
    const digest = std.fmt.bytesToHex(ir.sha256, .lower);
    var buffer: [256]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.print("{s}\n", .{&digest});
    try stdout.interface.flush();
}
