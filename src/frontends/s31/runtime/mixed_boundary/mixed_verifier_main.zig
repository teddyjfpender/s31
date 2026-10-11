//! Build-time source-embedded mixed N=3 verifier.
const std = @import("std");
const package = @import("package.zig");
const statement = @import("statement.zig");

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 3) return error.ExpectedProofAndStatementPaths;
    const proof = try std.fs.cwd().readFileAlloc(allocator, args[1], 16 << 20);
    defer allocator.free(proof);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 4096);
    defer allocator.free(statement_bytes);
    var parsed = try std.json.parseFromSlice(statement.Statement, allocator, statement_bytes, .{ .ignore_unknown_fields = false });
    defer parsed.deinit();
    const source = @embedFile("s31_program_source");
    const air = @embedFile("s31_air_programs");
    if (!std.mem.eql(u8, parsed.value.schema, statement.schema_name))
        return error.InvalidMixedStatementIdentity;
    const inspected = try package.verifyEmbeddedAndInspect(source, air, allocator, parsed.value.public_words, proof);
    try statement.check(&inspected, parsed.value);
    std.debug.print("verified\n", .{});
}
