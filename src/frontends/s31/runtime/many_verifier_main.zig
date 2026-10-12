//! Experimental V4 native verifier. The executable embeds its source and AIR;
//! callers provide only proof bytes and eight public output words.
const std = @import("std");
const package = @import("many_native_package.zig");
const statement = @import("many_statement.zig");

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
    if (!std.mem.eql(u8, parsed.value.schema, statement.schema_name))
        return error.InvalidManyStatementSchema;
    try package.verifyEmbedded(
        @embedFile("s31_program_source"),
        @embedFile("s31_air_programs"),
        allocator,
        parsed.value.public_words,
        proof,
    );
    std.debug.print("verified\n", .{});
}
