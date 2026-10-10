//! Experimental two-call verifier entrypoint. The executable embeds its
//! normalized source and AIR and derives the only accepted key from them.
//! The caller supplies only a proof and eight public output words.
const std = @import("std");
const pair = @import("pair_native_package.zig");
const statement = @import("pair_statement.zig");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const args = try std.process.argsAlloc(allocator);
    if (args.len != 3) return error.ExpectedProofAndStatementPaths;

    const raw = try std.fs.cwd().readFileAlloc(allocator, args[1], 16 << 20);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 4096);
    var parsed = try std.json.parseFromSlice(statement.Statement, allocator, statement_bytes, .{ .ignore_unknown_fields = false });
    defer parsed.deinit();
    if (!std.mem.eql(u8, parsed.value.schema, statement.schema_name))
        return error.InvalidPairStatementSchema;

    try pair.verifyEmbedded(@embedFile("s31_program_source"), @embedFile("s31_air_programs"), allocator, parsed.value.public_words, raw);
    std.debug.print("verified\n", .{});
}
