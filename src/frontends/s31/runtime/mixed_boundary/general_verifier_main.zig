//! Build-time source-embedded mixed 1..8 verifier.
const std = @import("std");
const package = @import("general_package.zig");
const statement = @import("general_statement.zig");
const relation = @import("../../language/relation.zig");
const record_abi = @import("../../language/record_abi.zig");

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 3) return error.ExpectedProofAndStatementPaths;
    const proof = try std.fs.cwd().readFileAlloc(allocator, args[1], 16 << 20);
    defer allocator.free(proof);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 1 << 20);
    defer allocator.free(statement_bytes);
    const source = @embedFile("s31_program_source");
    const air = @embedFile("s31_air_programs");
    var program = try relation.parseProgram(allocator, source);
    defer program.deinit();
    if (program.value.version == 2) {
        const words = try record_abi.claimedWords(allocator, program.value, statement_bytes);
        _ = try package.verifyEmbeddedAndInspect(source, air, allocator, words, proof);
    } else {
        var parsed = try std.json.parseFromSlice(statement.Statement, allocator, statement_bytes, .{ .ignore_unknown_fields = false });
        defer parsed.deinit();
        if (!std.mem.eql(u8, parsed.value.schema, statement.schema_name))
            return error.InvalidMixedStatementIdentity;
        const inspected = try package.verifyEmbeddedAndInspect(source, air, allocator, parsed.value.public_words, proof);
        try statement.check(&inspected, parsed.value);
    }
    std.debug.print("verified\n", .{});
}
