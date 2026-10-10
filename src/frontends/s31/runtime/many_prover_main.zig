//! Experimental V4 prover with source and official AIR embedded at build time.
const std = @import("std");
const relation = @import("../language/relation.zig");
const package = @import("many_native_package.zig");
const statement = @import("many_statement.zig");

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 4) return error.ExpectedAssignmentProofAndStatementPaths;
    const source = @embedFile("s31_program_source");
    const air = @embedFile("s31_air_programs");
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(assignment_bytes);
    var assignment = try relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    const public_words = try relation.evaluate(allocator, parsed.value, assignment.value);
    const proof = try package.proveSealed(allocator, source, air, assignment.value);
    defer allocator.free(proof);
    const statement_bytes = try std.json.Stringify.valueAlloc(allocator, statement.Statement{
        .schema = statement.schema_name,
        .public_words = public_words,
    }, .{});
    defer allocator.free(statement_bytes);
    try std.fs.cwd().writeFile(.{ .sub_path = args[2], .data = proof });
    try std.fs.cwd().writeFile(.{ .sub_path = args[3], .data = statement_bytes });
    std.debug.print("proved\n", .{});
}
