//! Experimental two-call prover entrypoint using an embedded normalized source.
const std = @import("std");
const relation = @import("../language/relation.zig");
const pair = @import("pair_native_package.zig");
const statement = @import("pair_statement.zig");

pub fn main() !void {
    // Pair AIR components evaluate composition quotients concurrently and
    // allocate scratch through this allocator. ArenaAllocator is not safe for
    // concurrent allocation, even when its backing allocator is thread-safe.
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
    var program = try relation.parseProgram(allocator, source);
    defer program.deinit();
    const public_words = try relation.evaluate(allocator, program.value, assignment.value);
    const key = try pair.sealKey(allocator, source, air);
    defer allocator.free(key);
    const raw = try pair.proveSealed(allocator, source, air, key, assignment.value);
    defer allocator.free(raw);
    const encoded_statement = try std.json.Stringify.valueAlloc(allocator, statement.Statement{
        .schema = statement.schema_name,
        .public_words = public_words,
    }, .{});
    defer allocator.free(encoded_statement);
    try std.fs.cwd().writeFile(.{ .sub_path = args[2], .data = raw });
    try std.fs.cwd().writeFile(.{ .sub_path = args[3], .data = encoded_statement });
    std.debug.print("proved\n", .{});
}
