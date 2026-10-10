//! Experimental two-call prover entrypoint using an embedded normalized source.
const std = @import("std");
const relation = @import("../language/relation.zig");
const pair = @import("pair_native_package.zig");
const statement = @import("pair_statement.zig");

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const args = try std.process.argsAlloc(allocator);
    if (args.len != 4) return error.ExpectedAssignmentProofAndStatementPaths;

    const source = @embedFile("s31_program_source");
    const air = @embedFile("s31_air_programs");
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    var assignment = try relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    var program = try relation.parseProgram(allocator, source);
    defer program.deinit();
    const public_words = try relation.evaluate(allocator, program.value, assignment.value);
    const key = try pair.sealKey(allocator, source, air);
    const raw = try pair.proveSealed(allocator, source, air, key, assignment.value);
    const encoded_statement = try std.json.Stringify.valueAlloc(allocator, statement.Statement{
        .schema = statement.schema_name,
        .public_words = public_words,
    }, .{});
    try std.fs.cwd().writeFile(.{ .sub_path = args[2], .data = raw });
    try std.fs.cwd().writeFile(.{ .sub_path = args[3], .data = encoded_statement });
    std.debug.print("proved\n", .{});
}
