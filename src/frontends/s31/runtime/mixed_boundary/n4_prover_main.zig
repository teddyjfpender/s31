//! Build-time source-embedded mixed N=4 prover.
const std = @import("std");
const relation = @import("../../language/relation.zig");
const package = @import("n4_package.zig");
const statement = @import("n4_statement.zig");

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
    const sealed = try package.proveSealedAndInspect(allocator, source, air, assignment.value);
    defer allocator.free(sealed.bytes);
    const inspected = sealed.inspection;
    const source_hex = std.fmt.bytesToHex(inspected.schedule.source_sha256, .lower);
    const manifest_hex = std.fmt.bytesToHex(inspected.schedule.digest, .lower);
    const identity_hex = std.fmt.bytesToHex(inspected.circuit_identity_sha256, .lower);
    const statement_bytes = try std.json.Stringify.valueAlloc(allocator, statement.Statement{
        .schema = statement.schema_name,
        .source_sha256 = &source_hex,
        .manifest_sha256 = &manifest_hex,
        .circuit_identity_sha256 = &identity_hex,
        .public_words = public_words,
    }, .{});
    defer allocator.free(statement_bytes);
    try std.fs.cwd().writeFile(.{ .sub_path = args[2], .data = sealed.bytes });
    try std.fs.cwd().writeFile(.{ .sub_path = args[3], .data = statement_bytes });
    std.debug.print("proved\n", .{});
}
