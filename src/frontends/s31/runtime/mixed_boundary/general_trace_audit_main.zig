//! Optional full-witness audit of an already verifiable mixed proof.
//!
//! The private assignment is read locally and is never printed. This tool
//! reconstructs and checks all trace rows, then binds its three commitment
//! roots to the verified proof. It is deliberately separate from the
//! succinct native verifier, which does not require the private assignment.
const std = @import("std");
const package = @import("general_package.zig");
const statement = @import("general_statement.zig");
const relation = @import("../../language/relation.zig");
const record_abi = @import("../../language/record_abi.zig");

const Report = struct {
    schema: []const u8 = "s31-mixed-full-trace-audit-v1",
    fixed_root: []const u8,
    main_root: []const u8,
    interaction_root: []const u8,
    circuit_rows: usize,
    chip_rows: usize,
    bridge_rows: usize,
    verified: bool = true,
};

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 4) return error.ExpectedProofStatementAndAssignmentPaths;
    const proof = try std.fs.cwd().readFileAlloc(allocator, args[1], 16 << 20);
    defer allocator.free(proof);
    const statement_bytes = try std.fs.cwd().readFileAlloc(allocator, args[2], 1 << 20);
    defer allocator.free(statement_bytes);
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[3], 1 << 20);
    defer allocator.free(assignment_bytes);

    const source = @embedFile("s31_program_source");
    const air = @embedFile("s31_air_programs");
    var program = try relation.parseProgram(allocator, source);
    defer program.deinit();
    var assignment = try relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();

    const trace = if (program.value.version == 2) blk: {
        const words = try record_abi.claimedWords(allocator, program.value, statement_bytes);
        const result = try package.verifyEmbeddedAndInspectWithTraceAudit(
            source, air, allocator, words, proof, assignment.value);
        break :blk result.trace;
    } else blk: {
        var parsed = try std.json.parseFromSlice(statement.Statement, allocator,
            statement_bytes, .{ .ignore_unknown_fields = false });
        defer parsed.deinit();
        if (!std.mem.eql(u8, parsed.value.schema, statement.schema_name))
            return error.InvalidMixedStatementIdentity;
        const result = try package.verifyEmbeddedAndInspectWithTraceAudit(
            source, air, allocator, parsed.value.public_words, proof,
            assignment.value);
        try statement.check(&result.inspection, parsed.value);
        break :blk result.trace;
    };
    const fixed_hex = std.fmt.bytesToHex(trace.fixed_root, .lower);
    const main_hex = std.fmt.bytesToHex(trace.main_root, .lower);
    const interaction_hex = std.fmt.bytesToHex(trace.interaction_root, .lower);
    const report = try std.json.Stringify.valueAlloc(allocator, Report{
        .fixed_root = &fixed_hex,
        .main_root = &main_hex,
        .interaction_root = &interaction_hex,
        .circuit_rows = trace.circuit_rows,
        .chip_rows = trace.chip_rows,
        .bridge_rows = trace.bridge_rows,
    }, .{});
    defer allocator.free(report);
    std.debug.print("S31_MIXED_TRACE_AUDIT_V1 {s}\n", .{report});
}
