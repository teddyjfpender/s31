//! Build-time source-embedded mixed 1..8 prover.
const std = @import("std");
const relation = @import("../../language/relation.zig");
const record_abi = @import("../../language/record_abi.zig");
const package = @import("general_package.zig");
const statement = @import("general_statement.zig");

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    // V2 consumes a canonical public-record statement supplied by the typed
    // frontend. Its eight flattened words must equal the evaluated source.
    // V1 retains the original three-argument CLI and statement bytes.
    const source = @embedFile("s31_program_source");
    var parsed = try relation.parseProgram(allocator, source);
    defer parsed.deinit();
    if (args.len != (if (parsed.value.version == 2) @as(usize, 5) else 4))
        return error.ExpectedAssignmentProofAndStatementPaths;
    const air = @embedFile("s31_air_programs");
    const assignment_bytes = try std.fs.cwd().readFileAlloc(allocator, args[1], 1 << 20);
    defer allocator.free(assignment_bytes);
    var assignment = try relation.parseAssignment(allocator, assignment_bytes);
    defer assignment.deinit();
    // Project the claimed statement here. The package performs the single
    // semantic evaluation and compares it with the native proof outputs before
    // returning; evaluating here as well repeats every chip round in the CLI.
    const public_words = try relation.claimedWords(allocator, parsed.value, assignment.value);
    const supplied_v2: ?[]u8 = if (parsed.value.version == 2) blk: {
        const supplied = try std.fs.cwd().readFileAlloc(allocator, args[4], 1 << 20);
        errdefer allocator.free(supplied);
        const claimed = try record_abi.claimedWords(allocator, parsed.value, supplied);
        if (!std.meta.eql(claimed, public_words)) return error.InvalidMixedPublicStatement;
        break :blk supplied;
    } else null;
    defer if (supplied_v2) |bytes| allocator.free(bytes);
    const sealed = try package.proveSealedAndInspect(allocator, source, air, assignment.value);
    defer allocator.free(sealed.bytes);
    const inspected = sealed.inspection;
    const source_hex = std.fmt.bytesToHex(inspected.schedule.source_sha256, .lower);
    const manifest_hex = std.fmt.bytesToHex(inspected.schedule.digest, .lower);
    const registry_hex = std.fmt.bytesToHex(inspected.registry_manifest_sha256, .lower);
    const identity_hex = std.fmt.bytesToHex(inspected.circuit_identity_sha256, .lower);
    const flat_statement_bytes: ?[]u8 = if (supplied_v2 == null) try std.json.Stringify.valueAlloc(allocator, statement.Statement{
        .schema = statement.schema_name,
        .source_sha256 = &source_hex,
        .selected_manifest_sha256 = &manifest_hex,
        .registry_manifest_sha256 = &registry_hex,
        .circuit_identity_sha256 = &identity_hex,
        .public_words = public_words,
    }, .{}) else null;
    defer if (flat_statement_bytes) |bytes| allocator.free(bytes);
    try std.fs.cwd().writeFile(.{ .sub_path = args[2], .data = sealed.bytes });
    try std.fs.cwd().writeFile(.{ .sub_path = args[3], .data = supplied_v2 orelse flat_statement_bytes.? });
    std.debug.print("proved\n", .{});
}
