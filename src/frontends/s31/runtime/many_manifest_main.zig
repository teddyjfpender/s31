//! Inspect the exact source-derived V4 component roster used by the native verifier.
const std = @import("std");
const binding = @import("bounded_compiled_binding.zig");

pub fn main() !void {
    const allocator = std.heap.smp_allocator;
    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);
    if (args.len != 1) return error.UnexpectedManifestInspectorArguments;

    var inspected = try binding.inspectMany(
        allocator,
        @embedFile("s31_program_source"),
        @embedFile("s31_air_programs"),
    );
    defer inspected.deinit();
    const report = .{
        .schema = "s31-many-component-inspection-v4",
        .manifest_precommitment_sha256 = std.fmt.bytesToHex(inspected.manifest_precommitment, .lower),
        .effective_source_sha256 = std.fmt.bytesToHex(inspected.effective_source_digest, .lower),
        .circuit_identity_sha256 = std.fmt.bytesToHex(inspected.circuit_identity, .lower),
        .manifest = inspected.generated.value,
    };
    const json = try std.json.Stringify.valueAlloc(allocator, report, .{});
    defer allocator.free(json);
    var buffer: [4096]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buffer);
    try stdout.interface.writeAll(json);
    try stdout.interface.writeByte('\n');
    try stdout.interface.flush();
}
