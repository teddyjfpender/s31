//! Public statement for the experimental, source-embedded mixed 1..8 binary.
//! Digest fields are redundant with the proof header, but make a saved
//! statement self-describing and catch accidental source/build mismatches.
const std = @import("std");
const package = @import("general_package.zig");

pub const schema_name = "s31-mixed-public-words-general-v3";

pub const Statement = struct {
    schema: []const u8,
    source_sha256: []const u8,
    selected_manifest_sha256: []const u8,
    registry_manifest_sha256: []const u8,
    circuit_identity_sha256: []const u8,
    public_words: [8]u32,
};

pub fn check(inspected: *const package.Inspection, value: Statement) !void {
    if (!std.mem.eql(u8, value.schema, schema_name) or
        !std.mem.eql(u8, value.source_sha256, &std.fmt.bytesToHex(inspected.schedule.source_sha256, .lower)) or
        !std.mem.eql(u8, value.selected_manifest_sha256, &std.fmt.bytesToHex(inspected.schedule.digest, .lower)) or
        !std.mem.eql(u8, value.registry_manifest_sha256, &std.fmt.bytesToHex(inspected.registry_manifest_sha256, .lower)) or
        !std.mem.eql(u8, value.circuit_identity_sha256, &std.fmt.bytesToHex(inspected.circuit_identity_sha256, .lower)))
        return error.InvalidMixedStatementIdentity;
}
