//! Bind a native S31 statement to the PCS mode selected by its sealed key.
//! The experimental CAS05 wire has no production S31 prover or verifier.
const std = @import("std");

pub const Mode = enum {
    legacy_postcard,
    cas05_sparse_v6,
};

pub const BoundLegacyProof = struct {
    public_words: [8]u32,
    proof_bytes: []const u8,
};

pub fn requireProduction(mode: Mode) !void {
    if (mode != .legacy_postcard) return error.Cas05NotProduction;
}

/// S31 wraps the serialized STARK proof in a profile-specific native header.
/// Check this reserved marker at the inner postcard decoder boundary as well.
pub fn requireLegacyPostcard(payload: []const u8) !void {
    if (std.mem.startsWith(u8, payload, "S31CAS05")) return error.WrongProofFormat;
}

/// Only the sealed key can choose `mode`. `public_words` must already have
/// been reconstructed from the independently supplied public statement.
pub fn bind(mode: Mode, public_words: [8]u32, proof_bytes: []const u8) !BoundLegacyProof {
    try requireProduction(mode);
    try requireLegacyPostcard(proof_bytes);
    return .{ .public_words = public_words, .proof_bytes = proof_bytes };
}

test "legacy selection carries the independently reconstructed statement" {
    const words = [8]u32{ 3, 5, 8, 13, 21, 34, 55, 89 };
    const proof = "S31NAT1\x00legacy postcard payload";
    const bound = try bind(.legacy_postcard, words, proof);
    try std.testing.expectEqual(words, bound.public_words);
    try std.testing.expectEqualSlices(u8, proof, bound.proof_bytes);
}

test "CAS05 key and proof-format confusion fail closed" {
    const words = [_]u32{0} ** 8;
    try std.testing.expectError(error.Cas05NotProduction, requireProduction(.cas05_sparse_v6));
    try std.testing.expectError(error.Cas05NotProduction, bind(.cas05_sparse_v6, words, "S31NAT1\x00"));
    try std.testing.expectError(error.Cas05NotProduction, bind(.cas05_sparse_v6, words, "S31CAS05\x06"));
    try std.testing.expectError(error.WrongProofFormat, bind(.legacy_postcard, words, "S31CAS05\x06"));
    try std.testing.expectError(error.WrongProofFormat, requireLegacyPostcard("S31CAS05\x06"));
    try requireLegacyPostcard("\x00\x01legacy postcard");
}
