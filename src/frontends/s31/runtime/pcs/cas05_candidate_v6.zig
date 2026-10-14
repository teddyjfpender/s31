//! Audit-only admission for a proposed S31 key/statement around CAS05 v6.
//! Matching bytes are never accepted as a production proof.
const std = @import("std");

const modulus: u32 = 2147483647;
const max_wire_bytes: usize = 64 << 20;
const max_key_bytes: usize = 16 << 10;
const max_statement_bytes: usize = 64 << 10;
const key_schema = "s31-verification-key-cas05-candidate-v1";
const statement_schema = "s31-public-statement-cas05-candidate-v1";

pub const Profile = struct {
    largest_log_size: u32,
    height_count: u16,
    log_blowup: u32,
    query_count: u32,
    columns: [8]u16,

    fn validate(self: Profile) !void {
        if (self.height_count < 2 or self.height_count > 8 or
            self.largest_log_size > 22 or
            self.largest_log_size < @as(u32, self.height_count) + 2 or
            self.log_blowup == 0 or
            @as(u64, self.height_count) + self.log_blowup > self.largest_log_size or
            self.query_count == 0 or self.query_count > (1 << 14))
            return error.InvalidCandidateProfile;
        var per_query_bytes: u64 = 4;
        for (self.columns[0..self.height_count]) |count| {
            if (count == 0 or count > 64) return error.InvalidCandidateProfile;
            per_query_bytes += 2 * @as(u64, count) * @sizeOf(u32);
        }
        for (self.columns[self.height_count..]) |count|
            if (count != 0) return error.InvalidCandidateProfile;
        if (per_query_bytes * self.query_count > max_wire_bytes - 128)
            return error.InvalidCandidateProfile;
    }

    fn terminalLength(self: Profile) usize {
        return @as(usize, 1) << @intCast(
            self.largest_log_size - @as(u32, self.height_count) - self.log_blowup,
        );
    }
};

pub const CandidateKey = struct {
    schema: []const u8,
    pcs_mode: []const u8,
    transcript_version: []const u8,
    source_wire_version: []const u8,
    program_sha256: []const u8,
    public_abi_sha256: ?[]const u8 = null,
    circuit_hash: []const u8,
    air_bundle_sha256: []const u8,
    profile: Profile,
};

pub const CandidateStatement = struct {
    schema: []const u8,
    verification_key_sha256: []const u8,
    public_words: [8]u32,
    source_root: []const u8,
    claims: []const []const [4]u32,
};

/// These values must be reconstructed independently of both the proof and
/// candidate JSON. In production they come from the installed verifier.
pub const Trusted = struct {
    sealed_key_bytes: []const u8,
    program_digest: [32]u8,
    public_abi_digest: ?[32]u8,
    circuit_hash: [32]u8,
    air_bundle_digest: [32]u8,
    public_words: [8]u32,
};

/// Check only the candidate format and independently supplied claims. The
/// draft CAS05 verifier, transcript replay, Merkle authentication and theorem
/// profile are unavailable in S31's pinned production engine.
pub fn inspect(
    allocator: std.mem.Allocator,
    trusted: Trusted,
    supplied_key_bytes: []const u8,
    statement_bytes: []const u8,
    wire: []const u8,
) !void {
    if (trusted.sealed_key_bytes.len > max_key_bytes or
        supplied_key_bytes.len > max_key_bytes or
        statement_bytes.len > max_statement_bytes)
        return error.CandidateMetadataTooLarge;
    if (!std.mem.eql(u8, trusted.sealed_key_bytes, supplied_key_bytes))
        return error.InvalidInstalledKey;
    var parsed_key = try std.json.parseFromSlice(
        CandidateKey,
        allocator,
        trusted.sealed_key_bytes,
        .{ .ignore_unknown_fields = false },
    );
    defer parsed_key.deinit();
    const key = parsed_key.value;
    if (!std.mem.eql(u8, key.schema, key_schema) or
        !std.mem.eql(u8, key.pcs_mode, "cas05_sparse_v6"))
        return error.InvalidInstalledKey;
    if (!std.mem.eql(u8, key.transcript_version, "S31CAS06") or
        !std.mem.eql(u8, key.source_wire_version, "S31XDM04"))
        return error.InvalidTranscriptVersion;
    try key.profile.validate();
    if (!sameDigest(key.program_sha256, trusted.program_digest) or
        !sameDigest(key.circuit_hash, trusted.circuit_hash) or
        !sameDigest(key.air_bundle_sha256, trusted.air_bundle_digest))
        return error.InvalidInstalledKey;
    if (trusted.public_abi_digest) |digest| {
        if (!sameDigest(key.public_abi_sha256 orelse return error.InvalidInstalledKey, digest))
            return error.InvalidInstalledKey;
    } else if (key.public_abi_sha256 != null) return error.InvalidInstalledKey;

    var parsed_statement = try std.json.parseFromSlice(
        CandidateStatement,
        allocator,
        statement_bytes,
        .{ .ignore_unknown_fields = false },
    );
    defer parsed_statement.deinit();
    const statement = parsed_statement.value;
    var key_digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(trusted.sealed_key_bytes, &key_digest, .{});
    if (!std.mem.eql(u8, statement.schema, statement_schema) or
        !sameDigest(statement.verification_key_sha256, key_digest) or
        !std.meta.eql(statement.public_words, trusted.public_words) or
        statement.claims.len != key.profile.height_count)
        return error.InvalidPublicStatement;
    var source_root: [32]u8 = undefined;
    if (statement.source_root.len != 64) return error.InvalidPublicStatement;
    _ = std.fmt.hexToBytes(&source_root, statement.source_root) catch return error.InvalidPublicStatement;
    if (!sameDigest(statement.source_root, source_root)) return error.InvalidPublicStatement;
    for (statement.claims, 0..) |height, i| {
        if (height.len != key.profile.columns[i]) return error.InvalidPublicStatement;
        for (height) |claim| for (claim) |limb|
            if (limb >= modulus) return error.InvalidPublicStatement;
    }
    try inspectWire(wire, key.profile, source_root, statement.claims);
    return error.Cas05NotProduction;
}

fn sameDigest(encoded: []const u8, expected: [32]u8) bool {
    return std.mem.eql(u8, encoded, &std.fmt.bytesToHex(expected, .lower));
}

const Cursor = struct {
    bytes: []const u8,
    at: usize = 0,

    fn take(self: *Cursor, count: usize) ![]const u8 {
        if (count > self.bytes.len - self.at) return error.TruncatedCandidateProof;
        const result = self.bytes[self.at..][0..count];
        self.at += count;
        return result;
    }
    fn readU16(self: *Cursor) !u16 {
        return std.mem.readInt(u16, (try self.take(2))[0..2], .little);
    }
    fn readU32(self: *Cursor) !u32 {
        return std.mem.readInt(u32, (try self.take(4))[0..4], .little);
    }
    fn felt(self: *Cursor) !u32 {
        const value = try self.readU32();
        if (value >= modulus) return error.NonCanonicalM31;
        return value;
    }
};

fn inspectWire(
    wire: []const u8,
    expected: Profile,
    expected_root: [32]u8,
    claims: []const []const [4]u32,
) !void {
    if (wire.len > max_wire_bytes) return error.CandidateProofTooLarge;
    var c = Cursor{ .bytes = wire };
    if (!std.mem.eql(u8, try c.take(8), "S31CAS05")) return error.WrongProofFormat;
    if (try c.readU16() != 6) return error.UnsupportedProofVersion;
    if (try c.readU16() != 0 or try c.readU32() != wire.len) return error.InvalidCandidateProof;
    const k = try c.readU32();
    const heights = try c.readU16();
    if (try c.readU16() != 0) return error.InvalidCandidateProof;
    const blowup = try c.readU32();
    const queries = try c.readU32();
    if (k != expected.largest_log_size or heights != expected.height_count or
        blowup != expected.log_blowup or queries != expected.query_count)
        return error.UnexpectedCandidateProfile;
    for (expected.columns[0..heights]) |count|
        if (try c.readU16() != count) return error.UnexpectedCandidateProfile;
    if (!std.mem.eql(u8, try c.take(32), &expected_root))
        return error.UnexpectedSourceRoot;
    // The sampled point is proof-supplied; only the future CAS05 transcript
    // replay can establish that it was actually drawn from the bound channel.
    for (0..8) |_| _ = try c.felt();
    for (claims) |height| for (height) |claim| for (claim) |limb|
        if (try c.felt() != limb) return error.UnexpectedCandidateClaims;

    const source_wire = try c.take(try c.readU32());
    try inspectSourceHeader(source_wire, expected, expected_root);
    if (try c.readU16() != heights - 1 or try c.readU16() != 0)
        return error.InvalidCandidateProof;
    for (0..heights - 1) |_| {
        _ = try c.take(32); // Unauthenticated line commitment until core replay.
        if (try c.readU32() != expected.query_count * 2) return error.InvalidCandidateProof;
        for (0..4 * expected.query_count * 2) |_| _ = try c.felt();
        const witness_count = try c.readU32();
        if (witness_count > (1 << 20)) return error.InvalidCandidateProof;
        _ = try c.take(@as(usize, witness_count) * 32);
    }
    if (try c.readU32() != expected.terminalLength()) return error.InvalidCandidateProof;
    for (0..expected.terminalLength() * 4) |_| _ = try c.felt();
    if (c.at != wire.len) return error.InvalidCandidateProof;
}

fn inspectSourceHeader(wire: []const u8, expected: Profile, root: [32]u8) !void {
    var c = Cursor{ .bytes = wire };
    if (!std.mem.eql(u8, try c.take(8), "S31XDM04")) return error.WrongSourceWireFormat;
    if (try c.readU16() != 4) return error.UnsupportedSourceWireVersion;
    if (try c.readU16() != 0 or try c.readU32() != wire.len) return error.InvalidCandidateProof;
    if (try c.readU32() != expected.largest_log_size or
        try c.readU16() != expected.height_count or
        try c.readU16() != 0 or
        try c.readU32() != expected.query_count)
        return error.UnexpectedCandidateProfile;
    for (expected.columns[0..expected.height_count]) |count|
        if (try c.readU16() != count) return error.UnexpectedCandidateProfile;
    if (!std.mem.eql(u8, try c.take(32), &root)) return error.UnexpectedSourceRoot;
    // Header equality is only an admission check. The future core verifier
    // must authenticate every sparse source opening in the remaining bytes.
}

fn appendU16(out: *std.ArrayList(u8), allocator: std.mem.Allocator, value: u16) !void {
    var bytes: [2]u8 = undefined;
    std.mem.writeInt(u16, &bytes, value, .little);
    try out.appendSlice(allocator, &bytes);
}

fn appendU32(out: *std.ArrayList(u8), allocator: std.mem.Allocator, value: u32) !void {
    var bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &bytes, value, .little);
    try out.appendSlice(allocator, &bytes);
}

/// Deliberately only header-shaped: a matching candidate must still fail.
fn testWire(
    allocator: std.mem.Allocator,
    profile: Profile,
    root: [32]u8,
    claims: []const []const [4]u32,
) ![]u8 {
    var source: std.ArrayList(u8) = .empty;
    defer source.deinit(allocator);
    try source.appendSlice(allocator, "S31XDM04");
    try appendU16(&source, allocator, 4);
    try appendU16(&source, allocator, 0);
    try appendU32(&source, allocator, 0);
    try appendU32(&source, allocator, profile.largest_log_size);
    try appendU16(&source, allocator, profile.height_count);
    try appendU16(&source, allocator, 0);
    try appendU32(&source, allocator, profile.query_count);
    for (profile.columns[0..profile.height_count]) |count|
        try appendU16(&source, allocator, count);
    try source.appendSlice(allocator, &root);
    std.mem.writeInt(u32, source.items[12..16], @intCast(source.items.len), .little);

    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);
    try out.appendSlice(allocator, "S31CAS05");
    try appendU16(&out, allocator, 6);
    try appendU16(&out, allocator, 0);
    try appendU32(&out, allocator, 0);
    try appendU32(&out, allocator, profile.largest_log_size);
    try appendU16(&out, allocator, profile.height_count);
    try appendU16(&out, allocator, 0);
    try appendU32(&out, allocator, profile.log_blowup);
    try appendU32(&out, allocator, profile.query_count);
    for (profile.columns[0..profile.height_count]) |count|
        try appendU16(&out, allocator, count);
    try out.appendSlice(allocator, &root);
    for (0..8) |_| try appendU32(&out, allocator, 0);
    for (claims) |height| for (height) |claim| for (claim) |limb|
        try appendU32(&out, allocator, limb);
    try appendU32(&out, allocator, @intCast(source.items.len));
    try out.appendSlice(allocator, source.items);
    try appendU16(&out, allocator, profile.height_count - 1);
    try appendU16(&out, allocator, 0);
    for (0..profile.height_count - 1) |_| {
        try out.appendSlice(allocator, &([_]u8{0x44} ** 32));
        try appendU32(&out, allocator, profile.query_count * 2);
        for (0..4 * profile.query_count * 2) |_| try appendU32(&out, allocator, 0);
        try appendU32(&out, allocator, 0);
    }
    try appendU32(&out, allocator, @intCast(profile.terminalLength()));
    for (0..profile.terminalLength() * 4) |_| try appendU32(&out, allocator, 0);
    std.mem.writeInt(u32, out.items[12..16], @intCast(out.items.len), .little);
    return out.toOwnedSlice(allocator);
}

test "candidate key, public statement and exact v6 wire header bind, then fail closed" {
    const allocator = std.testing.allocator;
    const program_digest = [_]u8{0x11} ** 32;
    const circuit_hash = [_]u8{0x22} ** 32;
    const air_digest = [_]u8{0x33} ** 32;
    const source_root = [_]u8{0x55} ** 32;
    const program_hex = std.fmt.bytesToHex(program_digest, .lower);
    const circuit_hex = std.fmt.bytesToHex(circuit_hash, .lower);
    const air_hex = std.fmt.bytesToHex(air_digest, .lower);
    const root_hex = std.fmt.bytesToHex(source_root, .lower);
    const profile = Profile{
        .largest_log_size = 6,
        .height_count = 2,
        .log_blowup = 1,
        .query_count = 2,
        .columns = .{ 1, 1, 0, 0, 0, 0, 0, 0 },
    };
    const key = CandidateKey{
        .schema = key_schema,
        .pcs_mode = "cas05_sparse_v6",
        .transcript_version = "S31CAS06",
        .source_wire_version = "S31XDM04",
        .program_sha256 = &program_hex,
        .circuit_hash = &circuit_hex,
        .air_bundle_sha256 = &air_hex,
        .profile = profile,
    };
    const key_bytes = try std.json.Stringify.valueAlloc(allocator, key, .{});
    defer allocator.free(key_bytes);
    var key_digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(key_bytes, &key_digest, .{});
    const key_hex = std.fmt.bytesToHex(key_digest, .lower);
    const words = [8]u32{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const height0 = [_][4]u32{.{ 1, 0, 0, 0 }};
    const height1 = [_][4]u32{.{ 2, 0, 0, 0 }};
    const claims = [_][]const [4]u32{ &height0, &height1 };
    var statement = CandidateStatement{
        .schema = statement_schema,
        .verification_key_sha256 = &key_hex,
        .public_words = words,
        .source_root = &root_hex,
        .claims = &claims,
    };
    const statement_bytes = try std.json.Stringify.valueAlloc(allocator, statement, .{});
    defer allocator.free(statement_bytes);
    const wire = try testWire(allocator, profile, source_root, &claims);
    defer allocator.free(wire);
    const trusted = Trusted{
        .sealed_key_bytes = key_bytes,
        .program_digest = program_digest,
        .public_abi_digest = null,
        .circuit_hash = circuit_hash,
        .air_bundle_digest = air_digest,
        .public_words = words,
    };
    try std.testing.expectError(error.Cas05NotProduction, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        wire,
    ));
    try std.testing.expectError(error.InvalidInstalledKey, inspect(
        allocator,
        trusted,
        "{}",
        statement_bytes,
        wire,
    ));
    var wrong_program = trusted;
    wrong_program.program_digest[0] ^= 1;
    try std.testing.expectError(error.InvalidInstalledKey, inspect(
        allocator,
        wrong_program,
        key_bytes,
        statement_bytes,
        wire,
    ));
    const injected_key = try std.mem.concat(allocator, u8, &.{
        "{\"proof_selected_mode\":\"legacy_postcard\",",
        key_bytes[1..],
    });
    defer allocator.free(injected_key);
    var injected_trusted = trusted;
    injected_trusted.sealed_key_bytes = injected_key;
    try std.testing.expectError(error.UnknownField, inspect(
        allocator,
        injected_trusted,
        injected_key,
        statement_bytes,
        wire,
    ));

    statement.public_words[0] = 99;
    const wrong_statement = try std.json.Stringify.valueAlloc(allocator, statement, .{});
    defer allocator.free(wrong_statement);
    try std.testing.expectError(error.InvalidPublicStatement, inspect(
        allocator,
        trusted,
        key_bytes,
        wrong_statement,
        wire,
    ));
    statement.public_words = words;
    statement.verification_key_sha256 = &root_hex;
    const wrong_key_statement = try std.json.Stringify.valueAlloc(allocator, statement, .{});
    defer allocator.free(wrong_key_statement);
    try std.testing.expectError(error.InvalidPublicStatement, inspect(
        allocator,
        trusted,
        key_bytes,
        wrong_key_statement,
        wire,
    ));

    var changed = try allocator.dupe(u8, wire);
    defer allocator.free(changed);
    changed[8] = 5;
    try std.testing.expectError(error.UnsupportedProofVersion, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[8] = 6;
    changed[36] ^= 1;
    try std.testing.expectError(error.UnexpectedSourceRoot, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[36] ^= 1;
    changed[100] ^= 1;
    try std.testing.expectError(error.UnexpectedCandidateClaims, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[100] ^= 1;
    changed[12] ^= 1;
    try std.testing.expectError(error.InvalidCandidateProof, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[12] ^= 1;
    // Prefix offset: 32-byte fixed header + two u16 column counts + root,
    // point, claims and the source-wire length.
    const nested_at: usize = 32 + 4 + 32 + 32 + 32 + 4;
    changed[nested_at] ^= 1;
    try std.testing.expectError(error.WrongSourceWireFormat, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[nested_at] ^= 1;
    changed[nested_at + 32] ^= 1;
    try std.testing.expectError(error.UnexpectedSourceRoot, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));
    changed[nested_at + 32] ^= 1;
    std.mem.writeInt(u32, changed[changed.len - 4 ..][0..4], modulus, .little);
    try std.testing.expectError(error.NonCanonicalM31, inspect(
        allocator,
        trusted,
        key_bytes,
        statement_bytes,
        changed,
    ));

    var wrong_tag_key = key;
    wrong_tag_key.transcript_version = "S31CAS05";
    const wrong_tag_bytes = try std.json.Stringify.valueAlloc(allocator, wrong_tag_key, .{});
    defer allocator.free(wrong_tag_bytes);
    var wrong_trusted = trusted;
    wrong_trusted.sealed_key_bytes = wrong_tag_bytes;
    try std.testing.expectError(error.InvalidTranscriptVersion, inspect(
        allocator,
        wrong_trusted,
        wrong_tag_bytes,
        statement_bytes,
        wire,
    ));
}
