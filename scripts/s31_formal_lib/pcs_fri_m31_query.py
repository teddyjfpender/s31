"""Source contract for the M31-masked native raw-query distribution.

This pins the selected path and key arithmetic stages. It does not prove the
hash words are uniform or independent; Lean makes that a conditional premise.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(queries: str, channel: str, hasher: str, m31: str,
                  profile: str, verifier: str, fri: str, pcs_verifier: str) -> None:
    draw = region(queries, "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    ordered_once(
        draw, "M31 masked raw queries",
        "const query_mask: u32 = (@as(u32, 1) << @intCast(log_domain_size)) - 1;",
        "var produced: usize = 0;",
        "while (produced < n_queries) {",
        "const words = channel.drawU32s();",
        "for (words) |word| {",
        "out[produced] = @as(usize, word & query_mask);",
        "produced += 1;",
        "if (produced == n_queries) break;",
        "return out;",
    )
    if "pub const FELTS_PER_HASH: usize = 8;" not in channel:
        raise ValueError("M31 channel batch width changed")
    if "pub const Blake2sM31Channel = Blake2sChannelGeneric(true);" not in channel:
        raise ValueError("M31 channel type changed")
    generic = region(channel, "pub fn Blake2sChannelGeneric(", "/// PoW worker count:")
    ordered_once(
        generic, "M31 channel hash selection",
        "const Hasher = blake2_hash.Blake2sHasherGeneric(is_m31_output);",
        "pub fn drawU32s(self: *Self)",
        "const hash = hashBytes(hash_input[0..]);",
        "out[i] = readU32Le(hash[base .. base + 4]);",
        "fn hashBytes(data: []const u8) Digest32 {",
    )
    draw_block = region(generic, "pub fn drawU32s(self: *Self)",
                        "pub fn drawSecureFelt(self: *Self)")
    ordered_once(
        draw_block, "M31 channel eight-lane digest order",
        "@memcpy(hash_input[0..32], self.digest[0..]);",
        "const counter = u32ToBytesLe(self.n_draws);",
        "hash_input[36] = 0;",
        "self.n_draws = nextDrawCounter(self.n_draws)",
        "const hash = hashBytes(hash_input[0..]);",
        "while (i < FELTS_PER_HASH) : (i += 1) {",
        "const base = i * 4;",
        "out[i] = readU32Le(hash[base .. base + 4]);",
        "return out;",
    )
    hash_fn = generic[generic.index("fn hashBytes(data: []const u8) Digest32 {"):]
    ordered_once(
        hash_fn, "M31 channel raw-word hash",
        "var hasher = Hasher.init();",
        "hasher.update(data);",
        "return hasher.finalize();",
    )
    if "pub const Blake2sM31Hasher = Blake2sHasherGeneric(true);" not in hasher:
        raise ValueError("M31 hasher type changed")
    finalize = region(hasher, "pub fn finalize(self: *Self)", "pub fn hash(data: []const u8)")
    ordered_once(
        finalize, "M31 hash output reduction",
        "var out = self.ctx.finalize();",
        "if (is_m31_output) out = reduceToM31(out);",
        "return out;",
    )
    reduce = region(hasher, "pub fn reduceToM31(", "fn readU32Le(")
    ordered_once(
        reduce, "M31 vector then scalar reduction",
        "const p: V4 = @splat(m31.Modulus);",
        "const folded = (input & p) +% (input >> @as(V4, @splat(31)));",
        "const reduced = @select(u32, folded >= p, folded -% p, folded);",
        "return @bitCast(words);",
        "const reduced = M31.fromU64(word);",
    )
    if "pub const Modulus: u32 = 0x7fffffff;" not in m31:
        raise ValueError("M31 modulus changed")
    if "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;" not in verifier:
        raise ValueError("S31 native verifier channel profile changed")
    sample = region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit(")
    ordered_once(
        sample, "FRI query raw and unique custody",
        "const first_layer_log_size = self.first_layer.column_commitment_domain.logSize();",
        "const raw = try queries_mod.drawQueries(\n"
        "                channel,\n"
        "                allocator,\n"
        "                first_layer_log_size,\n"
        "                self.config.n_queries,",
        "var new_queries = try queries_mod.Queries.init(\n"
        "                allocator,\n"
        "                raw,\n"
        "                first_layer_log_size,",
        "const unique = try allocator.dupe(usize, new_queries.positions);",
        "const retained_raw = try allocator.dupe(usize, raw);",
        "self.queries = new_queries;",
        "self.sampled_raw_queries = retained_raw;",
        "return .{",
        ".raw = raw,",
        ".unique = unique,",
    )
    pcs_sample = region(pcs_verifier, "channel.mixU64(proof.proof_of_work);",
                        "var query_capture_owned = true;")
    ordered_once(
        pcs_sample, "accepted PCS verifier query call",
        "channel.mixU64(proof.proof_of_work);",
        "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(\n"
        "                allocator,\n"
        "                channel,",
    )
    if "pub const Channel = channel_blake2s.Blake2sChannelGeneric(spec.m31_channel);" not in profile:
        raise ValueError("channel profile constructor changed")
    selected_profile = profile[profile.index(
        "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{"):]
    ordered_once(
        selected_profile, "selected S31 M31 channel profile",
        "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{",
        ".m31_channel = true,",
        ".revision = .proving_5a7c5ed,",
    )
    reduce64 = region(m31, "inline fn reduce64(", "inline fn reduceProduct(")
    ordered_once(
        reduce64, "scalar M31 reduction",
        "var t: u64 = (x & p) + (x >> 31);",
        "t = (t & p) + (t >> 31);",
        "return @min(r, r -% Modulus);",
    )


def check_pcs_fri_m31_query(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources(
        (core / "queries.zig").read_text(),
        (core / "channel/blake2s.zig").read_text(),
        (core / "vcs/blake2_hash.zig").read_text(),
        (core / "fields/m31.zig").read_text(),
        (core / "vcs_lifted/channel_profile.zig").read_text(),
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (core / "fri.zig").read_text(),
        (core / "pcs/verifier.zig").read_text(),
    )
