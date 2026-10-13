"""Source contract for the M31-masked native raw-query distribution.

This pins the selected path and key arithmetic stages. It does not prove the
hash words are uniform or independent; Lean makes that a conditional premise.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(queries: str, channel: str, hasher: str, m31: str) -> None:
    draw = region(queries, "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    ordered_once(
        draw, "M31 masked raw queries",
        "const query_mask: u32 = (@as(u32, 1) << @intCast(log_domain_size)) - 1;",
        "const words = channel.drawU32s();",
        "out[produced] = @as(usize, word & query_mask);",
        "produced += 1;",
        "return out;",
    )
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
    )
