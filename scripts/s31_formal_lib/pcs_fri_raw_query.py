"""Source contract for the opt-in raw Gate FRI query sampler.

The Lean finite count is conditional on uniform independent raw words. This
guard identifies the native route that supplies those words and preserves raw
draws before deduplicating Merkle openings; it is not a BCS theorem.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(queries: str, channel: str, hasher: str, profile: str,
                  verifier: str, runtime: str, fri: str, pcs_verifier: str) -> None:
    draw = region(queries, "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    ordered_once(draw, "raw Gate masked FRI draw",
                 "const query_mask: u32 = (@as(u32, 1) << @intCast(log_domain_size)) - 1;",
                 "const words = channel.drawU32s();",
                 "out[produced] = @as(usize, word & query_mask);",
                 "if (produced == n_queries) break;")
    selected = region(profile,
                      "pub const Blake2sMerkleChannel = Blake2sMerkleChannelProfile(.{",
                      "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{")
    ordered_once(selected, "raw channel profile", ".m31_channel = false,",
                 ".revision = .proving_5a7c5ed,")
    ordered_once(profile, "raw channel generic selection",
                 "pub const Channel = channel_blake2s.Blake2sChannelGeneric(spec.m31_channel);",
                 "pub const MerkleHasher = blake2_merkle.Blake2sPlainMerkleHasher;")
    generic = region(channel, "pub fn Blake2sChannelGeneric(", "/// PoW worker count:")
    ordered_once(generic, "raw BLAKE2s word path",
                 "const Hasher = blake2_hash.Blake2sHasherGeneric(is_m31_output);",
                 "pub fn drawU32s(self: *Self)",
                 "const hash = hashBytes(hash_input[0..]);",
                 "out[i] = readU32Le(hash[base .. base + 4]);")
    finalize = region(hasher, "pub fn finalize(self: *Self)",
                      "pub fn hash(data: []const u8)")
    ordered_once(finalize, "raw hash reduction selector",
                 "var out = self.ctx.finalize();",
                 "if (is_m31_output) out = reduceToM31(out);",
                 "return out;")
    ordered_once(verifier, "raw native profile selection",
                 "const RawMC = cpu.prove.profiles.Blake2sMerkleChannel;",
                 "const RAW_GATE_MAGIC = \"S31NAT8R\";",
                 "pub fn verifyRawGate(",
                 "return verifyProfile(RawMC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);")
    if "if (raw_gate_channel)\n            try native.verifyRawGate(" not in runtime:
        raise ValueError("raw Gate runtime no longer selects raw native verifier")
    if "(if (raw_gate_channel) cpu.Root else cpu.Internal).prove(" not in runtime:
        raise ValueError("raw Gate runtime no longer selects raw native prover")
    sample = region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit(")
    ordered_once(sample, "raw and deduplicated FRI query custody",
                 "const raw = try queries_mod.drawQueries(",
                 "var new_queries = try queries_mod.Queries.init(",
                 "const retained_raw = try allocator.dupe(usize, raw);",
                 "self.sampled_raw_queries = retained_raw;")
    opened = region(pcs_verifier, "channel.mixU64(proof.proof_of_work);",
                    "var query_capture_owned = true;")
    ordered_once(opened, "accepted PCS query invocation",
                 "channel.mixU64(proof.proof_of_work);",
                 "var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(")


def check_pcs_fri_raw_query(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources(
        (core / "queries.zig").read_text(),
        (core / "channel/blake2s.zig").read_text(),
        (core / "vcs/blake2_hash.zig").read_text(),
        (core / "vcs_lifted/channel_profile.zig").read_text(),
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (root / "src/frontends/s31/runtime/mvp_runtime.zig").read_text(),
        (core / "fri.zig").read_text(),
        (core / "pcs/verifier.zig").read_text(),
    )
