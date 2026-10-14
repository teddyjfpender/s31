"""Source guard for the two selected Gate PoW barriers and M31 predicate.

This only pins deterministic control flow and bytes. It does not establish
random-oracle independence, an adversary budget T, or native security bits.
"""
from __future__ import annotations

from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


def check_sources(component: str, runtime: str, frontend: str, pcs: str,
                  channel: str, hasher: str, profile: str, prove: str) -> None:
    if "pub const INTERACTION_POW_BITS: u32 = 20;" not in component:
        raise ValueError("selected interaction PoW bit count changed")
    if "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)" not in runtime:
        raise ValueError("selected Gate FRI PoW bit count changed")
    if "const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;" not in frontend or \
            "pub const profiles = core.vcs_lifted.channel_profile.proving_5a7c5ed;" not in prove:
        raise ValueError("selected Gate M31 profile changed")
    selected = profile[profile.index(
        "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{"):]
    ordered_once(selected, "selected M31 channel profile",
                 "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{",
                 ".m31_channel = true,", ".revision = .proving_5a7c5ed,")
    if "pub const Channel = channel_blake2s.Blake2sChannelGeneric(spec.m31_channel);" not in profile:
        raise ValueError("M31 channel profile constructor changed")

    direct = region(frontend, "fn verifyDirectProfile(", "fn sparseLogs(")
    ordered_once(direct, "Gate interaction PoW barrier",
                 "try scheme.commit(allocator, roots[1], component_logs.items[1], &channel);",
                 "if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))",
                 "return error.InvalidInteractionNonce;", "channel.mixU64(nonce);",
                 "const lookup = try core.channel.lookup_transcript.drawLookupElements(")
    fri = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    ordered_once(fri, "Gate FRI PoW barrier",
                 "var fri_verifier = try FriVerifier.commit(",
                 "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {",
                 "return verifier_types.VerificationError.ProofOfWork;",
                 "channel.mixU64(proof.proof_of_work);",
                 "fri_verifier.sampleQueryPositionsWithRaw(")

    generic = region(channel, "pub fn Blake2sChannelGeneric(", "/// PoW worker count:")
    if "const Hasher = blake2_hash.Blake2sHasherGeneric(is_m31_output);" not in generic:
        raise ValueError("PoW channel hasher changed")
    pow_source = region(generic, "pub fn verifyPowNonce(", "/// PoW predicate for eight candidates")
    ordered_once(pow_source, "PoW nonce hash input and predicate",
                 "const prefix = self.computePowPrefix(n_bits);",
                 "return verifyNonceWithPrefix(prefix, nonce, n_bits);",
                 "const prefix_bytes = u32ToBytesLe(POW_PREFIX);",
                 "prefixed_hasher.update(&[_]u8{0} ** 12);",
                 "prefixed_hasher.update(self.digest[0..]);",
                 "prefixed_hasher.update(bits_bytes[0..]);",
                 "return prefixed_hasher.finalize();",
                 "@memcpy(input[0..32], prefix[0..]);",
                 "@memcpy(input[32..40], nonce_bytes[0..]);",
                 "const out = Hasher.hashFixedSingleBlock(40, &input);",
                 "return trailingZeroBits(out[0..16]) >= n_bits;")
    if "pub const POW_PREFIX: u32 = 0x12345678;" not in generic:
        raise ValueError("PoW domain prefix changed")
    tail = region(channel, "fn trailingZeroBits(", "fn u32ToBytesLe(")
    ordered_once(tail, "little-endian low-bit PoW predicate",
                 "for (bytes) |b| {", "count += 8;", "count += @ctz(@as(u8, b));")
    fixed = region(hasher, "pub fn hashFixedSingleBlock(",
                   "pub fn hashFixedSingleBlockWithMode(")
    ordered_once(fixed, "M31-reduced PoW hash output",
                 "var out = blake2_backend.Blake2sHasher.hashFixedSingleBlock(byte_len, data);",
                 "if (is_m31_output) out = reduceToM31(out);", "return out;")
    reduce = region(hasher, "pub fn reduceToM31(", "fn readU32Le(")
    ordered_once(reduce, "M31 first-limb reduction",
                 "const p: V4 = @splat(m31.Modulus);",
                 "const folded = (input & p) +% (input >> @as(V4, @splat(31)));",
                 "const reduced = @select(u32, folded >= p, folded -% p, folded);")


def check_pcs_fri_pow_m31_predicate(root: Path) -> None:
    core = root / "deps/stwo-zig/src/core"
    check_sources(
        (root / "src/frontends/circuit/common/component_list.zig").read_text(),
        (root / "src/frontends/s31/runtime/mvp_runtime.zig").read_text(),
        (root / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
        (core / "pcs/verifier.zig").read_text(),
        (core / "channel/blake2s.zig").read_text(),
        (core / "vcs/blake2_hash.zig").read_text(),
        (core / "vcs_lifted/channel_profile.zig").read_text(),
        (root / "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig").read_text(),
    )
