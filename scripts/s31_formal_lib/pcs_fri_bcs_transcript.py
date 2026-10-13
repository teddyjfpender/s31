"""Independent byte-level model of the selected S31 direct Gate transcript.

This is a deterministic refinement fixture and source audit, not a random
oracle, BCS, or grinding soundness proof. The 8-bit fixture difficulties keep
the tests fast; production difficulties remain pinned by the release matrix.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region


ROOT = Path(__file__).resolve().parents[2]
P = (1 << 31) - 1


def _u32(value: int) -> bytes:
    if not 0 <= value < 1 << 32:
        raise ValueError("non-u32 transcript word")
    return value.to_bytes(4, "little")


def _felt(limbs: tuple[int, int, int, int]) -> bytes:
    if len(limbs) != 4 or any(not 0 <= x < P for x in limbs):
        raise ValueError("noncanonical QM31 limb")
    return b"".join(_u32(x) for x in limbs)


def _h(data: bytes) -> bytes:
    # The chosen channel is Blake2sM31: every output word, including PoW
    # prefixes and challenge blocks, is reduced independently modulo p.
    digest = hashlib.blake2s(data, digest_size=32).digest()
    return b"".join(_u32(int.from_bytes(digest[i:i + 4], "little") % P)
                    for i in range(0, 32, 4))


@dataclass
class Channel:
    digest: bytes = bytes(32)
    counter: int = 0

    def _absorb(self, data: bytes) -> None:
        self.digest = _h(self.digest + data)
        self.counter = 0

    def mix_u64(self, value: int) -> None:
        if not 0 <= value < 1 << 64:
            raise ValueError("non-u64 transcript word")
        self._absorb(value.to_bytes(8, "little"))

    def mix_u32s(self, words: tuple[int, ...]) -> None:
        self._absorb(b"".join(_u32(word) for word in words))

    def mix_root(self, root: bytes) -> None:
        if len(root) != 32:
            raise ValueError("root must be 32 bytes")
        self._absorb(root)

    def mix_felts(self, felts: tuple[tuple[int, int, int, int], ...]) -> None:
        self._absorb(b"".join(_felt(felt) for felt in felts))

    def draw_words(self) -> tuple[int, ...]:
        if self.counter >= (1 << 32) - 1:
            # Native nextDrawCounter refuses the increment before hashing.
            raise OverflowError("native draw counter exhausted")
        data = self.digest + _u32(self.counter) + b"\x00"
        self.counter += 1
        block = _h(data)
        return tuple(int.from_bytes(block[i:i + 4], "little") for i in range(0, 32, 4))

    def draw_secure(self) -> tuple[int, int, int, int]:
        while True:
            words = self.draw_words()
            if all(x < 2 * P for x in words):
                return tuple(x % P for x in words[:4])  # type: ignore[return-value]

    def draw_lookup_pair(self) -> tuple[tuple[int, ...], tuple[int, ...]]:
        # Native drawSecureFelts(2) consumes one accepted eight-word block.
        while True:
            words = self.draw_words()
            if all(x < 2 * P for x in words):
                return tuple(x % P for x in words[:4]), tuple(x % P for x in words[4:])

    def pow_valid(self, bits: int, nonce: int) -> bool:
        if not 0 <= bits <= 32 or not 0 <= nonce < 1 << 64:
            raise ValueError("unsupported PoW fixture")
        prefix = _h(_u32(0x12345678) + bytes(12) + self.digest + _u32(bits))
        digest = _h(prefix + nonce.to_bytes(8, "little"))
        first128 = int.from_bytes(digest[:16], "little")
        return first128 & ((1 << bits) - 1) == 0

    def first_valid_nonce(self, bits: int) -> int:
        # A small deterministic fixture only; production prover ordering is
        # covered by native pow_order and irrelevant to verifier soundness.
        for nonce in range(1 << 16):
            if self.pow_valid(bits, nonce):
                return nonce
        raise ValueError("fixture PoW search exhausted")

    def raw_queries(self, count: int, log_size: int) -> list[int]:
        if not 0 <= log_size <= 31 or not 0 <= count <= 1_000_000:
            raise ValueError("invalid fixture query geometry")
        out: list[int] = []
        while len(out) < count:
            out.extend(x & ((1 << log_size) - 1) for x in self.draw_words())
        return out[:count]


def fixture() -> dict[str, object]:
    c = Channel()
    epochs: list[dict[str, object]] = []

    def mark(stage: str) -> None:
        epochs.append({"stage": stage, "digest": c.digest.hex(), "counter": c.counter})

    # Direct Gate profile with an all-zero source digest, no chip and no
    # private boundary. The fixture follows the actual mixProfile encoding.
    c.mix_u64(0x5333314449523401)
    c.mix_u32s((0,) * 8)
    c.mix_u32s((0, 0, 0))
    c.mix_felts(((0, 0, 0, 0),))  # lookup channel salt
    c.mix_felts(((8, 1, 70, 0), (1, 0, 0, 0)))  # test FriConfigV2
    c.mix_root(bytes([1]) * 32)  # fixed
    c.mix_root(bytes([2]) * 32)  # circuit identity
    c.mix_felts(tuple((x, 0, 0, 0) for x in range(8)))
    c.mix_root(bytes([3]) * 32)  # main
    mark("before_interaction_pow")
    interaction_nonce = c.first_valid_nonce(8)
    c.mix_u64(interaction_nonce)
    mark("after_interaction_pow")
    lookup_z, lookup_alpha = c.draw_lookup_pair()
    mark("after_lookup_draw")
    c.mix_felts(((9, 10, 11, 12),))  # interaction claim
    c.mix_root(bytes([4]) * 32)  # interaction
    composition_randomness = c.draw_secure()
    c.mix_root(bytes([5]) * 32)  # composition
    oods_seed = c.draw_secure()
    c.mix_felts(((13, 14, 15, 16), (17, 18, 19, 20)))  # samples
    deep = c.draw_secure()
    c.mix_root(bytes([6]) * 32)  # first FRI layer
    first_alpha = c.draw_secure()
    c.mix_root(bytes([7]) * 32)  # one inner FRI layer
    inner_alpha = c.draw_secure()
    c.mix_felts(((21, 22, 23, 24), (25, 26, 27, 28)))  # last coefficients
    mark("before_fri_pow")
    fri_nonce = c.first_valid_nonce(8)
    c.mix_u64(fri_nonce)
    mark("after_fri_pow")
    queries = c.raw_queries(70, 21)
    mark("after_queries")
    return {
        "epochs": epochs, "interaction_nonce": interaction_nonce,
        "fri_nonce": fri_nonce, "lookup_z": lookup_z,
        "lookup_alpha": lookup_alpha,
        "composition_randomness": composition_randomness,
        "oods_seed": oods_seed, "deep": deep,
        "first_alpha": first_alpha, "inner_alpha": inner_alpha,
        "queries": queries,
    }


def audit_sources(frontend: str, verifier: str, pcs: str, fri: str,
                  channel: str, merkle: str, lookup: str, config: str,
                  queries: str, profile: str, profile_alias: str,
                  hash_source: str) -> None:
    direct = region(frontend, "fn verifyDirectProfile(", "fn sparseLogs(")
    ordered_once(direct, "direct Gate transcript",
                 "var channel = MC.Channel{};",
                 "cpu.direct_arithmetic.mixProfile(&channel,",
                 "core.channel.lookup_transcript.mixChannelSalt(&channel, 0);",
                 "pcs.fri_config.mixInto(&channel);",
                 "try scheme.commit(allocator, roots[0],",
                 "MC.mixRoot(&channel, circuit_hash);",
                 "channel.mixFelts(&outputs);",
                 "try scheme.commit(allocator, roots[1],",
                 "if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))",
                 "channel.mixU64(nonce);",
                 "core.channel.lookup_transcript.drawLookupElements(allocator, &channel);",
                 "core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..sum_count]);",
                 "try scheme.commit(allocator, roots[2],",
                 "core.verifier.verifyBorrowedExWithProofCapture(")
    if ("if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))\n"
            "        return error.InvalidInteractionNonce;") not in direct:
        raise ValueError("interaction PoW rejection barrier changed")
    if "return verifyDirectProfile(allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, source_digest, null, null, true);" not in frontend:
        raise ValueError("bound direct Gate entrypoint changed")
    if direct.count("const MC =") or not frontend.count("const MC = cpu.prove.profiles.Blake2sM31MerkleChannel;") == 1:
        raise ValueError("selected native channel changed")
    if "pub const profiles = core.vcs_lifted.channel_profile.proving_5a7c5ed;" not in profile_alias:
        raise ValueError("selected channel profile alias changed")
    profile_mix = region(profile, "pub fn mixProfile(", "pub fn identityHash(")
    ordered_once(profile_mix, "direct profile encoding",
                 "channel.mixU64(if (request.private_boundary != null) private_profile_tag else profile_tag);",
                 "std.mem.readInt(u32, request.source_digest[4 * i ..][0..4], .little);",
                 "channel.mixU32s(&words);",
                 "channel.mixU32s(&.{ 1, item.rounds, item.constant.toU32() })",
                 "channel.mixU32s(&.{ 0, 0, 0 });")
    if "pub const profile_tag: u64 = 0x5333314449523401;" not in profile:
        raise ValueError("direct Gate profile tag changed")
    core_verify = region(verifier, "fn verifyImpl(", "fn pointFromOodsSeed(")
    ordered_once(core_verify, "core OODS transcript",
                 "const composition_randomness = channel.drawSecureFelt();",
                 "try commitment_scheme.commit(",
                 "const oods_seed = channel.drawSecureFelt();",
                 "commitment_scheme.verifyValuesWithBorrowedProofCapture(")
    pcs_impl = region(pcs, "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    ordered_once(pcs_impl, "PCS FRI transcript",
                 "channel.mixFelts(sampled_values_flat);",
                 "const deep_randomness = channel.drawSecureFelt();",
                 "var fri_verifier = try FriVerifier.commit(",
                 "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work))",
                 "channel.mixU64(proof.proof_of_work);",
                 "fri_verifier.sampleQueryPositionsWithRaw(")
    if ("if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work)) {\n"
            "                return verifier_types.VerificationError.ProofOfWork;\n"
            "            }") not in pcs_impl:
        raise ValueError("FRI PoW rejection barrier changed")
    fri_commit = region(fri, "pub fn commit(", "pub fn sampleQueryPositions(")
    ordered_once(fri_commit, "FRI rounds",
                 "MC.mixRoot(channel, proof_in.first_layer.commitment);",
                 ".folding_alpha = channel.drawSecureFelt(),\n                .proof =",
                 "MC.mixRoot(channel, inner_proof.commitment);",
                 ".folding_alpha = channel.drawSecureFelt(),\n                    .layer_index = i,",
                 "channel.mixFelts(last_layer_poly.coefficients());")
    ordered_once(merkle, "Merkle root encoding", "const digest = channel.digestBytes();",
                 "channel.updateDigest(", "concatAndHash(digest, root)")
    ordered_once(config, "FRI config encoding",
                 "QM31.fromU32Unchecked(self.pow_bits, self.log_blowup_factor, self.n_queries, self.log_last_layer_degree_bound)",
                 "QM31.fromU32Unchecked(self.fold_step, 0, 0, 0)")
    ordered_once(lookup, "lookup pair draw", "const values = try channel.drawSecureFelts(allocator, 2);",
                 ".z = values[0], .alpha = values[1]")
    ordered_once(queries, "raw query blocks", "while (produced < n_queries)",
                 "const words = channel.drawU32s();", "out[produced] = @as(usize, word & query_mask);")
    query_loop = region(queries, "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    if re.findall(r"channel\.[A-Za-z0-9_]+\(", query_loop) != ["channel.drawU32s("]:
        raise ValueError("raw query loop gained an extra channel operation")
    fri_query = region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit(")
    ordered_once(fri_query, "configured FRI query count",
                 "const raw = try queries_mod.drawQueries(",
                 "self.config.n_queries,", "var new_queries = try queries_mod.Queries.init(")
    for label, start, end, stages in (
        ("field absorption", "pub fn mixFelts(", "pub fn mixU32s(",
         ("hasher.update(self.digest[0..]);", "self.updateDigest(hasher.finalize());")),
        ("word absorption", "pub fn mixU32s(", "pub fn mixU64(",
         ("hasher.update(self.digest[0..]);", "self.updateDigest(hasher.finalize());")),
        ("nonce absorption", "pub fn mixU64(", "pub fn drawU32s(",
         ("self.mixU32s(&[_]u32{", "@truncate(value),", "@truncate(value >> 32)")),
        ("draw encoding", "pub fn drawU32s(", "pub fn drawSecureFelt(",
         ("const counter = u32ToBytesLe(self.n_draws);", "hash_input[36] = 0;",
          "self.n_draws = nextDrawCounter(self.n_draws)", "const hash = hashBytes(hash_input[0..]);")),
        ("PoW encoding", "pub fn computePowPrefix(", "fn verifyNonceWithPrefix(",
         ("u32ToBytesLe(POW_PREFIX)", "u32ToBytesLe(n_bits)",
          "prefixed_hasher.update(&[_]u8{0} ** 12);",
          "prefixed_hasher.update(self.digest[0..]);",
          "return prefixed_hasher.finalize();")),
    ):
        ordered_once(region(channel, start, end), label, *stages)
    if "self.n_draws = 0;" not in region(channel, "pub inline fn updateDigest(", "pub fn mixFelts("):
        raise ValueError("absorption no longer resets draw epoch")
    if "return std.math.add(u32, current, 1) catch error.DrawCounterExhausted;" not in channel or \
       "self.n_draws = nextDrawCounter(self.n_draws) catch @panic(\"BLAKE2s draw counter exhausted\");" not in channel:
        raise ValueError("draw counter no longer fails closed")
    if "std.mem.sliceAsBytes(felts)" not in channel or "std.mem.sliceAsBytes(data)" not in channel:
        raise ValueError("little-endian absorption encoding changed")
    for offset in (8, 16, 24, 32, 40, 48, 56):
        if f"@truncate(x >> {offset})" not in region(channel, "fn u64ToBytesLe(", "fn readU32Le("):
            raise ValueError("u64 nonce encoding changed")
    for offset in (8, 16, 24):
        if f"@truncate(x >> {offset})" not in region(channel, "fn u32ToBytesLe(", "fn u64ToBytesLe("):
            raise ValueError("u32 counter encoding changed")
    if "pub const POW_PREFIX: u32 = 0x12345678;" not in channel:
        raise ValueError("PoW domain prefix changed")
    pow_verify = region(channel, "pub fn verifyPowNonce(", "pub fn computePowPrefix(")
    ordered_once(pow_verify, "PoW predicate dispatch",
                 "const prefix = self.computePowPrefix(n_bits);",
                 "return verifyNonceWithPrefix(prefix, nonce, n_bits);")
    if "const out = Hasher.hashFixedSingleBlock(40, &input);" not in channel:
        raise ValueError("PoW nonce hash changed")
    if "@memcpy(input[0..32], prefix[0..]);" not in channel or \
       "@memcpy(input[32..40], nonce_bytes[0..]);" not in channel:
        raise ValueError("PoW nonce encoding changed")
    if "return trailingZeroBits(out[0..16]) >= n_bits;" not in channel:
        raise ValueError("PoW predicate changed")
    if "if (x >= two_p)" not in region(channel, "fn drawBaseFelts(", "fn hashBytes("):
        raise ValueError("secure challenge rejection changed")
    if "const two_p = 2 * m31.Modulus;" not in channel or "M31.fromU64(x)" not in channel:
        raise ValueError("secure challenge reduction changed")
    if "return QM31.fromM31Array(.{ felts[0], felts[1], felts[2], felts[3] });" not in channel:
        raise ValueError("secure challenge limb selection changed")
    if "i += qm31.SECURE_EXTENSION_DEGREE" not in channel or \
       "out[produced] = QM31.fromM31Array" not in channel:
        raise ValueError("lookup pair draw packing changed")
    if "if (is_m31_output) out = reduceToM31(out);" not in hash_source or \
       "const reduced = @select(u32, folded >= p, folded -% p, folded);" not in hash_source:
        raise ValueError("M31 channel digest reduction changed")
    # The direct Gate path must contain no other direct channel operation.
    calls = re.findall(r"\bchannel\.(mix\w+|draw\w+|verifyPowNonce)\(", direct)
    if calls != ["mixFelts", "verifyPowNonce", "mixU64"]:
        raise ValueError(f"unexpected direct channel operation: {calls}")


def audit(root: Path = ROOT) -> dict[str, object]:
    names = (
        "src/frontends/s31/runtime/native_verifier.zig",
        "deps/stwo-zig/src/core/verifier.zig",
        "deps/stwo-zig/src/core/pcs/verifier.zig",
        "deps/stwo-zig/src/core/fri.zig",
        "deps/stwo-zig/src/core/channel/blake2s.zig",
        "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig",
        "deps/stwo-zig/src/core/channel/lookup_transcript.zig",
        "deps/stwo-zig/src/core/pcs/config_v2.zig",
        "deps/stwo-zig/src/core/queries.zig",
        "deps/stwo-zig/src/integrations/circuit_cpu/direct_arithmetic.zig",
        "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig",
        "deps/stwo-zig/src/core/vcs/blake2_hash.zig",
    )
    audit_sources(*((root / name).read_text() for name in names))
    saved_fixture = json.loads((root / "formal/s31/tests/pcs_fri_bcs_transcript.json").read_text())
    fresh_fixture = json.loads(json.dumps(fixture()))
    if saved_fixture != fresh_fixture:
        raise ValueError("independent transcript fixture changed or is stale")
    pinned = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True).strip()
    checked = subprocess.check_output(["git", "-C", str(root / "deps/stwo-zig"), "rev-parse", "HEAD"], text=True).strip()
    if checked != pinned:
        raise ValueError("native engine differs from pinned gitlink")
    return {"native_sources_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                                      for name in names}, "engine_gitlink_commit": pinned, "fixture": fresh_fixture,
            "proven_native_bcs_soundness": False}


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
