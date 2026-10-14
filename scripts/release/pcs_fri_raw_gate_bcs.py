#!/usr/bin/env python3
"""Source-bound raw Gate transcript inventory and conditional BCS arithmetic.

The fixture is a deterministic byte replay, not a proof-acceptance fixture.
Fixed-prefix sampling counts and hypothetical ROM arithmetic do not establish
adaptive Fiat-Shamir/BCS security for the installed verifier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.s31_formal_lib.pcs_fri_bcs_transcript import Channel, P, _u32
from scripts.s31_formal_lib.pcs_fri_order import ordered_once, region

ROOT = Path(__file__).resolve().parents[2]
ENGINE_COMMIT = "59e1f115250b8af01712b9bf3d71616e53094964"
ENGINE_SHA256 = {
    "deps/stwo-zig/src/frontends/circuit/common/component_list.zig": "d2f1e8facad581464f365958fb8e9fb9270fb28c09363b8361898df4136ceb2b",
    "deps/stwo-zig/src/core/channel/blake2s.zig": "fe0598dd15f70cc84b7098684b6a6f2e0ec319c4f7b5390c3ccd5f781ca32fc1",
    "deps/stwo-zig/src/core/vcs/blake2_hash.zig": "5600b1d1af9730403bb759b0dd4d7463efa5772cc2d95c567bd26c9d5315b1f0",
    "deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig": "93d77873303bdb149114d7222f60b84065b0fcb41bda556ce1b0c0a78dea0a0f",
    "deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig": "5c5da473db0ab9539ff12db3d1f244cab615741f2f96f66af3a5caaf3388e102",
    "deps/stwo-zig/src/core/queries.zig": "68e13fbb48c0cd684b94198c5452e003984237a2fe2000dd332ac57234328bce",
    "deps/stwo-zig/src/core/pcs/verifier.zig": "e119335172e17db5fd1345f476c7f6ad7fdf67e394a5b18d5c2085e892ffe3d5",
    "deps/stwo-zig/src/core/fri.zig": "5f84501d1ffbaf5d33d6f7063bea7e6fd88a4cb65140ff360b75cb11f812121f",
    "deps/stwo-zig/src/core/verifier.zig": "85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381",
    "deps/stwo-zig/src/core/channel/lookup_transcript.zig": "3180e2d704a07547a1df3a4c2da3b2dc675b7e18fb8715e39d889f8ddc9bc991",
    "deps/stwo-zig/src/core/pcs/config_v2.zig": "b58f464074d5c8ca5e002764e529afc9f3e1fe81f12320a180fc1f850ef05178",
}
FRONTEND = "src/frontends/s31/runtime/native_verifier.zig"
RUNTIME = "src/frontends/s31/runtime/mvp_runtime.zig"
TARGET = Fraction(1, 1 << 96)
T = 1 << 64


class RawChannel(Channel):
    """Independent Python BLAKE2s-256 byte model of the raw Zig channel."""

    def _absorb(self, data: bytes) -> None:
        self.digest = hashlib.blake2s(self.digest + data, digest_size=32).digest()
        self.counter = 0

    def draw_words(self) -> tuple[int, ...]:
        if self.counter >= (1 << 32) - 1:
            raise OverflowError("native draw counter exhausted before wrap")
        preimage = self.digest + _u32(self.counter) + b"\x00"
        self.counter += 1
        block = hashlib.blake2s(preimage, digest_size=32).digest()
        return tuple(int.from_bytes(block[i:i + 4], "little") for i in range(0, 32, 4))

    def pow_valid(self, bits: int, nonce: int) -> bool:
        if not 0 <= bits <= 32 or not 0 <= nonce < 1 << 64:
            raise ValueError("invalid fixture PoW input")
        prefix = hashlib.blake2s(
            _u32(0x12345678) + bytes(12) + self.digest + _u32(bits),
            digest_size=32,
        ).digest()
        output = hashlib.blake2s(prefix + nonce.to_bytes(8, "little"), digest_size=32).digest()
        return (int.from_bytes(output[:4], "little") & ((1 << bits) - 1)) == 0


def fixture() -> dict:
    """Synthetic accepted nonce/challenge *transcript*, not an accepted proof."""
    c = RawChannel()
    epochs = []

    def mark(stage: str) -> None:
        epochs.append({"stage": stage, "digest": c.digest.hex(), "counter": c.counter})

    # Plain ordinary Gate has no direct-profile source tag. The proof format
    # selector is checked before this channel sequence by native verifyProfile.
    c.mix_felts(((0, 0, 0, 0),))  # channel salt 0
    c.mix_felts(((8, 1, 70, 0), (1, 0, 0, 0)))  # pedagogical 8-bit FRI PoW
    c.mix_root(bytes([1]) * 32)  # fixed root
    c.mix_root(bytes([2]) * 32)  # circuit identity
    c.mix_felts(tuple((x, 0, 0, 0) for x in range(8)))  # public output words
    c.mix_root(bytes([3]) * 32)  # main root
    mark("before_interaction_pow")
    interaction_nonce = c.first_valid_nonce(8)
    c.mix_u64(interaction_nonce)
    mark("after_interaction_pow")
    lookup_z, lookup_alpha = c.draw_lookup_pair()
    mark("after_lookup_draw")
    c.mix_felts(((9, 10, 11, 12),))  # synthetic interaction claim
    c.mix_root(bytes([4]) * 32)  # interaction root
    composition = c.draw_secure()
    c.mix_root(bytes([5]) * 32)  # composition root
    oods = c.draw_secure()
    c.mix_felts(((13, 14, 15, 16), (17, 18, 19, 20)))  # OOD values
    deep = c.draw_secure()
    c.mix_root(bytes([6]) * 32)  # first FRI layer
    first_alpha = c.draw_secure()
    c.mix_root(bytes([7]) * 32)  # one inner FRI layer
    inner_alpha = c.draw_secure()
    c.mix_felts(((21, 22, 23, 24), (25, 26, 27, 28)))  # terminal polynomial
    mark("before_fri_pow")
    fri_nonce = c.first_valid_nonce(8)
    c.mix_u64(fri_nonce)
    mark("after_fri_pow")
    query_digest = c.digest.hex()
    queries = c.raw_queries(70, 21)
    mark("after_queries")
    return {
        "schema": "s31-raw-gate-bcs-transcript-fixture-v1",
        "scope": "synthetic_plain_gate_channel_replay_only",
        "epochs": epochs,
        "interaction_nonce": interaction_nonce,
        "fri_nonce": fri_nonce,
        "lookup_z": lookup_z,
        "lookup_alpha": lookup_alpha,
        "composition_randomness": composition,
        "oods_seed": oods,
        "deep": deep,
        "first_alpha": first_alpha,
        "inner_alpha": inner_alpha,
        "query_digest": query_digest,
        "queries": queries,
    }


def audit_source_shapes(frontend: str, runtime: str, engine: dict[str, str]) -> None:
    components = region(engine["deps/stwo-zig/src/frontends/circuit/common/component_list.zig"],
                        "pub const ComponentList = enum(u8) {", "/// `ComponentList::idx`:")
    if len(re.findall(r"^    [a-z0-9_]+,$", components, re.MULTILINE)) != 11 or \
       "pub const INTERACTION_POW_BITS: u32 = 20;" not in engine["deps/stwo-zig/src/frontends/circuit/common/component_list.zig"]:
        raise ValueError("raw proof header component count or interaction PoW changed")
    if "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)" not in runtime:
        raise ValueError("raw Gate FRI parameters changed")
    if "const HEADER_LEN = MAGIC.len + 8 + N_COMPONENTS * 16;" not in frontend:
        raise ValueError("raw Gate header shape changed")
    raw_entry = region(frontend, "pub fn verifyRawGate(", "/// Authenticate a full gate-profile proof")
    ordered_once(raw_entry, "raw Gate verifier entry", "pub fn verifyRawGate(",
                 "return verifyProfile(RawMC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);")
    verify = region(frontend, "fn verifyProfile(", "fn logsFor(")
    ordered_once(verify, "raw Gate proof and root epochs",
                 "const magic = if (hybrid) HYBRID_MAGIC else if (Profile == RawMC) RAW_GATE_MAGIC else MAGIC;",
                 "raw.len < header_len or raw.len > (16 << 20)",
                 "std.mem.readInt(u64, raw[magic.len..][0..8], .little);",
                 "sum.* = QM31.fromU32Unchecked(limbs[0], limbs[1], limbs[2], limbs[3]);",
                 "try pcs_mode_binding.requireLegacyPostcard(proof_bytes);",
                 "const decode_memory = try allocator.alloc(u8, 64 << 20);",
                 "try postcard.deserializeProof(H, bounded.allocator(), stream.reader());",
                 "if (stream.pos != proof_bytes.len or stark.commitment_scheme_proof.commitments.items.len != 4)",
                 "if (!std.meta.eql(stark.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))",
                 "if (!std.mem.eql(u8, &preprocessed_root, &roots[0]))",
                 "var channel = Profile.Channel{};",
                 "core.channel.lookup_transcript.mixChannelSalt(&channel, 0);",
                 "pcs.fri_config.mixInto(&channel);",
                 "try scheme.commit(allocator, roots[0], &pp_logs, &channel);",
                 "Profile.mixRoot(&channel, circuit_hash);",
                 "channel.mixFelts(&outputs);",
                 "try scheme.commit(allocator, roots[1], main_logs, &channel);",
                 "if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))",
                 "channel.mixU64(nonce);",
                 "core.channel.lookup_transcript.drawLookupElements(allocator, &channel);",
                 "core.channel.lookup_transcript.mixInteractionClaim(&channel, &sums);",
                 "try scheme.commit(allocator, roots[2], interaction_logs, &channel);",
                 "try core.verifier.verifyBorrowedExWithProofCapture(")
    if "const RAW_GATE_MAGIC = \"S31NAT8R\";" not in frontend:
        raise ValueError("raw proof-format selector changed")
    if "if (limb.* >= core.fields.m31.Modulus) return error.InvalidNativeProof;" not in region(
            verify, "var sums: [N_COMPONENTS]QM31", "var chip_sum = QM31.zero();"):
        raise ValueError("raw claimed-sum canonical decoding changed")
    if "if (Profile == RawMC and (spec != null or converted_out != null))" not in verify:
        raise ValueError("raw recursion exclusion changed")
    if "return error.InvalidInteractionNonce;" not in verify:
        raise ValueError("interaction PoW failure no longer exits")
    if not re.search(r"if \(raw_gate_channel\)\s+try native\.verifyRawGate\(", runtime):
        raise ValueError("raw package dispatch changed")
    if "(if (raw_gate_channel) cpu.Root else cpu.Internal).prove(" not in runtime:
        raise ValueError("raw prover profile dispatch changed")

    core = region(engine["deps/stwo-zig/src/core/verifier.zig"], "fn verifyImpl(", "fn pointFromOodsSeed(")
    ordered_once(core, "composition and OOD epochs",
                 "const composition_randomness = channel.drawSecureFelt();",
                 "try commitment_scheme.commit(",
                 "const oods_seed = channel.drawSecureFelt();",
                 "commitment_scheme.verifyValuesWithBorrowedProofCapture(")
    pcs = region(engine["deps/stwo-zig/src/core/pcs/verifier.zig"], "fn verifyValuesImpl(", "fn queryTreeLogSize(")
    ordered_once(pcs, "PCS PoW and query epoch",
                 "channel.mixFelts(sampled_values_flat);",
                 "const deep_randomness = channel.drawSecureFelt();",
                 "var fri_verifier = try FriVerifier.commit(",
                 "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work))",
                 "channel.mixU64(proof.proof_of_work);",
                 "fri_verifier.sampleQueryPositionsWithRaw(")
    if "return verifier_types.VerificationError.ProofOfWork;" not in pcs:
        raise ValueError("FRI PoW failure no longer exits")
    fri = engine["deps/stwo-zig/src/core/fri.zig"]
    ordered_once(region(fri, "pub fn commit(", "pub fn sampleQueryPositions("), "FRI root and alpha epochs",
                 "MC.mixRoot(channel, proof_in.first_layer.commitment);",
                 ".folding_alpha = channel.drawSecureFelt(),\n                .proof =",
                 "MC.mixRoot(channel, inner_proof.commitment);",
                 "channel.mixFelts(last_layer_poly.coefficients());")
    ordered_once(region(fri, "pub fn sampleQueryPositionsWithRaw(", "pub fn decommit("), "FRI raw query custody",
                 "const raw = try queries_mod.drawQueries(", "self.config.n_queries,",
                 "var new_queries = try queries_mod.Queries.init(",
                 "const retained_raw = try allocator.dupe(usize, raw);")
    queries = region(engine["deps/stwo-zig/src/core/queries.zig"], "pub fn drawQueries(", "pub fn sortedUniquePositions(")
    ordered_once(queries, "raw masked query loop", "while (produced < n_queries)",
                 "const words = channel.drawU32s();",
                 "out[produced] = @as(usize, word & query_mask);",
                 "if (produced == n_queries) break;")
    if re.findall(r"channel\.[A-Za-z0-9_]+\(", queries) != ["channel.drawU32s("]:
        raise ValueError("query loop gained another channel operation")
    channel = engine["deps/stwo-zig/src/core/channel/blake2s.zig"]
    raw_profile = region(engine["deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig"],
                         "pub const Blake2sMerkleChannel = Blake2sMerkleChannelProfile(.{",
                         "pub const Blake2sM31MerkleChannel = Blake2sMerkleChannelProfile(.{")
    ordered_once(raw_profile, "raw channel selection", ".m31_channel = false,",
                 ".revision = .proving_5a7c5ed,")
    if "const RawMC = cpu.prove.profiles.Blake2sMerkleChannel;" not in frontend:
        raise ValueError("raw verifier channel alias changed")
    if "if (H != MC.MerkleHasher or H != RawMC.MerkleHasher)" not in frontend:
        raise ValueError("raw/fixed Merkle hasher equality changed")
    draw = region(channel, "pub fn drawU32s(", "pub fn drawSecureFelt(")
    ordered_once(draw, "raw 37-byte counter preimage",
                 "var hash_input: [37]u8 = undefined;",
                 "@memcpy(hash_input[0..32], self.digest[0..]);",
                 "const counter = u32ToBytesLe(self.n_draws);",
                 "@memcpy(hash_input[32..36], counter[0..]);",
                 "hash_input[36] = 0;",
                 "self.n_draws = nextDrawCounter(self.n_draws)",
                 "const hash = hashBytes(hash_input[0..]);",
                 "out[i] = readU32Le(hash[base .. base + 4]);")
    ordered_once(region(channel, "fn drawBaseFelts(", "fn hashBytes("), "whole-block rejection",
                 "const words = self.drawU32s();", "if (x >= two_p)",
                 "if (!valid) continue;", "felts[i] = M31.fromU64(x);")
    if "return std.math.add(u32, current, 1) catch error.DrawCounterExhausted;" not in channel:
        raise ValueError("counter fail-closed law changed")
    if "self.n_draws = 0;" not in region(channel, "pub inline fn updateDigest(", "pub fn mixFelts("):
        raise ValueError("absorption no longer resets counter")
    if "return trailingZeroBits(out[0..16]) >= n_bits;" not in channel:
        raise ValueError("PoW predicate changed")
    if "pub const POW_PREFIX: u32 = 0x12345678;" not in channel:
        raise ValueError("PoW prefix role constant changed")
    ordered_once(region(channel, "pub fn verifyPowNonce(", "/// Compute the constant prefix hash"),
                 "PoW check uses the reviewed two-hash chain",
                 "const prefix = self.computePowPrefix(n_bits);",
                 "return verifyNonceWithPrefix(prefix, nonce, n_bits);")
    ordered_once(region(channel, "pub fn computePowPrefix(", "/// Check a single nonce"),
                 "52-byte PoW prefix input",
                 "const prefix_bytes = u32ToBytesLe(POW_PREFIX);",
                 "const bits_bytes = u32ToBytesLe(n_bits);",
                 "prefixed_hasher.update(prefix_bytes[0..]);",
                 "prefixed_hasher.update(&[_]u8{0} ** 12);",
                 "prefixed_hasher.update(self.digest[0..]);",
                 "prefixed_hasher.update(bits_bytes[0..]);",
                 "return prefixed_hasher.finalize();")
    ordered_once(region(channel, "fn verifyNonceWithPrefix(", "/// PoW predicate for eight candidates"),
                 "40-byte PoW nonce input",
                 "var input: [40]u8 = undefined;",
                 "@memcpy(input[0..32], prefix[0..]);",
                 "const nonce_bytes = u64ToBytesLe(nonce);",
                 "@memcpy(input[32..40], nonce_bytes[0..]);",
                 "const out = Hasher.hashFixedSingleBlock(40, &input);",
                 "return trailingZeroBits(out[0..16]) >= n_bits;")
    ordered_once(region(channel, "pub fn mixU64(", "pub fn drawU32s("),
                 "40-byte accepted nonce absorption",
                 "self.mixU32s(&[_]u32{", "@truncate(value),",
                 "@truncate(value >> 32),")
    if "if (is_m31_output) out = reduceToM31(out);" not in engine["deps/stwo-zig/src/core/vcs/blake2_hash.zig"]:
        raise ValueError("raw hash selector changed")
    merkle = engine["deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig"]
    if "pub const MerkleHasher = blake2_merkle.Blake2sPlainMerkleHasher;" not in engine[
            "deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig"]:
        raise ValueError("raw plain Merkle profile changed")
    root_mix = region(merkle, "pub fn mixRoot(", "pub const Blake2sMerkleChannel =")
    ordered_once(root_mix, "unframed root absorption",
                 "const digest = channel.digestBytes();",
                 "blake2_hash.Blake2sHasherGeneric(is_m31_output).concatAndHash(digest, root)")
    parent = region(merkle, "pub fn hashChildrenWithMode(", "pub fn domainPrefixBytes(")
    if "return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);" not in parent:
        raise ValueError("plain Merkle parent hash changed")
    leaf = region(merkle, "pub fn updateLeaf(self:", "pub fn finalize(self:")
    ordered_once(leaf, "unframed canonical M31 leaf",
                 "self.inner.update(std.mem.sliceAsBytes(column_values));",
                 "const value_bytes = column_values[at + i].toBytesLe();")
    if "QM31.fromU32Unchecked(self.pow_bits, self.log_blowup_factor, self.n_queries, self.log_last_layer_degree_bound)" not in engine["deps/stwo-zig/src/core/pcs/config_v2.zig"]:
        raise ValueError("FRI config absorption changed")


def audit_sources(root: Path = ROOT) -> dict[str, str]:
    commit = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD:deps/stwo-zig"], text=True).strip()
    actual = subprocess.check_output(["git", "-C", str(root / "deps/stwo-zig"), "rev-parse", "HEAD"], text=True).strip()
    if commit != ENGINE_COMMIT or actual != commit:
        raise ValueError("engine gitlink or checkout differs from reviewed source")
    engine = {name: (root / name).read_text() for name in ENGINE_SHA256}
    hashes = {name: hashlib.sha256(value.encode()).hexdigest() for name, value in engine.items()}
    if hashes != ENGINE_SHA256:
        raise ValueError("reviewed engine PCS/FRI source bytes changed")
    frontend = (root / FRONTEND).read_text()
    runtime = (root / RUNTIME).read_text()
    audit_source_shapes(frontend, runtime, engine)
    return {**hashes, FRONTEND: hashlib.sha256(frontend.encode()).hexdigest(),
            RUNTIME: hashlib.sha256(runtime.encode()).hexdigest()}


def exact(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def report(root: Path = ROOT) -> dict:
    hashes = audit_sources(root)
    # Fixed-prefix ideal-random-output arithmetic. Rejection applies only to
    # drawBaseFelts; drawQueries consumes unreduced words with no rejection.
    block_accept = Fraction(2 * P, 1 << 32) ** 8
    collision_work_factor = Fraction(3 * (T * T + 1), (1 << 256) * T)
    def paper_collision_work_factor(bits: int) -> Fraction:
        return Fraction(3 * (T * T + 1), (1 << bits) * T)

    minimum_collision_bits = next(bits for bits in range(1, 257)
                                  if paper_collision_work_factor(bits) <= TARGET)
    if minimum_collision_bits != 162:
        raise AssertionError("selected paper-only collision threshold changed")
    if not collision_work_factor < Fraction(1, 1 << 126):
        raise AssertionError("hypothetical 256-bit paper collision term changed")
    p20, p26 = Fraction(1, 1 << 20), Fraction(1, 1 << 26)
    two_first_one_second = (1 - (1 - p20) ** 2) * p26
    if not two_first_one_second > p20 * p26:
        raise AssertionError("two-stage grinding arithmetic changed")
    # These intentionally small separate nonce caps fit T even after two
    # prefix calls and leave ample room for other transcript hash work.
    first_nonce_cap, second_nonce_cap = 1 << 21, 1 << 27
    if first_nonce_cap + second_nonce_cap + 2 >= T:
        raise AssertionError("illustrative nonce caps exceed T")
    transcript = fixture()
    if len(transcript["queries"]) != 70 or transcript["epochs"][-1]["counter"] != 9:
        raise AssertionError("raw Gate fixture query schedule changed")
    return {
        "schema": "s31-raw-gate-bcs-audit-v1",
        "status": "source_bound_deterministic_transcript_adaptive_bcs_open",
        "selected_target": {"metric": "paper_work_factor_epsilon_over_T", "bits": 96,
                            "T_hash_queries": T},
        "reviewed_engine_gitlink": ENGINE_COMMIT,
        "source_sha256": hashes,
        "proof_wire": {"magic": "S31NAT8R", "nonce": "u64_le",
                       "claimed_sums": "eleven_QM31_values_as_canonical_u32le_limbs",
                       "postcard_commitment_roots": 4,
                       "header_bytes": 8 + 8 + 11 * 16},
        "commitment_epochs": ["fixed_before_public_values", "main_before_interaction_pow",
                              "interaction_after_lookup_claims", "composition_after_AIR_coefficient"],
        "conditional_fixed_prefix_ideal_raw": {
            "field_block_acceptance_exact": exact(block_accept),
            "field_block_rejection_exact": exact(1 - block_accept),
            "lookup_pair_uniform_QM31_squared": True,
            "pow_20_one_try_exact": exact(Fraction(1, 1 << 20)),
            "pow_26_one_try_exact": exact(Fraction(1, 1 << 26)),
            "query_index_uniform_with_replacement": True,
            "query_raw_hash_blocks": 9,
            "query_draw_counter_values": list(range(9)),
            "query_epoch_counter_overflow": False,
        },
        "conditional_two_stage_fresh_oracle_only": {
            "one_nonce_each_exact": exact(p20 * p26),
            "two_interaction_one_fri_exact": exact(two_first_one_second),
            "illustrative_first_nonce_cap": first_nonce_cap,
            "illustrative_second_nonce_cap": second_nonce_cap,
            "two_prefix_calls_plus_nonce_caps_below_T": True,
            "first_union_envelope_at_cap_exact": exact(min(1, first_nonce_cap * p20)),
            "second_conditional_union_envelope_at_cap_exact":
                exact(min(1, second_nonce_cap * p26)),
            "requires_fresh_distinct_cross_role_oracle_inputs": True,
            "applies_to_native_verifier": False,
        },
        "hypothetical_paper_BCS_lambda_256_only": {
            "collision_work_factor_exact": exact(collision_work_factor),
            "collision_work_factor_below_2_pow_minus_126": True,
            "applies_to_native_verifier": False,
        },
        "hypothetical_paper_collision_threshold": {
            "collision_term_only_minimum_lambda_bits": minimum_collision_bits,
            "work_factor_at_lambda_161_exact": exact(paper_collision_work_factor(161)),
            "work_factor_at_lambda_162_exact": exact(paper_collision_work_factor(162)),
            "other_round_error_budget_at_lambda_162_exact":
                exact(TARGET - paper_collision_work_factor(162)),
            "native_lambda_bits": None,
            "applies_to_native_verifier": False,
        },
        "unframed_hash_input_role_overlap": {
            "root_absorb_equals_plain_merkle_parent_at_same_digest_and_root": True,
            "root_absorb_equals_two_qm31_absorb_for_canonical_root_limbs": True,
            "canonical_32_byte_roots_count": P ** 8,
            "canonical_32_byte_roots_fraction_exact": exact(Fraction(P ** 8, 1 << 256)),
            "sixteen_m31_word_leaf_has_parent_message_length": True,
            "pow_nonce_input_can_equal_nonce_absorption_input": True,
            "domain_separated_BCS_encoding_proved": False,
            "accepted_proof_attack_demonstrated": False,
        },
        "unbounded_rejection_before_query_epoch": True,
        "draw_counter_fails_before_wrap": True,
        "adaptive_BCS_reduction_proved": False,
        "native_proven_security_bits": None,
        "release_gate_admissible": False,
        "remaining_P07_P09": [
            "prove full raw proof-byte and installed-binary execution refines this transcript for all accepting paths",
            "prove random-oracle input framing and role/cross-epoch collision accounting for raw 256-bit BLAKE2s",
            "charge adaptive commitment selection, both nonce searches, rejected challenge blocks, and total hash work T",
            "join the actual raw query law and Merkle/FRI opening relation to a matching IOP/BCS theorem",
            "instantiate all FRI/PCS round errors and admissible parameters; current 70-query profile fails quoted necessary arithmetic",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-adaptive-bcs", action="store_true")
    args = parser.parse_args(argv)
    try:
        value = report()
        if args.require_adaptive_bcs:
            raise ValueError("adaptive BCS/ROM reduction and full P09 bound are unproved")
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(f"raw Gate BCS audit rejected: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(value, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
