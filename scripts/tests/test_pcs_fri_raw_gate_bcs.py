"""Raw Gate transcript source boundary and fixed-prefix arithmetic tests."""

from __future__ import annotations

import copy
import hashlib
import json
import unittest
from fractions import Fraction
from pathlib import Path

from scripts.release.pcs_fri_raw_gate_bcs import (
    ENGINE_SHA256, FRONTEND, RUNTIME, RawChannel, T, TARGET,
    audit_source_shapes, audit_sources, fixture, report,
)

ROOT = Path(__file__).resolve().parents[2]
SAVED = ROOT / "formal/s31/tests/pcs_fri_raw_gate_bcs_transcript.json"


class RawGateBcsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.frontend = (ROOT / FRONTEND).read_text()
        cls.runtime = (ROOT / RUNTIME).read_text()
        cls.engine = {name: (ROOT / name).read_text() for name in ENGINE_SHA256}

    def reject_frontend(self, old: str, new: str) -> None:
        self.assertIn(old, self.frontend)
        with self.assertRaises(ValueError):
            audit_source_shapes(self.frontend.replace(old, new, 1), self.runtime, self.engine)

    def reject_engine(self, name: str, old: str, new: str) -> None:
        changed = copy.deepcopy(self.engine)
        self.assertIn(old, changed[name])
        changed[name] = changed[name].replace(old, new, 1)
        with self.assertRaises(ValueError):
            audit_source_shapes(self.frontend, self.runtime, changed)

    def test_source_and_report_stay_nonadmitting(self) -> None:
        hashes = audit_sources(ROOT)
        self.assertEqual(set(ENGINE_SHA256).issubset(hashes), True)
        value = report(ROOT)
        self.assertEqual(value["status"], "source_bound_deterministic_transcript_adaptive_bcs_open")
        self.assertEqual(value["proof_wire"]["header_bytes"], 192)
        self.assertEqual(value["proof_wire"]["postcard_commitment_roots"], 4)
        self.assertEqual(value["selected_target"]["T_hash_queries"], T)
        self.assertEqual(value["conditional_fixed_prefix_ideal_raw"]["query_draw_counter_values"], list(range(9)))
        self.assertTrue(value["hypothetical_paper_BCS_lambda_256_only"]
                        ["collision_work_factor_below_2_pow_minus_126"])
        self.assertFalse(value["hypothetical_paper_BCS_lambda_256_only"]["applies_to_native_verifier"])
        self.assertFalse(value["adaptive_BCS_reduction_proved"])
        self.assertTrue(value["draw_counter_fails_before_wrap"])
        self.assertTrue(value["unframed_hash_input_role_overlap"]
                        ["root_absorb_equals_plain_merkle_parent_at_same_digest_and_root"])
        self.assertFalse(value["unframed_hash_input_role_overlap"]
                         ["domain_separated_BCS_encoding_proved"])
        self.assertIsNone(value["hypothetical_paper_collision_threshold"]["native_lambda_bits"])
        self.assertFalse(value["release_gate_admissible"])
        self.assertIsNone(value["native_proven_security_bits"])
        two_stage = value["conditional_two_stage_fresh_oracle_only"]
        self.assertFalse(two_stage["applies_to_native_verifier"])
        self.assertEqual(two_stage["first_union_envelope_at_cap_exact"], "1/1")
        self.assertEqual(two_stage["second_conditional_union_envelope_at_cap_exact"], "1/1")
        self.assertLess(two_stage["illustrative_first_nonce_cap"] +
                        two_stage["illustrative_second_nonce_cap"] + 2, T)

    def test_exact_ideal_arithmetic(self) -> None:
        value = report(ROOT)
        facts = value["conditional_fixed_prefix_ideal_raw"]
        p = (1 << 31) - 1
        acceptance = Fraction(2 * p, 1 << 32) ** 8
        self.assertEqual(facts["field_block_acceptance_exact"],
                         f"{acceptance.numerator}/{acceptance.denominator}")
        self.assertEqual(facts["pow_20_one_try_exact"], "1/1048576")
        self.assertEqual(facts["pow_26_one_try_exact"], "1/67108864")
        two_stage = value["conditional_two_stage_fresh_oracle_only"]
        self.assertEqual(Fraction(two_stage["one_nonce_each_exact"]), Fraction(1, 1 << 46))
        self.assertGreater(Fraction(two_stage["two_interaction_one_fri_exact"]),
                           Fraction(two_stage["one_nonce_each_exact"]))
        self.assertFalse(two_stage["applies_to_native_verifier"])
        paper = Fraction(3 * (T * T + 1), (1 << 256) * T)
        self.assertLess(paper, Fraction(1, 1 << 126))
        self.assertLess(paper, TARGET)
        threshold = value["hypothetical_paper_collision_threshold"]
        self.assertEqual(threshold["collision_term_only_minimum_lambda_bits"], 162)
        self.assertGreater(Fraction(threshold["work_factor_at_lambda_161_exact"]), TARGET)
        self.assertLess(Fraction(threshold["work_factor_at_lambda_162_exact"]), TARGET)
        self.assertEqual(Fraction(threshold["other_round_error_budget_at_lambda_162_exact"]),
                         TARGET - Fraction(threshold["work_factor_at_lambda_162_exact"]))

    def test_unframed_hash_inputs_overlap_without_hash_collision(self) -> None:
        # This checks byte encodings only. The bytes are not an accepted proof
        # or a claim that any such Merkle root is reachable by a prover.
        digest = bytes(range(32))
        root = bytes(range(32, 64))
        c = RawChannel(digest)
        c.mix_root(root)
        self.assertEqual(c.digest, hashlib.blake2s(digest + root, digest_size=32).digest())

        limbs = (0, 1, (1 << 31) - 2, 17, 32, 257, 65536, (1 << 31) - 2)
        canonical_root = b"".join(x.to_bytes(4, "little") for x in limbs)
        by_root = RawChannel(digest)
        by_felts = RawChannel(digest)
        by_root.mix_root(canonical_root)
        by_felts.mix_felts((limbs[:4], limbs[4:]))
        self.assertEqual(by_root.digest, by_felts.digest)
        self.assertEqual(by_root.counter, by_felts.counter)

    def test_fixture_matches_pinned_native_channel_replay(self) -> None:
        expected = json.loads(SAVED.read_text())
        self.assertEqual(expected, json.loads(json.dumps(fixture())))
        self.assertEqual([e["counter"] for e in expected["epochs"]], [0, 0, 1, 0, 0, 9])
        self.assertEqual(len(expected["queries"]), 70)
        self.assertTrue(all(0 <= x < 1 << 21 for x in expected["queries"]))
        before = RawChannel(bytes.fromhex(expected["epochs"][0]["digest"]))
        self.assertTrue(before.pow_valid(8, expected["interaction_nonce"]))
        after = RawChannel(bytes.fromhex(expected["epochs"][3]["digest"]))
        self.assertTrue(after.pow_valid(8, expected["fri_nonce"]))

    def test_raw_counter_fails_before_wrap(self) -> None:
        c = RawChannel()
        c.counter = (1 << 32) - 2
        c.draw_words()
        self.assertEqual(c.counter, (1 << 32) - 1)
        with self.assertRaises(OverflowError):
            c.draw_words()

    def test_raw_dispatch_proof_format_and_pow_barriers_fail_closed(self) -> None:
        self.reject_frontend('const RAW_GATE_MAGIC = "S31NAT8R";',
                             'const RAW_GATE_MAGIC = "S31NAT1\\x00";')
        self.reject_frontend("return verifyProfile(RawMC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);",
                             "return verifyProfile(MC, allocator, layout, template, pcs, preprocessed_root, circuit_hash, public_words, raw, null, null);")
        self.reject_frontend("if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))",
                             "if (false)")
        changed_runtime = self.runtime.replace("try native.verifyRawGate(", "try native.verify(", 1)
        with self.assertRaises(ValueError):
            audit_source_shapes(self.frontend, changed_runtime, self.engine)

    def test_raw_hash_rejection_nonce_and_query_draw_guards(self) -> None:
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "return verifyNonceWithPrefix(prefix, nonce, n_bits);",
                           "return true;")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "prefixed_hasher.update(&[_]u8{0} ** 12);",
                           "prefixed_hasher.update(&[_]u8{1} ** 12);")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "@memcpy(input[32..40], nonce_bytes[0..]);",
                           "@memcpy(input[32..40], prefix[0..8]);")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "@truncate(value >> 32),", "@truncate(value >> 31),")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "if (x >= two_p)", "if (x >= m31.Modulus)")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "hash_input[36] = 0;", "hash_input[36] = 1;")
        self.reject_engine("deps/stwo-zig/src/core/pcs/verifier.zig",
                           "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work))",
                           "if (false)")
        self.reject_engine("deps/stwo-zig/src/core/queries.zig",
                           "const words = channel.drawU32s();",
                           "_ = channel.drawU32s();\n        const words = channel.drawU32s();")
        self.reject_engine("deps/stwo-zig/src/core/channel/blake2s.zig",
                           "return std.math.add(u32, current, 1) catch error.DrawCounterExhausted;",
                           "return current +% 1;")
        self.reject_engine("deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig",
                           "blake2_hash.Blake2sHasherGeneric(is_m31_output).concatAndHash(digest, root)",
                           "blake2_hash.Blake2sHasherGeneric(is_m31_output).concatAndHash(root, digest)")
        self.reject_engine("deps/stwo-zig/src/core/vcs_lifted/blake2_merkle.zig",
                           "return InnerHasher.concatAndHashWithMode(mode, children.left, children.right);",
                           "return InnerHasher.concatAndHashWithMode(mode, children.right, children.left);")
        self.reject_engine("deps/stwo-zig/src/core/vcs_lifted/channel_profile.zig",
                           "pub const MerkleHasher = blake2_merkle.Blake2sPlainMerkleHasher;",
                           "pub const MerkleHasher = blake2_merkle.Blake2sMerkleHasher;")


if __name__ == "__main__":
    unittest.main()
