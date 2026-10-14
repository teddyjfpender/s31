"""Focused controls for the proposed, nonselected BCS v2 byte encoding."""

from __future__ import annotations

import hashlib
import unittest

from scripts.release.pcs_fri_framed_bcs_v2 import (
    CHALLENGE_BLOCK_CAP, DOMAIN, HEADER_BYTES, M31_MODULUS, Role, StatementBinding,
    absorb_field, absorb_nonce,
    absorb_root, candidate_paired_gate_plan, frame, hash_frame, merkle_leaf, merkle_parent, parse_frame,
    canonical_m31_block, draw_challenge_m31_limbs, initial_digest,
    pow_trial, raw_words, report, tree_context,
)


class FramedBcsV2Tests(unittest.TestCase):
    def test_statement_binding_exact_bytes_and_first_digest(self) -> None:
        zero = bytes(32)
        statement = StatementBinding(zero, zero, zero, (zero, zero, zero, zero), zero)
        payload = statement.encode()
        self.assertEqual(payload, b"S31NAT9F" + bytes(256))
        self.assertEqual(len(payload), 264)
        self.assertEqual(initial_digest(statement).hex(),
                         "667b272f99f769be23d49cd20b59b07c31cbaa64cdb21243be1a3ba533117f7b")
        root = bytes(range(32))
        self.assertEqual(absorb_root(initial_digest(statement), 1, root).hex(),
                         "ded398cba3dcfbc1d7bc7f3665095df4592783b9b959f178e7c83c90e6a0bf22")
        with self.assertRaises(ValueError):
            StatementBinding(zero, zero, zero, (zero, zero, zero), zero).encode()  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            StatementBinding(zero, zero, zero, (zero, zero, zero, b"x"), zero).encode()

    def test_challenge_rejection_consumes_exact_counter_blocks(self) -> None:
        bad = (2 * M31_MODULUS, 0, 0, 0, 0, 0, 0, 0)
        good = (0, M31_MODULUS, 1, M31_MODULUS + 1,
                2, M31_MODULUS + 2, 3, M31_MODULUS + 3)
        self.assertIsNone(canonical_m31_block(bad))
        self.assertEqual(canonical_m31_block(good), (0, 0, 1, 1, 2, 2, 3, 3))
        seen: list[int] = []

        def rejected_once(_digest: bytes, _event: int, counter: int) -> tuple[int, ...]:
            seen.append(counter)
            return bad if counter == 0 else good

        limbs, next_counter = draw_challenge_m31_limbs(bytes(32), 17, oracle=rejected_once)
        self.assertEqual(limbs, (0, 0, 1, 1, 2, 2, 3, 3))
        self.assertEqual((next_counter, seen), (2, [0, 1]))
        self.assertEqual(CHALLENGE_BLOCK_CAP, 8)
        with self.assertRaisesRegex(ValueError, "cap exhausted"):
            draw_challenge_m31_limbs(bytes(32), 17,
                                     oracle=lambda _d, _e, _c: bad)

    def test_full_candidate_event_plan_has_native_golden_digest(self) -> None:
        zero = bytes(32)
        digest = initial_digest(StatementBinding(zero, zero, zero,
                                                 (zero, zero, zero, zero), zero))
        expected_challenges = {
            8: 1822750541, 11: 640893609, 13: 1454020928,
            15: 590385924, 16: 1174171810, 19: 452219042,
        }
        prefix_event: int | None = None
        for step in candidate_paired_gate_plan((17, 16))[1:]:
            event = step.event
            if step.role is Role.ROOT_ABSORB:
                digest = absorb_root(digest, event, bytes([event]) * 32)
            elif step.role is Role.FIELD_ABSORB:
                digest = absorb_field(digest, event, (0, 1, 2, 3))
            elif step.role is Role.POW_PREFIX:
                prefix_event = event
            elif step.role is Role.POW_TRIAL:
                if prefix_event is None:
                    self.fail("PoW trial lacks a prefix event")
                self.assertEqual(event, prefix_event + 1)
                self.assertEqual(len(pow_trial(digest, prefix_event, event, 0, 0)), 32)
            elif step.role is Role.NONCE_ABSORB:
                digest = absorb_nonce(digest, event, 0)
            elif step.role is Role.RAW_WORD_DRAW:
                if step.name == "raw_queries":
                    self.assertEqual(raw_words(digest, event, 0)[0], 1533884970)
                else:
                    limbs, next_counter = draw_challenge_m31_limbs(digest, event)
                    self.assertEqual((limbs[0], next_counter),
                                     (expected_challenges[event], 1))
        self.assertEqual(digest.hex(),
                         "84bbf452bd2097fe94c0310fe2030f5ff985fb52fa1d9dc8cbeedc2af9ed464f")

    def test_exact_frame_bytes_and_canonical_parser(self) -> None:
        expected = (b"S31BCS2\x02" + b"\x02" + bytes(7) +
                    b"\x03" + bytes(7) + b"\xaa\xbb")
        self.assertEqual(frame(Role.ROOT_ABSORB, 3, b"\xaa\xbb"), expected)
        self.assertEqual(len(expected), HEADER_BYTES + 2)
        self.assertEqual(parse_frame(expected), (Role.ROOT_ABSORB, 3, b"\xaa\xbb"))
        self.assertEqual(hash_frame(Role.ROOT_ABSORB, 3, b"\xaa\xbb"),
                         hashlib.blake2s(expected, digest_size=32).digest())
        self.assertEqual(len(DOMAIN), 7)

    def test_role_event_and_payload_are_distinct_inputs(self) -> None:
        payload = bytes(64)
        messages = {frame(role, event, payload)
                    for role in Role for event in (0, 1, (1 << 64) - 1)}
        self.assertEqual(len(messages), len(Role) * 3)
        self.assertNotEqual(frame(Role.ROOT_ABSORB, 0, payload),
                            frame(Role.FIELD_ABSORB, 0, payload))
        self.assertNotEqual(frame(Role.MERKLE_LEAF, 0, payload),
                            frame(Role.MERKLE_PARENT, 0, payload))
        self.assertNotEqual(frame(Role.ROOT_ABSORB, 0, b"\x00"),
                            frame(Role.ROOT_ABSORB, 0, b"\x00\x00"))

    def test_old_untagged_alias_is_separated_by_new_roles(self) -> None:
        digest = bytes(range(32))
        canonical_root = b"".join(x.to_bytes(4, "little")
                                   for x in (0, 1, 2, 3, 4, 5, 6, 7))
        self.assertNotEqual(absorb_root(digest, 5, canonical_root),
                            absorb_field(digest, 5, (0, 1, 2, 3, 4, 5, 6, 7)))
        # Framed root absorption includes role, length and event before the
        # digest and root, unlike the old parent input digest||root.
        root_input = frame(Role.ROOT_ABSORB, 5, digest + canonical_root)
        parent_input = frame(Role.MERKLE_PARENT, 5, digest + canonical_root)
        self.assertNotEqual(root_input, parent_input)

    def test_query_pow_and_merkle_roles(self) -> None:
        digest = bytes(32)
        self.assertEqual(len(raw_words(digest, 12, 0)), 8)
        self.assertNotEqual(raw_words(digest, 12, 0), raw_words(digest, 12, 1))
        self.assertNotEqual(absorb_nonce(digest, 12, 0), pow_trial(digest, 13, 14, 20, 0))
        with self.assertRaises(ValueError):
            pow_trial(digest, 13, 13, 20, 0)
        context = tree_context(b"gate-height=17;row-roster=v1")
        self.assertEqual(len(context), 32)
        leaf = merkle_leaf(context, tuple(range(16)))
        parent = merkle_parent(context, 1, digest, digest)
        self.assertNotEqual(leaf, parent)

    def test_malformed_frames_and_noncanonical_rows_reject(self) -> None:
        good = frame(Role.ROOT_ABSORB, 0, b"x")
        for bad in (good[:-1], good + b"z", b"wrong!!" + good[7:],
                    good[:7] + b"\xff" + good[8:]):
            with self.subTest(bad=bad):
                with self.assertRaises(ValueError):
                    parse_frame(bad)
        with self.assertRaises(ValueError):
            frame(Role.ROOT_ABSORB, 1 << 64, b"")
        with self.assertRaises(ValueError):
            frame(2, 0, b"")  # type: ignore[arg-type]
        with self.assertRaises(ValueError):
            absorb_field(bytes(32), 0, (M31_MODULUS, 0, 0, 0))
        with self.assertRaises(ValueError):
            merkle_leaf(bytes(32), (M31_MODULUS,))
        with self.assertRaises(ValueError):
            merkle_parent(bytes(32), True, bytes(32), bytes(32))

    def test_paired_gate_candidate_has_four_source_roots_and_two_fri_tracks(self) -> None:
        plan = candidate_paired_gate_plan((17, 16, 15))
        names = [step.name for step in plan]
        event_by_name = {step.name: step.event for step in plan}
        self.assertEqual([step.event for step in plan], list(range(len(plan))))
        self.assertEqual(names[names.index("sampled_values") + 1], "batch_lambda")
        self.assertEqual([name for name in names if name in {
            "fixed_root", "main_root", "interaction_root", "composition_root"}],
            ["fixed_root", "main_root", "interaction_root", "composition_root"])
        for height in (17, 16):
            alpha = names.index(f"fold_alpha_h{height}")
            self.assertEqual(names[alpha + 1:alpha + 3],
                             [f"original_root_h{height}", f"own_quotient_root_h{height}"])
        self.assertEqual(names[names.index("fold_alpha_h15") + 1],
                         "original_terminal_coefficients")
        self.assertEqual(names[-6:], ["original_terminal_coefficients",
                                      "own_quotient_terminal_coefficients",
                                      "fri_pow_prefix", "fri_pow_trial", "fri_nonce", "raw_queries"])
        digest = bytes(range(32))
        for barrier in ("interaction", "fri"):
            prefix_event = event_by_name[f"{barrier}_pow_prefix"]
            trial_event = event_by_name[f"{barrier}_pow_trial"]
            self.assertEqual(trial_event, prefix_event + 1)
            prefix = hash_frame(Role.POW_PREFIX, prefix_event,
                                digest + (20).to_bytes(4, "little"))
            expected = hash_frame(Role.POW_TRIAL, trial_event,
                                  prefix + (7).to_bytes(8, "little"))
            self.assertEqual(pow_trial(digest, prefix_event, trial_event, 20, 7),
                             expected)
        with self.assertRaises(ValueError):
            candidate_paired_gate_plan((16, 17))
        with self.assertRaises(ValueError):
            candidate_paired_gate_plan((17, 17))

    def test_report_remains_nonadmitting(self) -> None:
        value = report()
        self.assertIsNone(value["native_proven_security_bits"])
        self.assertFalse(value["proven_release_admissible"])
        self.assertEqual(value["new_proof_magic_reserved"], "S31NAT9F")


if __name__ == "__main__":
    unittest.main()
