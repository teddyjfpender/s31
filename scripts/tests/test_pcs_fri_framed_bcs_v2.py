"""Focused controls for the proposed, nonselected BCS v2 byte encoding."""

from __future__ import annotations

import hashlib
import unittest

from scripts.release.pcs_fri_framed_bcs_v2 import (
    DOMAIN, HEADER_BYTES, M31_MODULUS, Role, absorb_field, absorb_nonce,
    absorb_root, candidate_paired_gate_plan, frame, hash_frame, merkle_leaf, merkle_parent, parse_frame,
    pow_trial, raw_words, report, tree_context,
)


class FramedBcsV2Tests(unittest.TestCase):
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
        self.assertNotEqual(absorb_nonce(digest, 12, 0), pow_trial(digest, 12, 20, 0))
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

    def test_paired_gate_candidate_has_four_source_roots_and_two_fri_tracks(self) -> None:
        plan = candidate_paired_gate_plan((17, 16, 15))
        names = [step.name for step in plan]
        self.assertEqual([step.event for step in plan], list(range(len(plan))))
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
