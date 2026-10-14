"""Raw Gate transcript source boundary and fixed-prefix arithmetic tests."""

from __future__ import annotations

import copy
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
        self.assertFalse(value["release_gate_admissible"])
        self.assertIsNone(value["native_proven_security_bits"])

    def test_exact_ideal_arithmetic(self) -> None:
        value = report(ROOT)
        facts = value["conditional_fixed_prefix_ideal_raw"]
        p = (1 << 31) - 1
        acceptance = Fraction(2 * p, 1 << 32) ** 8
        self.assertEqual(facts["field_block_acceptance_exact"],
                         f"{acceptance.numerator}/{acceptance.denominator}")
        self.assertEqual(facts["pow_20_one_try_exact"], "1/1048576")
        self.assertEqual(facts["pow_26_one_try_exact"], "1/67108864")
        paper = Fraction(3 * (T * T + 1), (1 << 256) * T)
        self.assertLess(paper, Fraction(1, 1 << 126))
        self.assertLess(paper, TARGET)

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


if __name__ == "__main__":
    unittest.main()
