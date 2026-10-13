"""Independent transcript fixture and hostile source controls for P07."""
from __future__ import annotations

import json
import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_bcs_transcript import (
    Channel, P, ROOT, audit, audit_sources, fixture,
)

NAMES = (
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


class BcsTranscriptTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = tuple((ROOT / name).read_text() for name in NAMES)

    def reject(self, index: int, old: str, new: str) -> None:
        changed = list(self.sources)
        self.assertIn(old, changed[index])
        changed[index] = changed[index].replace(old, new, 1)
        with self.assertRaises(ValueError):
            audit_sources(*changed)

    def reject_direct(self, old: str, new: str) -> None:
        changed = list(self.sources)
        head, direct = changed[0].split("fn verifyDirectProfile(", 1)
        self.assertIn(old, direct)
        changed[0] = head + "fn verifyDirectProfile(" + direct.replace(old, new, 1)
        with self.assertRaises(ValueError):
            audit_sources(*changed)

    def test_fixture_and_pinned_source_audit(self) -> None:
        audit_sources(*self.sources)
        saved = json.loads((ROOT / "formal/s31/tests/pcs_fri_bcs_transcript.json").read_text())
        self.assertEqual(saved, json.loads(json.dumps(fixture())))
        report = audit(ROOT)
        self.assertEqual(len(report["native_sources_sha256"]), len(NAMES))
        self.assertFalse(report["proven_native_bcs_soundness"])
        self.assertEqual(report["engine_gitlink_commit"], "59e1f115250b8af01712b9bf3d71616e53094964")
        epochs = saved["epochs"]
        self.assertEqual([e["counter"] for e in epochs], [0, 0, 1, 0, 0, 9])
        self.assertEqual(len(saved["queries"]), 70)

    def test_channel_byte_semantics_and_epoch_reset(self) -> None:
        c = Channel()
        self.assertEqual(c.draw_words(),
                         (1508103417, 49928118, 1851109195, 649450964,
                          1514800545, 2089281384, 523819246, 1919080973))
        self.assertEqual(c.counter, 1)
        c.mix_u64(0x0102030405060708)
        self.assertEqual(c.counter, 0)
        self.assertNotEqual(c.digest, bytes(32))
        self.assertTrue(all(int.from_bytes(c.digest[i:i + 4], "little") < P for i in range(0, 32, 4)))
        c.counter = (1 << 32) - 1
        with self.assertRaises(OverflowError):
            c.draw_words()

    def test_pow_nonce_binds_digest_and_bits(self) -> None:
        before = Channel()
        before.mix_u64(1234567)
        nonce = before.first_valid_nonce(8)
        self.assertTrue(before.pow_valid(8, nonce))
        altered = Channel(before.digest)
        altered.mix_root(bytes([8]) * 32)
        self.assertNotEqual(before.digest, altered.digest)
        # The predicate is recomputed from the current digest. This is a
        # deterministic fixture assertion, not a collision-resistance proof.
        self.assertFalse(altered.pow_valid(8, nonce))
        self.assertFalse(before.pow_valid(9, nonce))

    def test_interaction_pow_barrier_removed(self) -> None:
        self.reject_direct("if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, nonce))",
                    "if (false)")

    def test_interaction_nonce_reordered(self) -> None:
        self.reject_direct("channel.mixU64(nonce);\n    const lookup =",
                    "const lookup =")

    def test_fri_pow_barrier_removed(self) -> None:
        self.reject(2, "if (!channel.verifyPowNonce(self.config.pow_bits, proof.proof_of_work))",
                    "if (false)")

    def test_fri_nonce_reordered(self) -> None:
        self.reject(2, "channel.mixU64(proof.proof_of_work);",
                    "channel.mixU64(0);")

    def test_deep_draw_moved_or_missing(self) -> None:
        self.reject(2, "const deep_randomness = channel.drawSecureFelt();",
                    "const deep_randomness = QM31.zero();")

    def test_first_fri_root_or_alpha_missing(self) -> None:
        self.reject(3, "MC.mixRoot(channel, proof_in.first_layer.commitment);",
                    "// omitted first FRI root")
        self.reject(3, ".folding_alpha = channel.drawSecureFelt(),\n                .proof =",
                    ".folding_alpha = QM31.zero(),\n                .proof =")

    def test_last_layer_coefficients_missing(self) -> None:
        self.reject(3, "channel.mixFelts(last_layer_poly.coefficients());",
                    "// omitted last layer coefficients")

    def test_profile_tag_and_alias_changed(self) -> None:
        self.reject(9, "pub const profile_tag: u64 = 0x5333314449523401;",
                    "pub const profile_tag: u64 = 0;")
        self.reject(10, "pub const profiles = core.vcs_lifted.channel_profile.proving_5a7c5ed;",
                    "pub const profiles = other;")

    def test_merkle_root_and_config_changed(self) -> None:
        self.reject(5, "concatAndHash(digest, root)", "concatAndHash(root, digest)")
        self.reject(7, "QM31.fromU32Unchecked(self.fold_step, 0, 0, 0)",
                    "QM31.fromU32Unchecked(1, 0, 0, 0)")

    def test_pow_prefix_and_predicate_changed(self) -> None:
        self.reject(4, "pub const POW_PREFIX: u32 = 0x12345678;",
                    "pub const POW_PREFIX: u32 = 0;")
        self.reject(4, "return trailingZeroBits(out[0..16]) >= n_bits;",
                    "return true;")

    def test_channel_draw_and_rejection_changed(self) -> None:
        self.reject(4, "hash_input[36] = 0;", "hash_input[36] = 1;")
        self.reject(4, "if (x >= two_p)", "if (x >= m31.Modulus)")

    def test_hash_reduction_and_query_count_changed(self) -> None:
        self.reject(11, "const reduced = @select(u32, folded >= p, folded -% p, folded);",
                    "const reduced = input;")
        self.reject(8, "const words = channel.drawU32s();",
                    "const words = [_]u32{0} ** 8;")


if __name__ == "__main__":
    unittest.main()
