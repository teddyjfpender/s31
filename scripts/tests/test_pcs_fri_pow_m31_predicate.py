"""Hostile source mutations for the selected two-stage M31 PoW path."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_pow_m31_predicate import check_sources

ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


class PowM31PredicateSourceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = {
            "component": (ROOT / "src/frontends/circuit/common/component_list.zig").read_text(),
            "runtime": (ROOT / "src/frontends/s31/runtime/mvp_runtime.zig").read_text(),
            "frontend": (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text(),
            "pcs": (CORE / "pcs/verifier.zig").read_text(),
            "channel": (CORE / "channel/blake2s.zig").read_text(),
            "hasher": (CORE / "vcs/blake2_hash.zig").read_text(),
            "profile": (CORE / "vcs_lifted/channel_profile.zig").read_text(),
            "prove": (ROOT / "deps/stwo-zig/src/integrations/circuit_cpu/prove.zig").read_text(),
        }

    def test_pinned_source(self) -> None:
        check_sources(**self.sources)

    def test_mutations_fail_closed(self) -> None:
        cases = (
            ("component", "INTERACTION_POW_BITS: u32 = 20", "INTERACTION_POW_BITS: u32 = 19"),
            ("runtime", "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)",
             "FriConfigV2.init(25, 0, 1, 70, fri_fold_step)"),
            ("frontend", "return error.InvalidInteractionNonce;", "// accept any nonce"),
            ("pcs", "return verifier_types.VerificationError.ProofOfWork;",
             "// accept any nonce"),
            ("profile", ".m31_channel = true,", ".m31_channel = false,"),
            ("channel", "return trailingZeroBits(out[0..16]) >= n_bits;", "return true;"),
            ("channel", "prefixed_hasher.update(bits_bytes[0..]);",
             "// omitted PoW bits"),
            ("hasher", "if (is_m31_output) out = reduceToM31(out);",
             "if (false) out = reduceToM31(out);"),
        )
        for name, old, new in cases:
            with self.subTest(name=name, old=old):
                sources = dict(self.sources)
                source = sources[name]
                if name in ("frontend", "hasher"):
                    anchor = ("fn verifyDirectProfile(" if name == "frontend"
                              else "pub fn hashFixedSingleBlock(")
                    before, selected = source.split(anchor, 1)
                    self.assertIn(old, selected)
                    sources[name] = before + anchor + selected.replace(old, new, 1)
                else:
                    self.assertIn(old, source)
                    sources[name] = source.replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(**sources)


if __name__ == "__main__":
    unittest.main()
