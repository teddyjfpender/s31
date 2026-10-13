"""Removal and misrouting controls for release SHA PCS/FRI replay."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.sha_release_capture import (
    RELEASE_PATHS, check_sources,
)


ROOT = Path(__file__).resolve().parents[2]
VERIFIER_DIR = ROOT / "src/frontends/s31/sha/verification"
PACKAGE_DIR = ROOT / "src/frontends/s31/sha/package"
HELPER = (VERIFIER_DIR / "pcs_capture_admission.zig").read_text()
VERIFIERS = {name: (VERIFIER_DIR / name).read_text()
             for name, _, _, _ in RELEASE_PATHS}
PACKAGES = {name: (PACKAGE_DIR / name).read_text()
            for _, _, name, _ in RELEASE_PATHS}


class ShaReleaseCaptureControls(unittest.TestCase):
    def test_actual_roster(self) -> None:
        check_sources(HELPER, VERIFIERS, PACKAGES)

    def test_missing_release_gate_and_wrong_config_rejected(self) -> None:
        for name, pcs_name, _, _ in RELEASE_PATHS:
            original = VERIFIERS[name]
            call = f"try pcs_capture_admission.validate(H, allocator, {pcs_name}, capture);"
            for changed in (
                original.replace(call, "// omitted", 1),
                original.replace(call, call.replace(pcs_name, "unbound_pcs"), 1),
            ):
                with self.subTest(name=name, changed=changed != original), self.assertRaises(ValueError):
                    check_sources(HELPER, {**VERIFIERS, name: changed}, PACKAGES)

    def test_deep_or_fold_replay_removal_rejected(self) -> None:
        for before in ("try deep.validate(", "try fri.validate(",
                       "capture.deep_randomness);", "capture.last_layer_coefficients);"):
            self.assertIn(before, HELPER)
            with self.subTest(before=before), self.assertRaises(ValueError):
                check_sources(HELPER.replace(before, "// omitted", 1), VERIFIERS, PACKAGES)


if __name__ == "__main__":
    unittest.main()
