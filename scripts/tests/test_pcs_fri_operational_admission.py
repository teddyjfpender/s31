"""Mutation controls for S31's FRI capture admission gate."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_operational_admission import check_sources


ROOT = Path(__file__).resolve().parents[2]
NATIVE = (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text()
ADMISSION = (ROOT / "src/frontends/s31/runtime/fri_capture_admission.zig").read_text()


class OperationalAdmissionSourceControls(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check_sources(NATIVE, ADMISSION)

    def test_bypasses_are_rejected(self) -> None:
        cases = (
            ("admission", "raw.len != config.n_queries or", "false or"),
            ("admission", "if (!left.eql(right)) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "if (!current.eql(subset[position % width])) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "if (!current.eql(expected)) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "return left.add(right).add(alpha.mul(left.sub(right).mulM31(inverse)));",
             "return left.add(right);"),
        )
        for name, before, after in cases:
            with self.subTest(name=name, before=before):
                source = NATIVE if name == "native" else ADMISSION
                self.assertEqual(source.count(before), 1)
                changed = source.replace(before, after, 1)
                with self.assertRaises(ValueError):
                    check_sources(changed, ADMISSION) if name == "native" else check_sources(NATIVE, changed)

    def test_every_verifier_path_requires_admission(self) -> None:
        for before, after in (
            ("try fri_capture_admission.validate(", "// admission omitted("),
            ("pcs.fri_config.folding(),", "pcs.fri_config,"),
            ("capture.deep_answers,", "capture.sampled_values,"),
        ):
            self.assertEqual(NATIVE.count(before), 4)
            start = 0
            for path in range(4):
                position = NATIVE.find(before, start)
                changed = NATIVE[:position] + after + NATIVE[position + len(before):]
                with self.subTest(path=path, before=before):
                    with self.assertRaises(ValueError):
                        check_sources(changed, ADMISSION)
                start = position + len(before)


if __name__ == "__main__":
    unittest.main()
