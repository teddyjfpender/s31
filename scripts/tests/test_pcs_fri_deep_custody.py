"""Mutations of the S31 raw DEEP admission source contract."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_deep_custody import check_sources


ROOT = Path(__file__).resolve().parents[2]
NATIVE = (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text()
ADMISSION = (ROOT / "src/frontends/s31/runtime/deep_capture_admission.zig").read_text()
PCS = (ROOT / "deps/stwo-zig/src/core/pcs/verifier.zig").read_text()


class DeepCustodySourceControls(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check_sources(NATIVE, ADMISSION, PCS)

    def test_each_verifier_path_requires_raw_custody(self) -> None:
        before = "try deep_capture_admission.validate("
        self.assertEqual(NATIVE.count(before), 4)
        start = 0
        for path in range(4):
            position = NATIVE.find(before, start)
            changed = NATIVE[:position] + "// omitted(" + NATIVE[position + len(before):]
            with self.subTest(path=path), self.assertRaises(ValueError):
                check_sources(changed, ADMISSION, PCS)
            start = position + len(before)

    def test_checker_and_core_mutations_rejected(self) -> None:
        cases = (
            ("admission", "raw.len != deep_answers.len or", "false or"),
            ("admission", "query_views[tree][column] = queried_values[query_at..query_end];",
             "query_views[tree][column] = queried_values[0..raw.len];"),
            ("admission", "if (!expected.eql(recorded)) return error.InvalidDeepCapture;",
             "if (false) return error.InvalidDeepCapture;"),
            ("pcs", "const deep_answers = try expandQueryValues(",
             "const deep_answers = try allocator.alloc(QM31, 0);"),
        )
        for which, before, after in cases:
            source = ADMISSION if which == "admission" else PCS
            self.assertEqual(source.count(before), 1)
            changed = source.replace(before, after, 1)
            with self.subTest(which=which, before=before), self.assertRaises(ValueError):
                check_sources(NATIVE, changed, PCS) if which == "admission" else check_sources(NATIVE, ADMISSION, changed)


if __name__ == "__main__":
    unittest.main()
