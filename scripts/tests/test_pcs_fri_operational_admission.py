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
            ("admission", "coefficients.len > (@as(usize, 1) << @intCast(config.log_last_layer_degree_bound))",
             "false"),
            ("admission", "if (!left.eql(right)) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "if (!current.eql(subset[position % width])) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "const challenge = alpha.pow(@as(u64, 1) << @intCast(step));",
             "const challenge = alpha;"),
            ("admission", "const y = fold_domain.half_coset.at(point_index).y;",
             "const y = M31.one();"),
            ("admission", "domain.at(point_index),",
             "M31.one(),"),
            ("admission", "const fold_initial = source_domain.coset().indexAt(initial_index);",
             "const fold_initial = source_domain.coset().indexAt(0);"),
            ("admission", "if (!current.eql(expected)) return error.InvalidFriCapture;",
             "if (false) return error.InvalidFriCapture;"),
            ("admission", "const expected = try terminal_evaluator.eval(coefficients, x);",
             "const expected = QM31.zero();"),
            ("admission", "if (coefficient_count == 0 or !std.math.isPowerOfTwo(coefficient_count))",
             "if (false)"),
            ("admission", "const factor = self.factors[depth - 1];",
             "const factor = self.factors[0];"),
            ("admission", "doubled_x = square.add(square).sub(QM31.one());",
             "doubled_x = square;"),
            ("admission", "var doubled_x = QM31.fromBase(x);",
             "var doubled_x = QM31.zero();"),
            ("admission", "self.scratch[2 * i + 1].mul(factor),",
             "self.scratch[2 * i + 1],"),
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
            ("capture.deep_answers,\n        capture.fri,",
             "capture.sampled_values,\n        capture.fri,"),
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
