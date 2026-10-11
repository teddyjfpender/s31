"""Native-free checks for stage partition, frozen model, and new source family."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
sys.path[:0] = [str(HERE), str(S31 / "python")]

from independent_score import measures  # noqa: E402
from model import COUNTS, STAGES, TARGETS, evaluate, fit, predict, sha  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from study import P, ROWS, SAMPLES, assignment_for, inventory, source_for  # noqa: E402
from text_frontend import compile_text  # noqa: E402


class StageResolvedStaticTests(unittest.TestCase):
    def test_historical_stage_calibration_reproduces(self) -> None:
        ledger = json.loads((HERE / "historical-stage-ledger.json").read_bytes())
        saved = json.loads((HERE / "calibration.json").read_bytes())
        self.assertEqual(saved, fit(ledger, sha(HERE / "historical-stage-ledger.json"),
                                    sha(HERE / "model.py")))
        self.assertEqual(len(ledger["programs"]), 9)
        self.assertEqual(sum(len(p["trials"]) for p in ledger["programs"]), 108)
        for count in COUNTS:
            first = predict(saved, count, 0)
            later = predict(saved, count, 1)
            self.assertGreater(first["first_verified_wall_seconds"]["center"],
                               later["first_verified_wall_seconds"]["center"] + .3)
            self.assertLess(later["after_reported_pow_seconds"]["upper"] /
                            later["after_reported_pow_seconds"]["center"], 1.5)
        with self.assertRaises(ValueError):
            predict(saved, 32, 0)

    def test_new_lagged_sources_and_assignments(self) -> None:
        planned = inventory()
        self.assertEqual(set(planned), {str(count) for count in COUNTS})
        self.assertEqual(len({v["source_sha256"] for v in planned.values()}), 3)
        digests = [h for v in planned.values() for h in v["assignment_sha256"]]
        self.assertEqual(len(digests), 3 * SAMPLES)
        self.assertEqual(len(set(digests)), len(digests))
        for count in COUNTS:
            relation, _ = compile_text(source_for(count))
            self.assertEqual(len(relation["nodes"]), count)
            self.assertEqual(ROWS[count], planned[str(count)]["expected_padded_qm31_rows"])
            for sample in (0, 1, 11):
                assignment = assignment_for(count, sample)
                self.assertEqual(evaluate_relation(relation, assignment),
                                 assignment["public_outputs"])
            self.assertEqual(assignment_for(count, 0)["public_inputs"]["x"],
                             [P - 2, P - 1, 0, 1])

    def test_stage_accounting_and_score_can_fail(self) -> None:
        ledger = json.loads((HERE / "historical-stage-ledger.json").read_bytes())
        saved = json.loads((HERE / "calibration.json").read_bytes())
        self.assertEqual(set(saved["stage_names"]), set(STAGES))
        self.assertEqual(set(saved["target_names"]), set(TARGETS))
        prior_raw = (S31.parents[2] / "zig-out/s31-operation-mix-transfer-v1" /
                     "heldout/mul-96/trials/000/trial-report.json")
        if prior_raw.exists():
            native = json.loads(prior_raw.read_bytes())
            self.assertGreater(measures(native)["prover_process_residual"], .3)
        future = []
        for count in COUNTS:
            source = f"fresh-{count}"
            template = next(p for p in ledger["programs"]
                            if p["family"] == "mul" and p["gates"] == count)
            future.append({"gates": count, "source_sha256": source,
                           "padded_qm31_rows": ROWS[count],
                           "trials": template["trials"]})
        result = evaluate(saved, future)
        self.assertEqual(set(result["cases"]), {str(n) for n in COUNTS})
        with self.assertRaisesRegex(ValueError, "12 trials"):
            evaluate(saved, [{**future[0], "trials": future[0]["trials"][:1]},
                             *future[1:]])


if __name__ == "__main__":
    unittest.main()
