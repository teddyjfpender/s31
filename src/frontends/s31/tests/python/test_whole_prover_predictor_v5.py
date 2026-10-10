"""Static V5 admission, fresh split, absolute-byte RSS, and draft freeze tests."""

import hashlib
import json
import subprocess
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(S31_ROOT / "benchmarks"), str(S31_ROOT / "python"),
                str(Path(__file__).resolve().parent)]

from benchmark_whole_prover_cost_v4 import workload_cases as v4_workloads
from benchmark_whole_prover_cost_v5 import (
    PROTOCOL, TOOL_SOURCES, require_frozen_pins, workload_cases,
)
from benchmark_whole_prover_cost_v3 import ROOT, measurement_tool_digest, s31
from whole_prover_predictor_v5 import (
    evaluate, fit_model, predict_rss_absolute, rss_program_gate,
)
from test_whole_prover_predictor_v3 import synthetic_corpus


def synthetic_v5(split: str, protocol: dict) -> dict:
    result = synthetic_corpus(split, protocol)
    old = "signed_div_rem_128" if split == "train" else "signed_quotient_128"
    new = "signed_quotient_128" if split == "train" else "signed_remainder_128"
    case = result["cases"].pop(old)
    case["source_sha256"] = hashlib.sha256(f"source:{split}:{new}".encode()).hexdigest()
    result["cases"][new] = case
    result["schema"] = "s31-whole-prover-cost-corpus-v5"
    result["protocol_sha256"] = hashlib.sha256(PROTOCOL.read_bytes()).hexdigest()
    result["measurement_tool_sha256"] = measurement_tool_digest(TOOL_SOURCES)
    return result


class WholeProverV5Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(PROTOCOL.read_text())

    def test_new_sources_assignments_and_oracles(self) -> None:
        from oracle import evaluate_relation
        from package.context import lower_text

        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = workload_cases("train", root / "v5-train", 2, self.protocol)
            held = workload_cases("validation", root / "v5-held", 2, self.protocol)
            self.assertEqual((len(train), len(held)), (23, 20))
            self.assertEqual(sum(item["family"] == "fixed_width" for item in train), 5)
            self.assertFalse({item["source"].read_bytes() for item in train} &
                             {item["source"].read_bytes() for item in held})
            v4_protocol = json.loads((PROTOCOL.parent / "whole-prover-cost-v4.json").read_text())
            older = (v4_workloads("train", root / "v4-train", 2, v4_protocol) +
                     v4_workloads("validation", root / "v4-held", 2, v4_protocol))
            self.assertFalse({item["source"].read_bytes() for item in train + held} &
                             {item["source"].read_bytes() for item in older})
            def assignment_bytes(items: list[dict]) -> set[bytes]:
                return {json.dumps(value, sort_keys=True).encode()
                        for item in items for value in item["assignments"]}
            self.assertFalse(assignment_bytes(train) & assignment_bytes(held))
            self.assertFalse(assignment_bytes(train + held) & assignment_bytes(older))
            for item in train + held:
                relation = (lower_text(item["source"])[0] if item["source"].suffix == ".s31"
                            else json.loads(item["source"].read_text()))
                for assignment in item["assignments"]:
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])

    def test_rss_radius_is_training_only_absolute_byte_loo_envelope(self) -> None:
        model = fit_model(synthetic_v5("train", self.protocol), self.protocol)
        self.assertEqual(set(model["families"]), set(self.protocol["profiles"]))
        for family, count in (("arithmetic", 6), ("chip", 6),
                              ("hash", 6), ("fixed_width", 5)):
            rss = model["families"][family]["prover_peak_rss_bytes"]
            self.assertEqual(rss["interval_kind"],
                             "symmetric_absolute_byte_loo_program_envelope")
            self.assertEqual(len(rss["calibration"]), count)
            self.assertEqual(rss["radius_bytes"], max(
                item["absolute_byte_radius"] for item in rss["calibration"]))
            self.assertEqual(rss["training_trials"], 100 * count)
            predicted = predict_rss_absolute(rss, {rss["feature"]: 1024.0})
            self.assertAlmostEqual(predicted["upper"] - predicted["center"],
                                   rss["radius_bytes"], places=6)
            self.assertEqual(predicted["lower"], max(
                0.0, predicted["center"] - rss["radius_bytes"]))
        self.assertFalse(model["automatic_lowering_selection_enabled"])

    def test_heldout_checks_new_inventory_and_single_program_rss_gate(self) -> None:
        model = fit_model(synthetic_v5("train", self.protocol), self.protocol)
        held = synthetic_v5("validation", self.protocol)
        result = evaluate(model, held, self.protocol)
        self.assertEqual(len(result["programs"]), 20)
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        held["cases"]["hash_2"]["source_sha256"] = model["training_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "source leaked"):
            evaluate(model, held, self.protocol)
        held = synthetic_v5("validation", self.protocol)
        for trial in held["cases"]["hash_2"]["trials"]:
            trial["prover_peak_rss_bytes"] *= 1.01
        result = evaluate(model, held, self.protocol)
        affected = next(item for item in result["programs"] if item["program"] == "hash_2")
        self.assertLess(affected["targets"]["prover_peak_rss_bytes"]["covered_trials"], 70)
        self.assertFalse(result["local_accuracy_gate_pass"])

        entries = [{"covered_trials": 100, "trial_count": 100,
                    "interval_upper_to_measured_point": 1.1} for _ in range(5)]
        entries[0]["covered_trials"] = 0
        self.assertEqual(sum(row["covered_trials"] for row in entries) /
                         sum(row["trial_count"] for row in entries), .8)
        self.assertFalse(rss_program_gate(entries, self.protocol["accuracy_gate"]))
        entries[0]["covered_trials"] = 70
        self.assertTrue(rss_program_gate(entries, self.protocol["accuracy_gate"]))
        entries[0]["interval_upper_to_measured_point"] = 1.6
        self.assertFalse(rss_program_gate(entries, self.protocol["accuracy_gate"]))

    def test_unfrozen_protocol_cannot_start_native_runner(self) -> None:
        self.assertIsNone(self.protocol["compiler_sha256"])
        self.assertIsNone(self.protocol["measurement_tool_sha256"])
        with self.assertRaisesRegex(ValueError, "must be pinned"):
            require_frozen_pins(self.protocol)
        ephemeral = dict(self.protocol)
        ephemeral.update({
            "source_base_commit": subprocess.check_output(
                ["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip(),
            "engine_gitlink_commit": subprocess.check_output(
                ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
                text=True).strip(),
            "compiler_sha256": s31.compiler_fingerprint(),
            "measurement_tool_sha256": measurement_tool_digest(TOOL_SOURCES),
            "status": "frozen-before-any-v5-native-observation",
        })
        require_frozen_pins(ephemeral)
        ephemeral["measurement_tool_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "measurement tool digest"):
            require_frozen_pins(ephemeral)


if __name__ == "__main__":
    unittest.main()
