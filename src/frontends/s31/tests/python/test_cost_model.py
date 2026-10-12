"""Cost evidence must include whole native processes and expose missing timers."""

import sys
from pathlib import Path

S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

import platform
import unittest
from tempfile import TemporaryDirectory

from runtime.cost_model import measured_invoke, observed_cost_model
sys.path.insert(0, str(S31_SOURCE_ROOT / "benchmarks"))
from benchmark_whole_prover import measured_package_build


class CostModelTests(unittest.TestCase):
    def test_package_build_timing_distinguishes_materialization_from_reuse(self) -> None:
        with TemporaryDirectory() as directory:
            package = Path(directory) / "package"

            def fake_build(_source: Path, destination: Path, _lowering: str) -> Path:
                destination.mkdir(exist_ok=True)
                return destination

            for expected_reused in (False, True):
                returned, measured = measured_package_build(
                    Path(directory) / "source.s31", package, "direct-gate", fake_build)
                self.assertEqual(returned, package)
                self.assertEqual(measured["package_reused"], expected_reused)
                self.assertGreaterEqual(measured["package_build_wall_seconds"], 0)
                self.assertIsNone(measured["package_build_peak_rss_bytes"])
                self.assertIn("uncontrolled", measured["zig_compiler_cache"])

    def test_real_child_peak_rss_is_reported_when_supported(self) -> None:
        measurement = measured_invoke(sys.executable, "-c", "print('proof accepted')")
        self.assertIn("proof accepted", measurement["output"])
        self.assertGreater(measurement["wall_seconds"], 0)
        if platform.system() in {"Darwin", "Linux"} and Path("/usr/bin/time").is_file():
            self.assertGreater(measurement["peak_rss_bytes"], 0)
            self.assertNotEqual(measurement["peak_rss_method"], "unavailable")
        else:
            self.assertIsNone(measurement["peak_rss_bytes"])

    def test_paired_cost_and_missing_pow_are_explicit(self) -> None:
        trials = [
            {"native_verifier_accepted": True, "prove_seconds": prove,
             "verify_seconds": verify, "proof_bytes": 100 + index,
             "prover_peak_rss_bytes": None, "verifier_peak_rss_bytes": 4096,
             "prover_stages": {"witness_seconds": 0.001, "setup_seconds": 0.002,
                               "prove_seconds": 0.003}}
            for index, (prove, verify) in enumerate(((0.020, 0.002), (0.030, 0.004), (0.040, 0.006)))
        ]
        model = observed_cost_model(trials)
        metrics = model["metrics"]
        self.assertAlmostEqual(metrics["paired_prove_and_verify_wall_seconds"]["median"], 0.034)
        self.assertAlmostEqual(metrics["prove_process_wall_seconds"]["median_absolute_deviation"], 0.01)
        self.assertIsNone(metrics["prover_peak_rss_bytes"])
        self.assertIsNone(metrics["runtime_interaction_pow_seconds"])
        self.assertEqual(metrics["runtime_setup_seconds"]["observations"], 3)
        self.assertEqual(metrics["verifier_peak_rss_bytes"]["observations"], 3)

    def test_unverified_proof_cannot_enter_cost_model(self) -> None:
        with self.assertRaisesRegex(ValueError, "verified proofs"):
            observed_cost_model([{"native_verifier_accepted": False}])

    def test_runtime_clock_cannot_exceed_process_wall(self) -> None:
        with self.assertRaisesRegex(ValueError, "runtime total exceeds"):
            observed_cost_model([{
                "native_verifier_accepted": True, "prove_seconds": 0.01,
                "verify_seconds": 0.002, "proof_bytes": 100,
                "prover_stages": {"total_through_verification_seconds": 0.02},
            }])


if __name__ == "__main__":
    unittest.main()
