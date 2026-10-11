#!/usr/bin/env python3
"""Native-free guards for V17 mixed-length N4/N8 and log14 challenge."""

from __future__ import annotations

import copy
import importlib.util
import unittest

import model as m
import protocol as p

spec = importlib.util.spec_from_file_location("v17_study", p.HERE / "study.py")
if spec is None or spec.loader is None:
    raise RuntimeError("V17 study loader missing")
study = importlib.util.module_from_spec(spec)
spec.loader.exec_module(study)
audit_spec = importlib.util.spec_from_file_location("v17_audit", p.HERE / "audit.py")
if audit_spec is None or audit_spec.loader is None:
    raise RuntimeError("V17 audit loader missing")
audit = importlib.util.module_from_spec(audit_spec)
audit_spec.loader.exec_module(audit)


class MixedCallsStaticTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.model = m.derive()
        cls.protocol = p.prepare_value()

    def test_declared_training_and_frozen_predictions(self) -> None:
        self.assertEqual(m.canonical(self.model), m.FROZEN.read_bytes())
        self.assertIn("V11/V15 failed", self.model["evidence_classification"])
        self.assertIn("V12/V13/V14/V16 passed", self.model["evidence_classification"])
        self.assertLessEqual(self.model["proof_relative_half_width"], 0.15)
        self.assertGreater(self.model["proof_relative_half_width"], 0.09)
        self.assertEqual(self.model["input_sha256"]["v12_model"],
                         m.sha(m.INPUTS["v12_model"].read_bytes()))
        self.assertEqual(set(m.SPECS), set(p.SOURCES))
        self.assertIn("no defensible gate", self.model["build_cold_prediction_status"])
        for name in p.SOURCES:
            prediction = m.prediction(self.model, name)
            for field in ("warm_wall_one_draw_quantile_ns",
                          "warm_wall_sample20_median_quantile_ns",
                          "fri_pow_one_draw_quantile_ns",
                          "interaction_pow_one_draw_quantile_ns"):
                q = prediction[field]
                self.assertLess(q["0.05"], q["0.5"])
                self.assertLess(q["0.5"], q["0.95"])
        with self.assertRaises(ValueError):
            m.prediction(self.model, "training_source_not_frozen")

    def test_fresh_sources_and_interleaved_schedule(self) -> None:
        self.assertEqual(set(self.protocol["source_roster"]), set(p.SOURCES))
        self.assertEqual(self.protocol["v17_model_sha256"], p.sha(p.MODEL.read_bytes()))
        seen: set[str] = set()
        for name, expected in self.protocol["source_roster"].items():
            spec = p.SOURCES[name]
            self.assertEqual(spec["rounds"], m.SPECS[name]["rounds"])
            self.assertEqual(spec["mul_every"], m.SPECS[name]["mul_every"])
            self.assertEqual(spec["ops"], m.SPECS[name]["ops"])
            self.assertEqual(spec["branches"], 16)
            self.assertEqual(expected["live_mul_nodes"], sum(
                (index + branch) % spec["mul_every"] == 0
                for index in range(spec["ops"] // spec["branches"])
                for branch in range(spec["branches"])))
            self.assertEqual(expected["live_add_nodes"], spec["ops"] - expected["live_mul_nodes"])
            geometry = expected["expected_geometry"]
            self.assertEqual(geometry["slots"], 1 + 2 * len(spec["rounds"]))
            self.assertEqual(geometry["slot_trace_logs"],
                             [spec["ops"].bit_length()] +
                             [entry for rounds in spec["rounds"]
                              for entry in (rounds.bit_length() - 1, 4)])
            self.assertEqual(geometry["composition_log_size"],
                             max(geometry["slot_trace_logs"]))
            self.assertEqual(expected["source_sha256"], p.sha(p.source(name)))
            for index in range(p.CLAIMS + 1):
                source, assignment, statement = p.case(name, index)
                self.assertEqual(source, p.source(name))
                for raw, expected_digest in ((assignment, expected["assignment_sha256"][index]),
                                             (statement, expected["statement_sha256"][index])):
                    digest = p.sha(raw)
                    self.assertEqual(digest, expected_digest)
                    self.assertNotIn(digest, seen)
                    seen.add(digest)
        self.assertEqual(len(seen), 126)
        schedule = p.schedule()
        self.assertEqual(schedule, self.protocol["scored_schedule"])
        self.assertEqual(len(schedule), 60)
        self.assertEqual(len({(item["name"], item["claim_index"]) for item in schedule}), 60)
        for offset in range(0, 60, 3):
            block = schedule[offset:offset + 3]
            self.assertEqual(len({item["name"] for item in block}), 3)
            self.assertEqual(len({item["claim_index"] for item in block}), 1)

    def test_manifest_and_score_guards(self) -> None:
        original = study.registry_manifest_digest
        study.registry_manifest_digest = lambda _: "digest"
        try:
          for name in ("calls8_log13", "calls4_log14"):
            expected = self.protocol["source_roster"][name]
            geometry = expected["expected_geometry"]
            count = expected["call_count"]
            manifest = {"schema": "s31-mixed-component-inspection-general-v3",
                        "source_sha256": expected["source_sha256"], "call_count": count,
                        "slot_count": geometry["slots"], "interaction_pow_bits": 20,
                        "pcs": {"fri_config": {"pow_bits": 26}},
                        "slots": [{"trace_log_size": log, "n_constraints": n}
                                  for log, n in zip(geometry["slot_trace_logs"],
                                                    [11] + [value for _ in range(count)
                                                            for value in (6, 13)], strict=True)],
                        "calls": [{"rounds": rounds} for rounds in expected["chip_rounds"]],
                        "tree_columns": geometry["tree_columns"],
                        "total_constraints": geometry["constraints"],
                        "main_columns": geometry["tree_columns"][1],
                        "interaction_columns": geometry["tree_columns"][2],
                        "max_column_log_size": max(geometry["slot_trace_logs"]),
                        "composition_log_size": max(geometry["slot_trace_logs"]),
                        "registry_manifest_sha256": "digest"}
            study.check_manifest(manifest, expected)
            for key in ("max_column_log_size", "composition_log_size"):
                bad = copy.deepcopy(manifest)
                bad[key] -= 1
                with self.assertRaises(ValueError):
                    study.check_manifest(bad, expected)
            bad = copy.deepcopy(manifest)
            bad["slots"][1]["trace_log_size"] = 11
            with self.assertRaises(ValueError):
                study.check_manifest(bad, expected)
        finally:
            study.registry_manifest_digest = original

    def test_runner_and_independent_score_agree_on_synthetic_rows(self) -> None:
        expected = self.protocol["source_roster"]["calls8_log13"]
        prediction = expected["prediction"]
        wall = round(prediction["warm_wall_one_draw_quantile_ns"]["0.5"])
        size = round(prediction["proof_bytes_center"])
        prover_rss = round(prediction["prover_peak_rss_median_bytes"])
        verifier_rss = round(prediction["verifier_peak_rss_median_bytes"])
        rows = []
        for index in range(22):
            rows.append({"claim_index": max(0, index - 1),
                         "first_verified_process_wall_ns": wall,
                         "proof_bytes": size,
                         "native_phases_ns": {"fri_pow_ns": 10_000_000,
                                              "interaction_pow_ns": 1_000_000},
                         "package_stages_ns": prediction["native_package_phase_center_ns"],
                         "prover_process_monotonic_ns": {"peak_rss_bytes": prover_rss},
                         "external_verifier_process_monotonic_ns": {
                             "peak_rss_bytes": verifier_rss}})
        official = study.score_record({"trials": rows, "build_wall_ns": 1},
                                      expected, p.GATES)
        independent = audit.calculated_score(rows, prediction, p.GATES)
        self.assertEqual(official["gates"], independent["gates"])
        for field in ("wall_median_relative_error", "wall_one_draw_interval_hits",
                      "wall_one_draw_interval_coverage", "wall_sample20_median_in_band",
                      "proof_median_relative_error", "proof_interval_coverage",
                      "prover_rss_median_relative_error", "verifier_rss_median_relative_error",
                      "nonpow_wall_median_relative_error",
                      "observed_native_package_phase_medians_ns",
                      "native_package_phase_relative_errors"):
            self.assertEqual(official[field], independent[field])
        self.assertEqual(official["all_gates_pass"], independent["all_gates_pass"])


if __name__ == "__main__":
    unittest.main()
