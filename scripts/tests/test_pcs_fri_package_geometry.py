"""Generated-key controls for fail-closed P01 package geometry extraction."""

import copy
import unittest
from pathlib import Path

from scripts.release.pcs_fri_package_geometry import SOURCE_FILES, check_source_texts, extract_fields

ROOT = Path(__file__).resolve().parents[2]


FRI = {"pow_bits": 26, "log_blowup_factor": 1,
       "last_layer_degree_bound": 1, "queries": 70, "fold_step": 1}


def package(lowering="gate", schema="s31-verification-key-gate-roster-v1",
            profile="circuit-v1"):
    manifest = {"schema": "s31-package-v1", "lowering": lowering, "fri_fold_step": 1}
    key = {"schema": schema, "profile": profile, "trace_log_size": 11,
           "fri": copy.deepcopy(FRI)}
    return manifest, key


def rows(count):
    return [{"name": f"component_{i}", "proof_index": i,
             "trace_log_size": i + 1} for i in range(count)]


def fixed():
    return [{"id": "fixed_0", "commitment_index": 0,
             "log_size": 2, "rows": 4}]


class PackageGeometryTests(unittest.TestCase):
    def test_gate_roster_and_configured_domains(self):
        manifest, key = package()
        roster = {"schema": "s31-component-roster-gate-v1", "components": rows(11),
                  "preprocessed_columns": fixed()}
        result = extract_fields(manifest, key, roster)
        self.assertEqual(result["candidate_N_trace_rows"], 2048)
        self.assertEqual(result["configured_trace_lifting_rows"], 4096)
        self.assertEqual(result["components"][0]["configured_extended_rows"], 4)
        self.assertTrue(result["component_roster_complete"])
        self.assertEqual(result["preprocessed_columns"][0]["rows"], 4)
        self.assertIsNone(result["theorem_inputs"]["D_final_fri_domain"])
        self.assertFalse(result["proven_release_admissible"])

    def test_sparse_roster_and_direct_manifest(self):
        manifest, key = package("sparse-gate", "s31-verification-key-sparse-roster-v1", "sparse-v3")
        result = extract_fields(manifest, key,
                                {"schema": "s31-component-roster-sparse-gate-v1",
                                 "components": rows(3), "preprocessed_columns": fixed()})
        self.assertEqual(len(result["components"]), 3)
        manifest, key = package("direct-gate", "s31-verification-key-direct-manifest-v2", "direct-m31-v4")
        key["component_manifest"] = {"components": [{**rows(1)[0], "evaluation_log_size": 2}],
                                     "preprocessed_columns": fixed()}
        result = extract_fields(manifest, key, key["component_manifest"])
        self.assertEqual(result["components"][0]["configured_extended_log_size"], 2)

    def test_sha_reports_partial_logs_and_missing_roster(self):
        for lowering, suffix in (("sha-joint", "joint-v1"),
                                 ("sha-shift", "shift-v3"),
                                 ("sha-fused", "fused-v4")):
            with self.subTest(lowering=lowering):
                manifest, key = package(lowering, "s31-verification-key-sha-" + suffix,
                                        "sha-" + suffix)
                key[lowering.replace("-", "_")] = {"circuit_logs": [4, 8, 6, 10]}
                result = extract_fields(manifest, key)
                self.assertEqual(result["partial_component_metadata"]["sha_circuit_logs"], [4, 8, 6, 10])
                self.assertEqual(result["components"], [])
                self.assertFalse(result["component_roster_complete"])
                self.assertIn("full SHA component-name-to-domain roster", result["missing_package_geometry"])

    def test_four_fold_gate_schedule_is_reported(self):
        manifest, key = package()
        manifest["fri_fold_step"] = 4
        key["fri"]["fold_step"] = 4
        result = extract_fields(manifest, key,
                                {"schema": "s31-component-roster-gate-v1",
                                 "components": rows(11), "preprocessed_columns": fixed()})
        self.assertEqual(result["fri"]["fold_step"], 4)

    def test_unrostered_chip_stays_incomplete(self):
        manifest, key = package("chip", "s31-verification-key-v2", "hybrid-step-v2")
        result = extract_fields(manifest, key)
        self.assertEqual(result["missing_package_geometry"],
                         ["per-component trace-domain roster", "preprocessed column domain roster"])

    def test_mutated_fields_reject(self):
        manifest, key = package()
        roster = {"schema": "s31-component-roster-gate-v1", "components": rows(11),
                  "preprocessed_columns": fixed()}
        changes = (
            lambda m, k, r: k["fri"].update(queries=69),
            lambda m, k, r: k["fri"].update(log_blowup_factor=True),
            lambda m, k, r: k["fri"].update(fold_step=True),
            lambda m, k, r: k.update(trace_log_size=True),
            lambda m, k, r: m.update(fri_fold_step=4),
            lambda m, k, r: k.update(schema="s31-verification-key-v1"),
            lambda m, k, r: r["components"][0].update(trace_log_size=12),
            lambda m, k, r: r["components"][1].update(proof_index=0),
            lambda m, k, r: r["components"][1].update(name="component_0"),
            lambda m, k, r: r["components"].pop(),
            lambda m, k, r: r["preprocessed_columns"][0].update(rows=8),
            lambda m, k, r: r["preprocessed_columns"][0].update(rows=True),
        )
        for mutate in changes:
            with self.subTest(mutate=mutate):
                m, k, r = copy.deepcopy((manifest, key, roster))
                mutate(m, k, r)
                with self.assertRaises(ValueError):
                    extract_fields(m, k, r)

    def test_direct_evaluation_log_mismatch_rejects(self):
        manifest, key = package("direct-gate", "s31-verification-key-direct-manifest-v2", "direct-m31-v4")
        key["component_manifest"] = {"components": [{**rows(1)[0], "evaluation_log_size": 3}],
                                     "preprocessed_columns": fixed()}
        with self.assertRaisesRegex(ValueError, "evaluation log differs"):
            extract_fields(manifest, key, key["component_manifest"])

    @unittest.skipUnless((ROOT / SOURCE_FILES[-1]).is_file(), "engine submodule not checked out")
    def test_pinned_native_source_changes_reject(self):
        sources = {name: (ROOT / name).read_text() for name in SOURCE_FILES}
        check_source_texts(sources)
        mutations = (
            (SOURCE_FILES[0], "FriConfigV2.init(26, 0, 1, 70, fri_fold_step)",
             "FriConfigV2.init(26, 0, 2, 70, fri_fold_step)"),
            (SOURCE_FILES[1], "FriConfigV2.init(26, 0, 1, 70, 1)",
             "FriConfigV2.init(26, 0, 2, 70, 1)"),
            (SOURCE_FILES[-1], "trace_log_size + config.log_blowup_factor",
             "trace_log_size"),
        )
        for name, old, new in mutations:
            with self.subTest(path=name):
                self.assertIn(old, sources[name])
                changed = dict(sources)
                changed[name] = changed[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_source_texts(changed)


if __name__ == "__main__":
    unittest.main()
