"""Generated-envelope controls for the conditional gate FRI-domain diagnostic."""

import copy
import hashlib
import json
import struct
import unittest
from pathlib import Path

from scripts.release.pcs_fri_gate_final_domain import (
    BUNDLE, SOURCE_TOKENS, BundleComponent, bundle_components, bundle_offsets,
    check_source_texts, derive_gate, derive_gate_constraint_roster,
    derive_gate_trace_and_fri_schedule,
)
from scripts.release.pcs_fri_package_geometry import extract_fields

ROOT = Path(__file__).resolve().parents[2]
GATE_FIXTURE = ROOT / "src/frontends/s31/tests/python/security/fixtures/effects_gate_ownership"
NAMES = ("eq", "qm31_ops", "triple_xor", "m_31_to_u_32", "blake_g_gate",
         "verify_bitwise_xor_8", "verify_bitwise_xor_12", "verify_bitwise_xor_4",
         "verify_bitwise_xor_7", "verify_bitwise_xor_9", "range_check_16")


def synthetic_bundle(rows):
    pieces = [struct.pack("<8sIIQIIQ", b"STWZEVA\x00", 1, 1, len(rows),
                          max(e for _, _, e in rows), len(rows), 1)]
    for index, (name, trace, evaluation) in enumerate(rows):
        encoded = name.encode()
        pieces += [struct.pack("<HH10I", len(encoded), 0, index, trace, evaluation,
                               1, index, 1, 0, 1 << (evaluation - trace), 0, 1),
                   encoded, struct.pack("<III", 0, 0, 1),
                   b"\0" * (4 * (1 << (evaluation - trace))),
                   struct.pack("<IIQ", 0, 1, 1), b"\0"]
    return b"".join(pieces)


def gate_report(logs):
    manifest = {"schema": "s31-package-v1", "lowering": "gate", "fri_fold_step": 1}
    key = {"schema": "s31-verification-key-gate-roster-v1", "profile": "circuit-v1",
           "trace_log_size": max(logs), "fri": {"pow_bits": 26, "log_blowup_factor": 1,
           "last_layer_degree_bound": 1, "queries": 70, "fold_step": 1}}
    roster = {"schema": "s31-component-roster-gate-v1",
              "components": [{"name": name, "proof_index": i, "trace_log_size": log}
                             for i, (name, log) in enumerate(zip(NAMES, logs, strict=True))],
              "preprocessed_columns": [{"id": "fixed", "commitment_index": 0,
                                        "log_size": 1, "rows": 2}]}
    report = extract_fields(manifest, key, roster)
    report["package_checks"] = {"native_check_key": "accepted"}
    return report


class GateFinalDomainTests(unittest.TestCase):
    def test_sealed_gate_trace_widths_and_native_fold_schedule(self):
        key = json.loads((GATE_FIXTURE / "verification-key.json").read_text())
        roster = json.loads((GATE_FIXTURE / "gate-component-roster.json").read_text())
        manifest = {"schema": "s31-package-v1", "lowering": "gate", "fri_fold_step": 1}
        report = extract_fields(manifest, key, roster)
        report["package_checks"] = {"native_check_key": "accepted"}
        report = derive_gate(report, [(name, 1) for name in NAMES])
        derive_gate_trace_and_fri_schedule(report, roster)
        native = report["gate_trace_and_fri_schedule"]
        self.assertEqual(len(native["tables"]), 11)
        self.assertEqual(len(native["preprocessed_columns"]), 45)
        self.assertEqual(native["main_trace_column_count"], 114)
        self.assertEqual(native["interaction_trace_column_count"], 152)
        self.assertEqual(native["tables"][6]["trace_rows"], 1 << 20)
        self.assertEqual(native["tables"][6]["main_trace_columns"], 16)
        self.assertEqual([(tree["kind"], tree["column_count"], tree["lifted_height_log_size"])
                          for tree in native["pcs_commitment_trees"]],
                         [("preprocessed", 45, 21), ("main", 114, 21),
                          ("interaction", 152, 21), ("composition", 8, 21)])
        self.assertEqual(native["pcs_commitment_trees"][3]["column_log_size"], 20)
        self.assertEqual(native["fri_first_circle_commitments"], 1)
        self.assertEqual(native["fri_inner_line_commitments"], 19)
        self.assertEqual(native["fri_folding_challenges"], 20)
        self.assertEqual(native["fri_commitment_and_fold_rounds"][0], {
            "commitment_index": 0, "kind": "circle_first",
            "commitment_domain_log_size": 21, "degree_log_bound_before_fold": 20,
            "fold_step": 1, "degree_log_bound_after_fold": 19,
            "next_domain_log_size": 20,
        })
        self.assertEqual(native["fri_commitment_and_fold_rounds"][-1]["commitment_domain_log_size"], 2)
        self.assertEqual(native["terminal_line_domain_rows"], 2)
        self.assertEqual(native["terminal_polynomial_max_coefficients"], 1)
        self.assertEqual(native["raw_query_draws"], 70)
        self.assertIsNone(native["unique_query_count"])
        self.assertIsNone(native["published_theorem_parameter_mapping"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertFalse(report["proven_release_admissible"])

        changed = copy.deepcopy(roster)
        changed["components"][0]["base_trace_columns"] = 0
        with self.assertRaisesRegex(ValueError, "invalid main trace width"):
            derive_gate_trace_and_fri_schedule(copy.deepcopy(report), changed)
        changed = copy.deepcopy(roster)
        changed["components"][0]["trace_log_size"] += 1
        with self.assertRaisesRegex(ValueError, "width or height"):
            derive_gate_trace_and_fri_schedule(copy.deepcopy(report), changed)
        changed = copy.deepcopy(roster)
        changed["preprocessed_columns"][0]["rows"] += 1
        with self.assertRaisesRegex(ValueError, "fixed-column height"):
            derive_gate_trace_and_fri_schedule(copy.deepcopy(report), changed)
        changed = copy.deepcopy(report)
        changed["fri"]["fold_step"] = 4
        with self.assertRaisesRegex(ValueError, "unreviewed gate FRI schedule"):
            derive_gate_trace_and_fri_schedule(changed, roster)
        changed = copy.deepcopy(report)
        changed["fri"]["fold_step"] = True
        with self.assertRaisesRegex(ValueError, "invalid gate fold step"):
            derive_gate_trace_and_fri_schedule(changed, roster)
        changed = copy.deepcopy(report)
        changed["fri"]["last_layer_degree_bound"] = True
        with self.assertRaisesRegex(ValueError, "invalid terminal degree bound"):
            derive_gate_trace_and_fri_schedule(changed, roster)
        changed = copy.deepcopy(roster)
        changed["components"][1]["proof_index"] = True
        with self.assertRaisesRegex(ValueError, "invalid sealed table proof index"):
            derive_gate_trace_and_fri_schedule(copy.deepcopy(report), changed)
        changed = copy.deepcopy(roster)
        changed["preprocessed_columns"][1]["log_size"] = True
        with self.assertRaisesRegex(ValueError, "invalid sealed fixed-column log"):
            derive_gate_trace_and_fri_schedule(copy.deepcopy(report), changed)
        changed = copy.deepcopy(report)
        changed["gate_final_domain"]["fri_input_degree_bound_log"] -= 1
        with self.assertRaisesRegex(ValueError, "input degree or domain"):
            derive_gate_trace_and_fri_schedule(changed, roster)

    def test_metadata_parser_and_mutations(self):
        data = synthetic_bundle([("eq", 4, 5), ("qm31_ops", 7, 8)])
        self.assertEqual(bundle_offsets(data), [("eq", 1), ("qm31_ops", 1)])
        self.assertEqual(bundle_components(data), [
            BundleComponent("eq", 1, 1, 1), BundleComponent("qm31_ops", 1, 1, 1)])
        mutations = (data[:-1], data + b"\0", b"wrong!!!" + data[8:],
                     data[:28] + struct.pack("<I", 3) + data[32:])
        for altered in mutations:
            with self.subTest(size=len(altered)), self.assertRaises(ValueError):
                bundle_offsets(altered)

    def test_derived_bounds_and_conditional_domain(self):
        logs = (4, 7, 5, 4, 7, 4, 5, 4, 4, 4, 4)
        report = derive_gate(gate_report(logs), [(name, 1) for name in NAMES])
        derived = report["gate_final_domain"]
        self.assertEqual(derived["unsplit_composition_log_degree_bound"], 8)
        self.assertEqual(derived["split_composition_log_degree_bound"], 7)
        self.assertEqual(derived["committed_composition_column_log_size"], 7)
        self.assertEqual(derived["fri_input_degree_bound_log"], 7)
        self.assertEqual(derived["fri_input_domain_rows"], 256)
        self.assertEqual(derived["candidate_paper_protocol4_D0_if_N_is_trace_rows"], 512)
        self.assertEqual(derived["candidate_paper_domain_cap_rows"], 1 << 30)
        self.assertFalse(derived["native_fri_domain_equals_candidate_paper_protocol4_D0"])
        self.assertEqual(derived["candidate_smallest_component_rows"], 16)
        self.assertTrue(derived["conditional_small_table_ood_for_every_udr_theta_if_components_are_tables"])
        self.assertEqual(report["theorem_inputs"]["D_final_fri_domain"], 256)
        self.assertFalse(report["proven_release_admissible"])
        self.assertEqual(report["status"], "incomplete")

    def test_air_constraint_counts_are_conditional_metadata(self):
        logs = (4, 7, 5, 4, 7, 4, 5, 4, 4, 4, 4)
        report = derive_gate(gate_report(logs), [(name, 1) for name in NAMES])
        components = [BundleComponent(name, 1, index + 1, 1)
                      for index, name in enumerate(NAMES)]
        derive_gate_constraint_roster(report, components)
        roster = report["gate_air_constraint_roster"]
        self.assertEqual(roster["native_total_constraints"], 66)
        self.assertEqual(roster["components"][1], {
            "name": "qm31_ops", "native_constraint_count": 2,
            "native_program_parts": 1})
        self.assertFalse(roster["identified_as_published_k_t"])
        self.assertFalse(report["proven_release_admissible"])
        with self.assertRaisesRegex(ValueError, "order differ"):
            derive_gate_constraint_roster(report, list(reversed(components)))
        with self.assertRaisesRegex(ValueError, "invalid AIR constraint"):
            derive_gate_constraint_roster(report, [BundleComponent(NAMES[0], 1, 1, 2)] + components[1:])

    def test_adversarial_roster_and_degree_controls(self):
        logs = (4, 7, 5, 4, 7, 4, 5, 4, 4, 4, 4)
        base = gate_report(logs)
        with self.assertRaisesRegex(ValueError, "order differ"):
            derive_gate(copy.deepcopy(base), [(name, 1) for name in reversed(NAMES)])
        with self.assertRaisesRegex(ValueError, "cannot fit"):
            derive_gate(copy.deepcopy(base), [(name, 3) for name in NAMES])
        rejected = copy.deepcopy(base)
        rejected["package_checks"]["native_check_key"] = "unsupported-by-installed-verifier"
        with self.assertRaisesRegex(ValueError, "native check-key"):
            derive_gate(rejected, [(name, 1) for name in NAMES])
        rejected = copy.deepcopy(base)
        rejected["lowering"] = "chip"
        with self.assertRaisesRegex(ValueError, "only the sealed gate"):
            derive_gate(rejected, [(name, 1) for name in NAMES])
        rejected = copy.deepcopy(base)
        rejected["max_trace_log_size"] = 30
        rejected["configured_trace_lifting_log_size"] = 31
        with self.assertRaisesRegex(ValueError, "exceeds circle"):
            derive_gate(rejected, [(name, 1) for name in NAMES])
        # N*B fits the native circle, while the paper's full N*B^2
        # ensemble exceeds its 2^30 domain cap.
        logs = (29,) * len(NAMES)
        rejected = gate_report(logs)
        with self.assertRaisesRegex(ValueError, "N\\*B\\^2 exceeds"):
            derive_gate(rejected, [(name, 1) for name in NAMES])
        accepted = gate_report((28,) * len(NAMES))
        boundary = derive_gate(accepted, [(name, 1) for name in NAMES])
        self.assertEqual(boundary["gate_final_domain"]["candidate_paper_protocol4_D0_if_N_is_trace_rows"],
                         1 << 30)
        # A two-row component does not satisfy the uniform theta premise.
        tiny = gate_report((1,) + (4,) * (len(NAMES) - 1))
        small_table = derive_gate(tiny, [(name, 1) for name in NAMES])
        self.assertFalse(small_table["gate_final_domain"][
            "conditional_small_table_ood_for_every_udr_theta_if_components_are_tables"])

    @unittest.skipUnless((ROOT / BUNDLE).is_file(), "pinned engine submodule not checked out")
    def test_real_bundle_offsets_and_source_mutation(self):
        sources = {name: (ROOT / name).read_text() for name in SOURCE_TOKENS}
        digest = check_source_texts(sources)
        data = (ROOT / BUNDLE).read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), digest)
        self.assertEqual(bundle_offsets(data), [(name, 1) for name in NAMES])
        components = bundle_components(data)
        self.assertEqual(sum(item.constraints for item in components), 57)
        self.assertEqual(components[1].constraints, 11)
        changed = dict(sources)
        name = "deps/stwo-zig/src/core/pcs/verifier.zig"
        changed[name] = changed[name].replace(
            "break :blk self.trees.items[self.trees.items.len - 1].height;",
            "break :blk 0;", 1)
        with self.assertRaisesRegex(ValueError, "source changed"):
            check_source_texts(changed)
        changed = dict(sources)
        name = "src/frontends/s31/runtime/native_verifier.zig"
        first = "try scheme.commit(allocator, roots[0], &pp_logs, &channel);"
        second = "try scheme.commit(allocator, roots[1], main_logs, &channel);"
        changed[name] = changed[name].replace(first, "TEMPORARY_GATE_COMMIT", 1).replace(
            second, first, 1).replace("TEMPORARY_GATE_COMMIT", second, 1)
        with self.assertRaisesRegex(ValueError, "source order changed"):
            check_source_texts(changed)
        changed = dict(sources)
        name = "deps/stwo-zig/src/core/fri.zig"
        changed[name] = changed[name].replace(
            "const this_fold_step: u32 = config_mod.foldStepAt(config.fold_step, remaining);",
            "const this_fold_step: u32 = remaining;", 1)
        with self.assertRaisesRegex(ValueError, "source changed"):
            check_source_texts(changed)


if __name__ == "__main__":
    unittest.main()
