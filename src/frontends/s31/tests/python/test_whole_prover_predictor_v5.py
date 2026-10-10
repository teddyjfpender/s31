"""Static V5 admission, fresh split, absolute-byte RSS, and draft freeze tests."""

import hashlib
import json
import subprocess
import sys
import unittest
from datetime import datetime, timezone
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(S31_ROOT / "benchmarks"), str(S31_ROOT / "python"),
                str(Path(__file__).resolve().parent)]

from benchmark_whole_prover_cost_v4 import workload_cases as v4_workloads
from benchmark_whole_prover_cost_v5 import (
    PROTOCOL, TOOL_SOURCES, check_build_inventory, checked_sha, committed_anchor,
    require_frozen_pins, tool_source_inventory, workload_cases,
)
from benchmark_whole_prover_cost_v3 import ROOT, measurement_tool_digest, s31
from whole_prover_predictor_v5 import (
    evaluate, fit_model, predict_rss_absolute, rss_program_gate,
)
from publish_whole_prover_cost_v5 import assert_build_case_binding
from test_whole_prover_predictor_v3 import synthetic_corpus
from whole_prover_predictor_v3 import expected_names


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


def write_build_fixture(output: Path, split: str, protocol: dict,
                        protocol_sha: str, model_sha: str | None = None) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    inventory = {
        "schema": "s31-whole-prover-build-inventory-v5",
        "split": split, "protocol_sha256": protocol_sha,
        "compiler_sha256": protocol["compiler_sha256"],
        "measurement_tool_sha256": protocol["measurement_tool_sha256"],
        "protocol_anchor_commit": "a" * 40,
        "model_anchor_commit": "b" * 40 if model_sha is not None else None,
        "frozen_model_sha256": model_sha,
        "programs": {},
    }
    for name in expected_names(split, protocol):
        source = output / "generated-sources" / (
            name + (".s31" if name.startswith("signed_") else ".s31.json"))
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(name)
        source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
        build = {"source_sha256": source_sha,
                 "compiler_sha256": protocol["compiler_sha256"],
                 "measurement_tool_sha256": protocol["measurement_tool_sha256"],
                 "package_build": {"package_reused": False,
                                   "package_build_wall_seconds": 1.0}}
        record_path = output / name / "package-build-record.json"
        record_path.parent.mkdir(parents=True, exist_ok=True)
        record_path.write_text(json.dumps(build))
        inventory["programs"][name] = {
            "source_sha256": source_sha,
            "chip_manifest_binding": None,
            "package_build": build["package_build"],
        }
    (output / "whole-prover-build-inventory.json").write_text(json.dumps(inventory))
    return inventory


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
        draft = dict(self.protocol)
        draft["compiler_sha256"] = None
        draft["measurement_tool_sha256"] = None
        draft["measurement_tool_paths"] = None
        draft["status"] = "draft"
        with self.assertRaisesRegex(ValueError, "must be pinned"):
            require_frozen_pins(draft)
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
            "measurement_tool_paths": tool_source_inventory(),
            "status": "frozen-before-any-v5-native-observation",
        })
        require_frozen_pins(ephemeral)
        ephemeral["measurement_tool_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "measurement tool digest"):
            require_frozen_pins(ephemeral)

    def test_protocol_mutation_between_build_and_prove_fails_before_native(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            protocol_path = root / "protocol.json"
            protocol_path.write_bytes(PROTOCOL.read_bytes())
            original_sha = hashlib.sha256(protocol_path.read_bytes()).hexdigest()
            output = root / "build"
            original = json.loads(protocol_path.read_text())
            write_build_fixture(output, "train", original, original_sha)
            checked_sha(protocol_path, original_sha, "protocol")
            with patch("benchmark_whole_prover_cost_v5.chip_manifest_binding",
                       return_value=None):
                check_build_inventory(output, "train", original, original_sha,
                                      protocol_anchor_commit="a" * 40)
            changed = json.loads(protocol_path.read_text())
            changed["accuracy_gate"]["per_family_whole_wall_trial_interval_coverage_min"] = .7
            protocol_path.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "externally recorded"):
                checked_sha(protocol_path, original_sha, "protocol")
            changed_sha = hashlib.sha256(protocol_path.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "build inventory protocol SHA"):
                check_build_inventory(output, "train", changed, changed_sha,
                                      protocol_anchor_commit="a" * 40)
            changed["splits"]["train"]["assignment_index_base"] += 1
            protocol_path.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "externally recorded"):
                checked_sha(protocol_path, original_sha, "protocol")

    def test_model_mutation_after_validation_build_fails_before_native(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            model_path = root / "model.json"
            model_path.write_text('{"training_corpus_sha256":"' + "b" * 64 + '"}')
            original_sha = hashlib.sha256(model_path.read_bytes()).hexdigest()
            output = root / "build"
            inventory = write_build_fixture(
                output, "validation", self.protocol,
                hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(), original_sha)
            checked_sha(model_path, original_sha, "model")
            with patch("benchmark_whole_prover_cost_v5.chip_manifest_binding",
                       return_value=None):
                check_build_inventory(output, "validation", self.protocol,
                                      inventory["protocol_sha256"], original_sha,
                                      "a" * 40, "b" * 40)
            model_path.write_text('{"training_corpus_sha256":"' + "c" * 64 + '"}')
            with self.assertRaisesRegex(ValueError, "externally recorded"):
                checked_sha(model_path, original_sha, "model")
            changed_sha = hashlib.sha256(model_path.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "frozen model SHA"):
                check_build_inventory(output, "validation", self.protocol,
                                      inventory["protocol_sha256"], changed_sha,
                                      "a" * 40, "b" * 40)

    def test_build_wall_and_source_metadata_are_bound_before_proving(self) -> None:
        with TemporaryDirectory() as directory:
            output = Path(directory) / "build"
            protocol_sha = hashlib.sha256(PROTOCOL.read_bytes()).hexdigest()
            inventory = write_build_fixture(output, "train", self.protocol, protocol_sha)
            inventory_path = output / "whole-prover-build-inventory.json"
            name = "arithmetic_24"
            built = inventory["programs"][name]
            case = {"source_sha256": built["source_sha256"],
                    "package_build": dict(built["package_build"]),
                    "chip_manifest_binding": None}
            assert_build_case_binding(name, built, case)
            case["package_build"]["package_build_wall_seconds"] = 999
            with self.assertRaisesRegex(ValueError, "final corpus"):
                assert_build_case_binding(name, built, case)
            build_path = output / name / "package-build-record.json"
            source_path = output / "generated-sources" / f"{name}.s31.json"
            with patch("benchmark_whole_prover_cost_v5.chip_manifest_binding",
                       return_value=None):
                check_build_inventory(output, "train", self.protocol, protocol_sha,
                                      protocol_anchor_commit="a" * 40)
                tampered = json.loads(inventory_path.read_text())
                tampered["programs"][name]["package_build"]["package_build_wall_seconds"] = 999
                inventory_path.write_text(json.dumps(tampered))
                with self.assertRaisesRegex(ValueError, "build record"):
                    check_build_inventory(output, "train", self.protocol, protocol_sha,
                                          protocol_anchor_commit="a" * 40)
                inventory_path.write_text(json.dumps(inventory))
                build = json.loads(build_path.read_text())
                build["package_build"]["package_build_wall_seconds"] = 999
                build_path.write_text(json.dumps(build))
                with self.assertRaisesRegex(ValueError, "build record"):
                    check_build_inventory(output, "train", self.protocol, protocol_sha,
                                          protocol_anchor_commit="a" * 40)
                build["package_build"]["package_build_wall_seconds"] = 1.0
                build_path.write_text(json.dumps(build))
                source_path.write_text("different")
                with self.assertRaisesRegex(ValueError, "generated source"):
                    check_build_inventory(output, "train", self.protocol, protocol_sha,
                                          protocol_anchor_commit="a" * 40)

    def test_freeze_anchor_requires_committed_bytes_and_schema(self) -> None:
        with TemporaryDirectory() as directory:
            repo = Path(directory)
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.name", "V5 test"],
                           check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.email",
                            "v5-test@example.invalid"], check=True)
            path = repo / "protocol-freeze.json"
            anchor = {"schema": "s31-whole-prover-v5-protocol-freeze",
                      "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
                      "protocol_sha256": "a" * 64}
            path.write_text(json.dumps(anchor))
            subprocess.run(["git", "-C", str(repo), "add", path.name], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "-qm", "freeze"], check=True)
            commit = subprocess.check_output(
                ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
            with patch("benchmark_whole_prover_cost_v5.ROOT", repo):
                self.assertEqual(committed_anchor(path, commit, anchor["schema"]), anchor)
                with self.assertRaisesRegex(ValueError, "wrong schema"):
                    committed_anchor(path, commit, "s31-whole-prover-v5-model-freeze")
                path.write_text(json.dumps({**anchor, "protocol_sha256": "b" * 64}))
                with self.assertRaisesRegex(ValueError, "differs from its recorded commit"):
                    committed_anchor(path, commit, anchor["schema"])


if __name__ == "__main__":
    unittest.main()
