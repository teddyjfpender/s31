"""Native-free checks for prospective mixed cost cohort, accounting and gates."""

from __future__ import annotations

import copy
import json
import os
import subprocess
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import patch

import anchors
import protocol
from cohort import ROOT, canonical, case, design, inventory, sha
from evidence import bins, check_materialized, materialize, phase_root, replay_trial, zig_cache_path
from model import components, evaluate, fit_model, predict
from protocol import check, tool_paths


def synthetic_report(count: int, index: int, *, slowdown: float = 1.0) -> dict:
    variation = 1 + ((index % 5) - 2) / 100
    stages = {
        "profile_rebuild_ns": 4_000_000 + 100_000 * count,
        "semantic_evaluation_ns": 20_000 + 1_000 * count,
        "topology_compile_ns": 300_000 + 10_000 * count,
        "witness_compile_ns": 400_000 + 10_000 * count,
        "native_prove_including_setup_ns":
            round((90_000_000 + 18_000_000 * count) * variation * slowdown),
        "envelope_and_serialization_ns": 100_000 + 10_000 * count,
    }
    stages["package_total_ns"] = sum(stages.values())
    residual = 500_000_000 + index % 7 * 100_000
    prover = stages["package_total_ns"] + residual
    verifier = 400_000_000 + index % 11 * 100_000
    start = 10_000_000_000 + count * 10_000_000_000 + index * 2_000_000_000
    return {
        "schema": "s31-mixed-stage-diagnostic-v1",
        "external_native_verification_accepted": True,
        "source_sha256": sha(f"source:{count}".encode()),
        "assignment_sha256": sha(f"assignment:{count}:{index}".encode()),
        "prover_internal_stages_ns": stages,
        "prover_process_wall_ns": prover,
        "external_verifier_process_wall_ns": verifier,
        "first_verified_process_wall_ns": prover + verifier,
        "proof_bytes": 50_000 + 15_000 * count + index % 5,
        "process_monotonic_ns": {
            "prover_start": start, "prover_end": start + prover,
            "verifier_start": start + prover + 1_000_000,
            "verifier_end": start + prover + 1_000_000 + verifier,
        },
        "engine_setup_preprocessing_ns": None,
        "engine_pow_ns": None,
    }


def synthetic_records(counts: list[int], slowdown: float = 1.0) -> list[dict]:
    return [{"call_count": count, "source_sha256": sha(f"source:{count}".encode()),
             "build_wall_ns": 50_000_000_000 + count * 1_000_000,
             "trials": [synthetic_report(count, i, slowdown=slowdown) for i in range(100)]}
            for count in counts]


class ProspectiveMixedCostTests(unittest.TestCase):
    def test_protocol_anchor_cannot_precede_protocol_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            for key, value in (("user.name", "S31 test"),
                               ("user.email", "s31-test@example.invalid")):
                subprocess.run(["git", "-C", str(root), "config", key, value], check=True)
            freeze = root / "freeze.json"
            freeze.write_text("{}\n")
            subprocess.run(["git", "-C", str(root), "add", "freeze.json"], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-qm", "anchor first"],
                           check=True)
            anchor_commit = subprocess.check_output(
                ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            prospective = root / "protocol.json"
            prospective.write_text("{}\n")
            subprocess.run(["git", "-C", str(root), "add", "protocol.json"], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-qm", "protocol later"],
                           check=True)
            with patch.object(protocol, "ROOT", root), \
                    patch.object(protocol, "PROTOCOL", prospective), \
                    patch.object(protocol, "ANCHOR", freeze):
                with self.assertRaisesRegex(ValueError, "uncommitted mixed cost source"):
                    protocol.check(sha(prospective.read_bytes()), anchor_commit)

    def test_evaluation_requires_committed_heldout_phase_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            with patch.object(anchors, "ROOT", root), patch.object(protocol, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "uncommitted mixed cost source"):
                    anchors.evaluate_heldout(root, {}, "p" * 64, "r" * 64,
                                             "a" * 40, "m" * 40)

    def test_clean_stack_rejects_untracked_compiler_source(self) -> None:
        def fake_git(*args: str, cwd: Path = ROOT) -> str:
            if args[:1] == ("rev-parse",):
                return "a" * 40
            if args[:1] == ("status",) and args[-1:] == ("src",):
                return "?? src/untracked.zig" if "--untracked-files=all" in args else ""
            return ""

        with patch.object(protocol, "design", return_value={"source_template": "source"}), \
                patch.object(protocol, "committed"), \
                patch.object(protocol, "tool_paths", return_value=[]), \
                patch.object(protocol, "git", side_effect=fake_git):
            with self.assertRaisesRegex(ValueError, "uncommitted source files"):
                protocol.clean_stack()

    def test_relative_zig_cache_guard_uses_build_cwd(self) -> None:
        with patch.dict(os.environ, {"ZIG_LOCAL_CACHE_DIR": "temporary-cache"}):
            self.assertEqual(zig_cache_path("ZIG_LOCAL_CACHE_DIR", Path("unused")),
                             ROOT / "temporary-cache")

    def test_report_anchor_rejects_post_audit_edit(self) -> None:
        protocol_sha, inventory_sha, compiler_sha = "p" * 64, "i" * 64, "c" * 64
        engine_commit, model_sha = "e" * 40, "m" * 64
        host = {"host": "test"}
        model = fit_model(synthetic_records([1, 3, 5, 7]), protocol_sha,
                          inventory_sha, host, compiler_sha, engine_commit)
        records = synthetic_records([2, 4, 6, 8])
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "repo"
            out = Path(temporary) / "evidence"
            root.mkdir()
            out.mkdir()
            (out / "raw.marker").write_bytes(b"retained raw phase")
            phase_bytes = canonical(phase_root(out, "heldout", protocol_sha))
            (out / "phase-root.json").write_bytes(phase_bytes)
            phase_sha = sha(phase_bytes)
            corpus = {"schema": "s31-mixed-stage-cost-v1-audited-corpus",
                      "split": "heldout", "protocol_sha256": protocol_sha,
                      "phase_root_sha256": phase_sha, "host": host,
                      "compiler_sha256": compiler_sha,
                      "engine_gitlink_commit": engine_commit,
                      "inventory_sha256": inventory_sha, "records": records}
            (out / "corpus.json").write_bytes(canonical(corpus))
            audit = {"schema": "s31-mixed-stage-cost-v1-audit", "split": "heldout",
                     "phase_root_sha256": phase_sha,
                     "corpus_sha256": sha((out / "corpus.json").read_bytes()),
                     "native_verified_proofs": 400,
                     "changed_input_and_result_rejected": True,
                     "raw_build_and_process_endpoints_replayed": True,
                     "source_assignment_statement_manifest_and_binary_hashes_replayed": True}
            (out / "audit.json").write_bytes(canonical(audit))
            result = evaluate(model, records, protocol_sha256=protocol_sha,
                              inventory_sha256=inventory_sha, host=host,
                              compiler_sha256=compiler_sha,
                              engine_gitlink_commit=engine_commit)
            (out / "evaluation.json").write_bytes(canonical(result))
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            for key, value in (("user.name", "S31 test"),
                               ("user.email", "s31-test@example.invalid")):
                subprocess.run(["git", "-C", str(root), "config", key, value], check=True)
            directory = root / "design/s31/measurements/language"
            directory.mkdir(parents=True)
            timestamp = datetime.now(timezone.utc).isoformat()
            phase_anchor = directory / "mixed-stage-cost-v1-heldout-phase-anchor.json"
            phase_anchor.write_bytes(canonical({
                "schema": "s31-mixed-stage-cost-v1-phase-anchor", "split": "heldout",
                "protocol_sha256": protocol_sha, "phase_root_sha256": phase_sha,
                "recorded_at_utc": timestamp}))
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-qm", "phase anchor"],
                           check=True)
            phase_commit = subprocess.check_output(
                ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            report_anchor = directory / "mixed-stage-cost-v1-heldout-report-anchor.json"
            report_anchor.write_bytes(canonical({
                "schema": "s31-mixed-stage-cost-v1-heldout-report-anchor",
                "split": "heldout", "protocol_sha256": protocol_sha,
                "phase_root_sha256": phase_sha,
                "phase_anchor_commit": phase_commit,
                "model_sha256": model_sha, "model_anchor_commit": phase_commit,
                "audit_sha256": sha((out / "audit.json").read_bytes()),
                "corpus_sha256": sha((out / "corpus.json").read_bytes()),
                "evaluation_sha256": sha((out / "evaluation.json").read_bytes()),
                "recorded_at_utc": timestamp}))
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "commit", "-qm", "report anchor"],
                           check=True)
            report_commit = subprocess.check_output(
                ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            arguments = (out, model, protocol_sha, phase_commit, phase_sha, phase_commit,
                         model_sha, phase_commit, report_commit)
            with patch.object(anchors, "ROOT", root), patch.object(protocol, "ROOT", root):
                self.assertTrue(anchors.check_heldout_report_anchor(*arguments)
                                ["local_accuracy_gate_pass"])
                for name in ("audit", "corpus", "evaluation"):
                    path = out / f"{name}.json"
                    saved = path.read_bytes()
                    path.write_bytes(saved + b" ")
                    with self.assertRaisesRegex(ValueError, "report anchor"):
                        anchors.check_heldout_report_anchor(*arguments)
                    path.write_bytes(saved)

    def test_tool_inventory_covers_transitive_oracle_and_frontend(self) -> None:
        paths = {path.relative_to(ROOT).as_posix()
                 for path in tool_paths()}
        self.assertIn("src/frontends/s31/python/oracle.py", paths)
        self.assertIn("src/frontends/s31/python/abi/binding_v2.py", paths)
        self.assertIn("src/frontends/s31/python/package/context.py", paths)
        self.assertIn("src/frontends/s31/benchmarks/paired_record_v2/diagnose_stages_v1.py", paths)

    def test_cohort_is_distinct_and_deterministic(self) -> None:
        cfg = design()
        rows = inventory(cfg)
        self.assertEqual(set(rows["train"]), {"1", "3", "5", "7"})
        self.assertEqual(set(rows["heldout"]), {"2", "4", "6", "8"})
        self.assertEqual(len({row["source_sha256"] for split in rows.values()
                              for row in split.values()}), 8)
        self.assertEqual(len({digest for split in rows.values() for row in split.values()
                              for digest in row["assignment_sha256"]}), 800)
        source, assignment, statement = case(8, 0, cfg)
        self.assertIn(b'"name":"mixed_stage_cost_v1_n8"', source)
        self.assertEqual(json.loads(statement)["leaves"][0]["words"],
                         next(iter(json.loads(assignment)["public_inputs"].values())))
        self.assertEqual(sha(canonical(rows)),
                         "08725ff480e6bfbd272fb8afe3d415b15d21abe9a62939716ed7e85644a56250")

    def test_design_does_not_admit_native_measurement(self) -> None:
        with self.assertRaisesRegex(ValueError, "full externally recorded"):
            check("0" * 64, "short")

    def test_model_reconstructs_exact_whole_wall_and_has_local_scope(self) -> None:
        train = synthetic_records([1, 3, 5, 7])
        model = fit_model(train, "p" * 64, "i" * 64, {"host": "test"},
                          "c" * 64, "e" * 40)
        result = evaluate(model, synthetic_records([2, 4, 6, 8]),
                          protocol_sha256="p" * 64, inventory_sha256="i" * 64,
                          host={"host": "test"}, compiler_sha256="c" * 64,
                          engine_gitlink_commit="e" * 40)
        self.assertTrue(result["local_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        predicted = predict(model, 8)
        self.assertAlmostEqual(predicted["targets"]["first_verified_process_wall_ns"]["center"],
                               sum(predicted["stages_ns"].values()))
        self.assertFalse(result["programs"][0]["build_accounting"]["build_modelled"])
        self.assertEqual(result["programs"][0]["build_accounting"]
                         ["observed_build_plus_first_verified_median_ns"],
                         result["programs"][0]["build_accounting"]
                         ["observed_package_build_wall_ns"] +
                         result["programs"][0]["targets"]
                         ["first_verified_process_wall_ns"]["measured_median"])

    def test_mutated_raw_wall_and_partition_are_rejected(self) -> None:
        trial = synthetic_report(2, 0)
        components(trial)
        bad = copy.deepcopy(trial)
        bad["prover_process_wall_ns"] += 1
        with self.assertRaisesRegex(ValueError, "raw monotonic"):
            components(bad)
        bad = copy.deepcopy(trial)
        bad["prover_internal_stages_ns"]["native_prove_including_setup_ns"] += 1
        with self.assertRaisesRegex(ValueError, "partition"):
            components(bad)
        bad = copy.deepcopy(trial)
        bad["external_native_verification_accepted"] = False
        with self.assertRaisesRegex(ValueError, "accepted"):
            components(bad)

    def test_training_source_and_assignment_leakage_rejected(self) -> None:
        model = fit_model(synthetic_records([1, 3, 5, 7]), "p" * 64, "i" * 64,
                          {"host": "test"}, "c" * 64, "e" * 40)
        heldout = synthetic_records([2, 4, 6, 8])
        heldout[0]["source_sha256"] = model["training_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "source leaked"):
            evaluate(model, heldout, protocol_sha256="p" * 64,
                     inventory_sha256="i" * 64, host={"host": "test"},
                     compiler_sha256="c" * 64, engine_gitlink_commit="e" * 40)
        heldout = synthetic_records([2, 4, 6, 8])
        heldout[0]["trials"][0]["assignment_sha256"] = \
            model["training_assignment_sha256"][0]
        with self.assertRaisesRegex(ValueError, "assignment leaked"):
            evaluate(model, heldout, protocol_sha256="p" * 64,
                     inventory_sha256="i" * 64, host={"host": "test"},
                     compiler_sha256="c" * 64, engine_gitlink_commit="e" * 40)

    def test_predeclared_gate_fails_on_heldout_slowdown(self) -> None:
        model = fit_model(synthetic_records([1, 3, 5, 7]), "p" * 64, "i" * 64,
                          {"host": "test"}, "c" * 64, "e" * 40)
        result = evaluate(model, synthetic_records([2, 4, 6, 8], slowdown=4),
                          protocol_sha256="p" * 64, inventory_sha256="i" * 64,
                          host={"host": "test"}, compiler_sha256="c" * 64,
                          engine_gitlink_commit="e" * 40)
        self.assertFalse(result["local_accuracy_gate_pass"])
        self.assertGreater(result["accuracy"]["native_opaque_program_median_p90_relative_error"],
                           0.30)

    def test_materialized_case_mutation_and_phase_root(self) -> None:
        cfg = design()
        expected = inventory(cfg)["train"]["1"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "n1"
            materialize(directory, 1, cfg, expected)
            check_materialized(directory, 1, cfg, expected)
            first = phase_root(root, "train", "p" * 64)
            (root / "phase-root.json").write_bytes(canonical(first))
            self.assertEqual(first, phase_root(root, "train", "p" * 64))
            assignment = directory / "assignments/00.json"
            assignment.write_bytes(assignment.read_bytes() + b" ")
            with self.assertRaisesRegex(ValueError, "frozen case changed"):
                check_materialized(directory, 1, cfg, expected)
            self.assertNotEqual(first, phase_root(root, "train", "p" * 64))

    def test_saved_trial_requires_native_replay_and_changed_claim_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            count, index = 1, 0
            source, assignment, typed = case(count, index, design())
            (directory / "assignments").mkdir()
            (directory / "statements").mkdir()
            (directory / "assignments/00.json").write_bytes(assignment)
            (directory / "statements/00.json").write_bytes(typed)
            trial = directory / "trials/00"
            trial.mkdir(parents=True)
            proof = b"proof"
            (trial / "proof.bin").write_bytes(proof)
            (trial / "statement.json").write_bytes(typed)
            registry, circuit = "a" * 64, "b" * 64
            manifest = {"source_sha256": sha(source),
                        "registry_manifest_sha256": registry,
                        "circuit_identity_sha256": circuit}
            (directory / "inspector.stdout").write_bytes(canonical(manifest))
            (directory / "inspector.stderr").write_bytes(b"")
            paths = bins(directory, count)
            paths["verifier"].parent.mkdir(parents=True)
            for name in ("prover", "inspector"):
                paths[name].write_text("#!/bin/sh\nexit 0\n")
            paths["verifier"].write_text(
                "#!/usr/bin/env python3\nimport pathlib,sys\n"
                f"assert pathlib.Path(sys.argv[1]).read_bytes()=={proof!r}\n"
                f"assert pathlib.Path(sys.argv[2]).read_bytes()=={typed!r}\n")
            for path in paths.values():
                path.chmod(0o755)
            stage_report = synthetic_report(count, index)
            stage_report.update({"source_sha256": sha(source),
                                 "registry_manifest_sha256": registry,
                                 "circuit_identity_sha256": circuit,
                                 "binary_sha256": {name: sha(path.read_bytes())
                                                   for name, path in paths.items()},
                                 "assignment_sha256": sha(assignment),
                                 "typed_statement_sha256": sha(typed),
                                 "proof_sha256": sha(proof), "proof_bytes": len(proof)})
            line = {
                "schema": "s31-mixed-general-prover-stages-v1",
                "source_sha256": sha(source),
                "registry_manifest_sha256": registry,
                "circuit_identity_sha256": circuit,
                "proof_bytes": len(proof), "statement_bytes": len(typed),
                "stages_ns": stage_report["prover_internal_stages_ns"],
                "external_native_verification_ns": None,
            }
            for name in ("prover.stdout", "verifier.stdout", "verifier.stderr",
                         "inspector.stderr"):
                (trial / name).write_bytes(b"")
            (trial / "prover.stderr").write_bytes(
                b"S31_MIXED_STAGE_V1 " + canonical(line))
            (trial / "inspector.stdout").write_bytes(canonical(manifest))
            stage_report["raw_log_sha256"] = {
                name: sha((trial / name).read_bytes()) for name in (
                    "prover.stdout", "prover.stderr", "verifier.stdout", "verifier.stderr",
                    "inspector.stdout", "inspector.stderr")}
            (trial / "report.json").write_bytes(canonical(stage_report))
            expected = {"source_sha256": sha(source),
                        "assignment_sha256": [sha(assignment)],
                        "typed_statement_sha256": [sha(typed)]}
            build = {"registry_manifest_sha256": registry,
                     "circuit_identity_sha256": circuit,
                     "binary_sha256": stage_report["binary_sha256"]}
            self.assertEqual(replay_trial(directory, count, index, expected, build,
                                          replay_native=True), stage_report)
            paths["verifier"].write_text("#!/usr/bin/env python3\nraise SystemExit(0)\n")
            with self.assertRaisesRegex(ValueError, "changed public claim accepted"):
                replay_trial(directory, count, index, expected, build, replay_native=True)


if __name__ == "__main__":
    unittest.main()
