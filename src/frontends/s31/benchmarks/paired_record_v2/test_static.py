"""Static admission checks; native acceptance runs only after exclusive slot release."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from design import ROOT, S31, canonical, case, design, inventory, sha
from integrity import (BUILD_EVENT_SCHEMA, EVENT_SCHEMA, GENESIS,
                       append_event, build_root, phase_root, read_ledger,
                       replay_process)
from protocol import check
from runner import (altered_valid_assignment, build_event_seconds,
                    changed_claim, materialize, paired_summary,
                    replay_build_evidence, require_static_case)


class PairedRecordDesign(unittest.TestCase):
    def test_all_source_assignment_statement_bytes_are_unique_and_balanced(self) -> None:
        cfg = design()
        frozen = inventory(cfg)
        self.assertEqual(set(frozen["train"]), {"1", "2", "4", "6"})
        self.assertEqual(set(frozen["heldout"]), {"3", "5", "7", "8"})
        sources = []
        assignments = []
        statements = []
        for split in frozen.values():
            for count, entry in split.items():
                sources.append(entry["source_sha256"])
                assignments.extend(entry["assignment_sha256"])
                statements.extend(entry["statement_sha256"])
                self.assertEqual(entry["order"].count("generic-first"), 50)
                self.assertEqual(entry["order"].count("mixed-first"), 50)
                self.assertEqual(len(entry["assignment_sha256"]), 100)
                self.assertEqual(len(entry["statement_sha256"]), 100)
        self.assertEqual(len(set(sources)), 8)
        self.assertEqual(len(set(assignments)), 800)
        self.assertEqual(len(set(statements)), 800)

    def test_typed_claims_and_evaluation_are_bound_to_each_pair(self) -> None:
        cfg = design()
        for count in range(1, 9):
            source_bytes, assignment_bytes, typed = case(count, 0, cfg)
            source = json.loads(source_bytes)
            assignment = json.loads(assignment_bytes)
            statement = json.loads(typed)
            self.assertEqual(source["version"], 2)
            self.assertEqual(len([node for node in source["nodes"]
                                  if node["op"] == "repeat"]), count)
            self.assertEqual(statement["leaves"][0]["words"],
                             next(iter(assignment["public_inputs"].values())))
            self.assertEqual(statement["leaves"][1]["words"],
                             next(iter(assignment["public_outputs"].values())))
            self.assertNotEqual(typed, changed_claim(typed, 0))
            self.assertNotEqual(typed, changed_claim(typed, 1))

    def test_altered_public_input_recomputes_valid_output_and_typed_claim(self) -> None:
        cfg = design()
        for count in range(1, 9):
            source_bytes, assignment_bytes, typed = case(count, 0, cfg)
            changed_assignment, changed_typed = altered_valid_assignment(
                assignment_bytes, count, json.loads(source_bytes))
            self.assertNotEqual(changed_assignment, assignment_bytes)
            self.assertNotEqual(changed_typed, typed)
            old = json.loads(assignment_bytes)
            changed = json.loads(changed_assignment)
            self.assertNotEqual(changed["public_inputs"], old["public_inputs"])

    def test_saved_source_witness_or_claim_mutation_fails_static_replay(self) -> None:
        cfg = design()
        expected = inventory(cfg)["train"]["1"]
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "n1"
            materialize(directory, 1, cfg, expected)
            assignment = directory / "assignments/00.json"
            old = assignment.read_bytes()
            assignment.write_bytes(old + b" ")
            with self.assertRaises(ValueError):
                require_static_case(directory, 1, 0, cfg, expected)
            assignment.write_bytes(old)
            statement = directory / "statements/00.json"
            statement.write_bytes(changed_claim(statement.read_bytes(), 0))
            with self.assertRaises(ValueError):
                require_static_case(directory, 1, 0, cfg, expected)

    def test_unfrozen_design_cannot_authorize_native_runner(self) -> None:
        with self.assertRaisesRegex(ValueError, "externally recorded"):
            check("0" * 64, "short")

    def test_summary_uses_paired_assignment_unit(self) -> None:
        cfg = design()
        cfg["assignments_per_call_count"] = 4
        cfg["bootstrap_resamples"] = 100
        rows = []
        for index, ratio in enumerate((2.0, 2.0, 2.0, 2.0)):
            generic = {name: ratio for name in (
                "first_verified_wall_seconds", "prove_wall_seconds",
                "verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes")}
            mixed = {name: 1.0 for name in generic}
            rows.append({"index": index, "generic": generic, "mixed": mixed})
        summary = paired_summary({"split": "heldout", "cases": {"1": rows}}, cfg)
        self.assertEqual(summary["per_call_count"]["1"]["first_verified_wall_seconds"]
                         ["median_ratio_generic_over_mixed"], 2.0)

    def test_phase_root_detects_corpus_cost_and_identity_mutations(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            raw = {"schema": EVENT_SCHEMA, "arm": "generic", "source_sha256": "a" * 64,
                   "start_monotonic_ns": 10, "end_monotonic_ns": 20,
                   "peak_rss_bytes": 4096, "proof_bytes": 64}
            ledger = directory / "phase-ledger.ndjson"
            append_event(ledger, raw, 0, GENESIS)
            row = {"arm": "generic", "source_sha256": "a" * 64,
                   "prove_wall_seconds": 1.0, "prover_peak_rss_bytes": 4096,
                   "proof_bytes": 64}
            corpus = {"cases": {"1": [{"generic": row}]}}
            (directory / "corpus.json").write_bytes(canonical(corpus))
            (directory / "n1").mkdir()
            (directory / "n1/build-times.json").write_bytes(canonical({
                "generic_seconds": 1.0, "mixed_seconds": 2.0}))
            (directory / "n1/package-attestation.json").write_bytes(canonical({
                "source_sha256": "a" * 64}))
            build_ledger = directory / "build-ledger.ndjson"
            previous = GENESIS
            for index, arm in enumerate(("generic", "mixed")):
                previous = append_event(build_ledger, {
                    "schema": BUILD_EVENT_SCHEMA, "arm": arm,
                    "start_monotonic_ns": index * 10,
                    "end_monotonic_ns": index * 10 + 5,
                }, index, previous, event_schema=BUILD_EVENT_SCHEMA)
            (directory / "build-root.json").write_bytes(canonical(build_root(
                directory, "train", "b" * 64, "c" * 40, ["1"])))
            sealed = phase_root(directory, "train", "b" * 64, "c" * 40, 1, ["1"])
            self.assertEqual(len(read_ledger(ledger)[0]), 1)
            for field, changed in (("prove_wall_seconds", 2.0),
                                   ("prover_peak_rss_bytes", 8192),
                                   ("proof_bytes", 65),
                                   ("arm", "mixed"),
                                   ("source_sha256", "d" * 64)):
                altered = {"cases": {"1": [{"generic": {**row, field: changed}}]}}
                (directory / "corpus.json").write_bytes(canonical(altered))
                self.assertNotEqual(phase_root(directory, "train", "b" * 64,
                                                "c" * 40, 1, ["1"]), sealed)
            (directory / "n1/build-times.json").write_bytes(canonical({
                "generic_seconds": 999.0, "mixed_seconds": 2.0}))
            with self.assertRaises(ValueError):
                phase_root(directory, "train", "b" * 64, "c" * 40, 1, ["1"])
            line = ledger.read_text()
            ledger.write_text(line.replace('"arm":"generic"', '"arm":"mixed"'))
            with self.assertRaises(ValueError):
                read_ledger(ledger)

    def test_raw_resource_replay_rejects_rss_or_output_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name, content in (("prover.stdout", b"ok\n"), ("prover.stderr", b""),
                                  ("prover.log", b"ok\n"), ("prover.resource", b"42\n")):
                (directory / name).write_bytes(content)
            observation = {
                "argv": ["/pinned/prover"], "start_monotonic_ns": 100,
                "end_monotonic_ns": 1_000_000_100, "exit_code": 0,
                "rss_method": "gnu-time-max-rss-kib", "raw_resource_text": "42\n",
                "raw_resource_sha256": sha(b"42\n"), "peak_rss_bytes": 42 * 1024,
                "stdout_sha256": sha(b"ok\n"), "stderr_sha256": sha(b""),
                "log_sha256": sha(b"ok\n"),
            }
            self.assertEqual(replay_process(observation, directory, "prover",
                                             ["/pinned/prover"])[0], 1.0)
            with self.assertRaises(ValueError):
                replay_process({**observation, "peak_rss_bytes": 8192}, directory,
                               "prover", ["/pinned/prover"])
            with self.assertRaises(ValueError):
                replay_process(observation, directory, "prover", ["/wrong/prover"])
            (directory / "prover.stdout").write_bytes(b"changed\n")
            with self.assertRaises(ValueError):
                replay_process(observation, directory, "prover", ["/pinned/prover"])

    def test_build_ledger_rederives_times_and_rejects_reanchored_edits(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            directory = out / "n1"
            directory.mkdir()
            source = directory / "source.s31.json"
            source.write_bytes(canonical({"name": "test"}))
            attestation = directory / "package-attestation.json"
            attestation.write_bytes(canonical({"source_sha256": "a" * 64}))
            protocol = {"compiler_sha256": "b" * 64,
                        "engine_gitlink_commit": "c" * 40}
            entries = {"1": {"source_sha256": "a" * 64}}
            common = {"schema": BUILD_EVENT_SCHEMA, "split": "train", "count": 1,
                      "source_sha256": "a" * 64,
                      "compiler_sha256": protocol["compiler_sha256"],
                      "engine_gitlink_commit": protocol["engine_gitlink_commit"],
                      "package_attestation_sha256": sha(attestation.read_bytes()),
                      "outcome": "success"}
            events = [
                {**common, "arm": "generic", "operation": {
                    "api": "s31.build", "source": str(source),
                    "output": str(directory / "generic"), "lowering": "direct-gate"},
                 "start_monotonic_ns": 0, "end_monotonic_ns": 1_000_000_000},
                {**common, "arm": "mixed", "operation": {"argv": [
                    "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
                    "-Doptimize=ReleaseFast", "-Ds31-version=2",
                    "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source}",
                    "-Ds31-name=test", "-j1", "--prefix", str(directory / "mixed"),
                ], "cwd": str(ROOT)},
                 "start_monotonic_ns": 1_000_000_000,
                 "end_monotonic_ns": 3_000_000_000},
            ]
            ledger = out / "build-ledger.ndjson"
            previous = GENESIS
            for index, event in enumerate(events):
                previous = append_event(ledger, event, index, previous,
                                        event_schema=BUILD_EVENT_SCHEMA)
            times = {"schema": "s31-paired-record-v2-build-times-v1",
                     "generic_seconds": 1.0, "mixed_seconds": 2.0}
            (directory / "build-times.json").write_bytes(canonical(times))
            def reseal() -> None:
                (out / "build-root.json").write_bytes(canonical(build_root(
                    out, "train", "d" * 64, "e" * 40, ["1"])))
            reseal()
            replay_build_evidence(out, "train", entries, protocol, "d" * 64, "e" * 40)
            with self.assertRaises(ValueError):
                build_event_seconds({**events[0], "arm": "mixed"}, directory,
                                    "train", 1, "generic", entries["1"], protocol)
            with self.assertRaises(ValueError):
                build_event_seconds({**events[0], "source_sha256": "f" * 64},
                                    directory, "train", 1, "generic", entries["1"], protocol)
            (directory / "build-times.json").write_bytes(canonical({
                **times, "generic_seconds": 7.0}))
            reseal()
            with self.assertRaisesRegex(ValueError, "differ from raw monotonic"):
                replay_build_evidence(out, "train", entries, protocol,
                                      "d" * 64, "e" * 40)


if __name__ == "__main__":
    unittest.main()
