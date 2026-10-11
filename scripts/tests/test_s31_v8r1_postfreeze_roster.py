"""Static audit of the post-freeze V8r1 roster-only evaluator repair."""

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "scripts"),
                str(ROOT / "src/frontends/s31/benchmarks"),
                str(ROOT / "src/frontends/s31/benchmarks/cost"),
                str(ROOT / "src/frontends/s31/python")]

import s31_v8r1_postfreeze_roster as repair
import v8r1_protocol
import whole_prover_predictor_v3 as legacy
import whole_prover_predictor_v8r1 as predictor


def digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def synthetic_validation(protocol: dict) -> dict:
    spec = protocol["splits"]["validation"]
    inventory, cases = {}, {}
    for family, sizes in (("arithmetic", spec["arithmetic_rounds"]),
                          ("chip", spec["chip_rounds"]),
                          ("hash", spec["hash_depths"]),
                          ("fixed_width", spec["signed_widths"])):
        for size in sizes:
            kind = spec["signed_128_result"] if size == 128 else "div_rem"
            name = (f"signed_{kind}_{size}" if family == "fixed_width" else
                    f"hash_{size}" if family == "hash" else f"{family}_{size}")
            source = digest(f"synthetic-validation/{name}/source")
            assignments = [digest(f"synthetic-validation/{name}/{i}") for i in range(100)]
            raw = {"blake_g": size} if family == "hash" else {"qm31_ops": size}
            binding = None
            if family == "chip":
                rows = (16, size)
                binding = {
                    "schema": "s31-component-manifest-direct-chip-v2",
                    "chip_call": {"call_id": 0, "rounds": size},
                    "component_geometry": [
                        {"name": component, "trace_log_size": row.bit_length() - 1,
                         "base_trace_columns": 2, "interaction_trace_columns": 1}
                        for component, row in zip(("qm31_ops", "repeated_step_chip"), rows)
                    ],
                    "chip_trace_cells": sum(row * 3 for row in rows),
                    "chip_fri_domain_rows": max(rows),
                    "manifest_precommitment_sha256": digest(name + "/precommit"),
                    "component_manifest_sha256": digest(name + "/manifest"),
                }
            trial = {
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.result[0]",
                "independent_value_oracle": {"status": "passed"},
                "prove_seconds": .08 + size / 100_000,
                "verify_seconds": .02 + size / 100_000,
                "prover_stages": {
                    "witness_seconds": .006, "setup_seconds": .008,
                    "prove_seconds": .032, "prove_excluding_pow_seconds": .02,
                    "interaction_pow_seconds": .005, "fri_pow_seconds": .005,
                    "runtime_other_seconds": .006,
                    "total_through_verification_seconds": .06,
                },
                "proof_bytes": 1000 + size,
                "prover_peak_rss_bytes": 16_000_000 + size * 100,
            }
            cases[name] = {
                "family": family, "source_sha256": source,
                "assignment_sha256": assignments,
                "lowering": protocol["profiles"][family],
                "profile": protocol["profile_by_family"][family],
                "visible_fri": protocol["visible_fri"],
                "package_build": {"package_build_wall_seconds": 1.0,
                                  "package_reused": False},
                "chip_manifest_binding": binding,
                "raw": raw, "padded": raw,
                "preprocessed_cells": max(8, size),
                "trials": [dict(trial) for _ in range(100)],
                "compiler_sha256": "a" * 64,
            }
            inventory[name] = {"family": family,
                               "lowering": protocol["profiles"][family],
                               "source_sha256": source,
                               "assignment_sha256": assignments}
    assert len(cases) == 20
    protocol["inventory"] = {"train": {}, "validation": inventory}
    return {"schema": predictor.CORPUS_SCHEMA, "split": "validation",
            "measurement_tool_sha256": "b" * 64,
            "samples_per_program": 100, "host": {"host": "static-test"},
            "cases": cases}


class PostfreezeRosterTests(unittest.TestCase):
    def test_exact_validation_roster_original_fails_repair_preserves_inputs(self):
        with (patch.object(v8r1_protocol.s31, "compiler_fingerprint", return_value="f" * 64),
              patch.object(v8r1_protocol, "host_identity", return_value={"host": "static-test"}),
              patch.object(v8r1_protocol, "tool_paths", return_value=[])):
            protocol = v8r1_protocol.protocol_template()
        corpus = synthetic_validation(protocol)
        spec = protocol["splits"]["validation"]
        checker = {**protocol, "splits": {**protocol["splits"],
                   "validation": {**spec, "signed_128_output": spec["signed_128_result"]}}}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "protocol.json"
            path.write_text(json.dumps(protocol, sort_keys=True))
            corpus["protocol_sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
            before_corpus, before_checker = copy.deepcopy(corpus), copy.deepcopy(checker)
            kwargs = {"protocol_path": path, "corpus_schema": predictor.CORPUS_SCHEMA}
            with self.assertRaisesRegex(ValueError, "wrong prospective program set"):
                legacy.checked_cases(corpus, "validation", checker, **kwargs)
            records = repair.checked_cases_roster_bridge(
                legacy.checked_cases, corpus, "validation", checker, **kwargs)
            self.assertEqual(len(records), 20)
            self.assertEqual({row["name"] for row in records}, set(corpus["cases"]))
            self.assertTrue(all(row["case"] is corpus["cases"][row["name"]]
                                for row in records))
            self.assertEqual(corpus, before_corpus)
            self.assertEqual(checker, before_checker)
            poisoned = copy.deepcopy(corpus)
            poisoned["cases"]["signed_quotient_8"] = poisoned["cases"].pop("signed_div_rem_8")
            with self.assertRaisesRegex(ValueError, "exact frozen validation inventory"):
                repair.checked_cases_roster_bridge(
                    legacy.checked_cases, poisoned, "validation", checker, **kwargs)

    def test_training_is_unmodified_passthrough(self):
        corpus, protocol = {"split": "train"}, {"splits": {}}
        seen = []
        def original(c, s, p, **kwargs):
            seen.append((c is corpus, s, p is protocol, kwargs))
            return []
        self.assertEqual(repair.checked_cases_roster_bridge(
            original, corpus, "train", protocol, token="unchanged"), [])
        self.assertEqual(seen, [(True, "train", True, {"token": "unchanged"})])


if __name__ == "__main__":
    unittest.main()
