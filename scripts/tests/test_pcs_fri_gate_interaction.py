"""P02 gate relation-use and native claim-closure controls."""

import json
import tempfile
import unittest
from pathlib import Path

from scripts.release.pcs_fri_gate_interaction import (
    NATIVE_SOURCES, check_sources, derive_budget, verify_claim_mutation,
)

ROOT = Path(__file__).resolve().parents[2]
ROSTER = ROOT / "src/frontends/s31/tests/python/security/fixtures/effects_gate_ownership/gate-component-roster.json"
LIVE_PACKAGE = Path("/private/tmp/s31-effects-admission-smoke-package-final")
LIVE_PROOF = Path("/private/tmp/s31-effects-admission-smoke.proof")
LIVE_STATEMENT = Path("/private/tmp/s31-effects-admission-smoke.proof.statement.json")


def fixture():
    roster = json.loads(ROSTER.read_text())
    geometry = {"components": [
        {"name": row["name"], "trace_log_size": row["trace_log_size"]}
        for row in roster["components"]]}
    return roster, geometry


class GateInteractionTests(unittest.TestCase):
    def test_exact_relation_use_budget(self):
        roster, geometry = fixture()
        bounds = {row["relation"]: row for row in derive_budget(roster, geometry)}
        self.assertEqual(len(bounds), 8)
        self.assertEqual(bounds["Gate"]["exact_uses"], 1216)
        self.assertEqual(bounds["Gate"]["native_shifted_bound"], 14)
        self.assertTrue(all(row["canonical_m31_use_count"] for row in bounds.values()))

    def test_resealed_relation_or_shape_is_rejected(self):
        for field, value in (("uses", 3), ("relation_id", "RangeCheck_16")):
            roster, geometry = fixture()
            roster["components"][1]["lookup_uses_per_row"][0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "reviewed AIR"):
                derive_budget(roster, geometry)
        roster, geometry = fixture()
        roster["components"][6]["trace_log_size"] = 19
        geometry["components"][6]["trace_log_size"] = 19
        with self.assertRaisesRegex(ValueError, "reviewed AIR"):
            derive_budget(roster, geometry)

    def test_native_shifted_overflow_is_rejected(self):
        roster, geometry = fixture()
        roster["components"][1]["trace_log_size"] = 30
        geometry["components"][1]["trace_log_size"] = 30
        with self.assertRaisesRegex(ValueError, "exceeds M31"):
            derive_budget(roster, geometry)

    @unittest.skipUnless(all((ROOT / name).is_file() for name in NATIVE_SOURCES),
                         "pinned native engine not checked out")
    def test_native_source_change_is_rejected(self):
        digests = check_sources(ROOT)
        self.assertEqual(digests, NATIVE_SOURCES)
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            for name in NATIVE_SOURCES:
                target = scratch / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((ROOT / name).read_bytes())
            changed = scratch / next(iter(NATIVE_SOURCES))
            changed.write_bytes(changed.read_bytes() + b"\n// altered")
            with self.assertRaisesRegex(ValueError, "source changed"):
                check_sources(scratch)

    @unittest.skipUnless(LIVE_PACKAGE.is_dir() and LIVE_PROOF.is_file() and
                         LIVE_STATEMENT.is_file(), "local sealed gate proof unavailable")
    def test_native_claim_mutation_is_rejected(self):
        result = verify_claim_mutation(LIVE_PACKAGE, LIVE_PROOF, LIVE_STATEMENT)
        self.assertEqual(result["original_proof"], "accepted")
        self.assertEqual(result["changed_claims"], "rejected_InvalidLookupSum")
        self.assertEqual(result["claimed_sum_slots_mutated"], 11)


if __name__ == "__main__":
    unittest.main()
