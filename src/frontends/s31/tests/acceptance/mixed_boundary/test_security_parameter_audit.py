"""Fast mutation controls for the source-pinned mixed security diagnostic."""

from __future__ import annotations

import unittest

import security_parameter_audit as audit


ROOT = audit._default_root()
PREFLIGHT = "deps/stwo-zig/src/integrations/circuit_cpu/direct_many_preflight.zig"
LOGUP = "deps/stwo-zig/src/prover/air/logup_columns.zig"
MIXED = "deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig"
PCS_VERIFIER = "deps/stwo-zig/src/core/pcs/verifier.zig"
QUERIES = "deps/stwo-zig/src/core/queries.zig"


def changed(path: str, before: str, after: str) -> dict[str, bytes]:
    source = (ROOT / path).read_text()
    if source.count(before) != 1:
        raise AssertionError(f"mutation anchor count is {source.count(before)}: {path}")
    return {path: source.replace(before, after, 1).encode()}


class SecurityParameterAuditTests(unittest.TestCase):
    def test_pinned_profile_reports_only_conditional_lookup(self) -> None:
        report = audit.audit(ROOT)
        self.assertEqual(report["lookup"]["conditional_numerator"], 5_055_289)
        self.assertEqual(report["lookup"]["event_occurrences_max"], 722_185)
        self.assertEqual(report["fri"]["n_queries_raw"], 70)
        self.assertIsNone(report["whole_proof_security_bits"])
        self.assertIn("FRI/PCS", report["unbounded_terms"])

    def test_changed_pcs_pow_bits_refused(self) -> None:
        overrides = changed(PREFLIGHT, "FriConfigV2.init(26, 0, 1, 70, 1)",
                            "FriConfigV2.init(25, 0, 1, 70, 1)")
        with self.assertRaisesRegex(audit.AuditError, "PCS_CONFIG"):
            audit.audit(ROOT, overrides)

    def test_changed_query_count_refused(self) -> None:
        overrides = changed(PREFLIGHT, "FriConfigV2.init(26, 0, 1, 70, 1)",
                            "FriConfigV2.init(26, 0, 1, 69, 1)")
        with self.assertRaisesRegex(audit.AuditError, "PCS_CONFIG"):
            audit.audit(ROOT, overrides)

    def test_removed_zero_denominator_rejection_refused(self) -> None:
        overrides = changed(LOGUP,
                            "if (fraction.denominator.isZero()) return error.DegenerateDenominator;",
                            "if (fraction.denominator.isZero()) {}")
        with self.assertRaisesRegex(audit.AuditError, "DENOMINATOR_POLICY"):
            audit.audit(ROOT, overrides)

    def test_lookup_draw_before_nonce_mix_refused(self) -> None:
        before = ("channel.mixU64(proof.interaction_pow_nonce);\n"
                  "    try order.accept(.interaction_pow_nonce);\n"
                  "    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);")
        after = ("const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);\n"
                 "    channel.mixU64(proof.interaction_pow_nonce);\n"
                 "    try order.accept(.interaction_pow_nonce);")
        overrides = changed(MIXED, before, after)
        with self.assertRaisesRegex(audit.AuditError, "ORDER_VERIFY"):
            audit.audit(ROOT, overrides)

    def test_fri_query_before_pow_mix_refused(self) -> None:
        before = ("channel.mixU64(proof.proof_of_work);\n\n"
                  "            var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(\n"
                  "                allocator,\n"
                  "                channel,\n"
                  "            );")
        after = ("var query_capture = try fri_verifier.sampleQueryPositionsWithRaw(\n"
                 "                allocator,\n"
                 "                channel,\n"
                 "            );\n"
                 "            channel.mixU64(proof.proof_of_work);")
        overrides = changed(PCS_VERIFIER, before, after)
        with self.assertRaisesRegex(audit.AuditError, "ORDER_FRI_QUERY"):
            audit.audit(ROOT, overrides)

    def test_other_source_change_requires_review(self) -> None:
        source = (ROOT / QUERIES).read_bytes()
        with self.assertRaisesRegex(audit.AuditError, "SOURCE_DIGEST"):
            audit.audit(ROOT, {QUERIES: source + b"\n"})


if __name__ == "__main__":
    unittest.main()
