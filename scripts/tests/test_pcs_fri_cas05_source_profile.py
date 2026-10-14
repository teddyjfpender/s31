"""Hostile source-pin and boundary checks for the experimental P05 audit."""

from __future__ import annotations

import hashlib
import unittest
from fractions import Fraction

from scripts.release.pcs_fri_cas05_source_profile import (
    Q, check_fixed_source_custody, conditional_ood_support,
    profile_geometry, verify_hashes,
)


THETA = Fraction(16383, 65536)


def _zig_body(signature: str, *lines: str) -> str:
    body = "\n".join(lines)
    # Keep the small mutation fixture's braces balanced. It is a source-guard
    # test input; the whole draft source is independently pinned by SHA-256.
    return f"{signature} {{\n{body}\n" + "}" * (1 + body.count("{") - body.count("}"))


def _custody_fixture() -> dict[str, str]:
    return {
        "src/core/pcs/paired_sparse_cascade_experimental.zig": "\n".join((
            _zig_body("fn matches(",
                "statement.profile, proof.profile",
                "statement.source_root, &proof.source_root",
                "statement.claims.len != proof.claims.len",
                "for (statement.claims, proof.claims) {",
                "if (!expected.eql(actual)) return false;"),
            _zig_body("pub fn drawBatchAfterOod(",
                "staged.mixU64(CLAIM_GROUP_TAG);",
                "for (claims, 0..) |height, index| {",
                "staged.mixU64(CLAIM_HEIGHT_TAG);",
                "staged.mixFelts(height);",
                "const batch = staged.drawSecureFelt();",
                "channel.* = staged;"),
            _zig_body("pub fn verifyAgainstStatement(",
                "try validateProof(proof);",
                "if (!matches(statement, proof)) return error.UnexpectedSparseStatement;",
                "const batch = try drawBatchAfterOod(&staged, proof.claims);",
                "var opened = try xdm.verifyAndCollect(",
                "var answers = try paired.fromVerifiedOpenings(",
                "try verifyFolds(allocator, proof, raw, answers.values, alphas);",
                "channel.* = staged;"),
        )),
        "src/core/pcs/transposed_merkle_sparse.zig": _zig_body(
            "pub fn verifyAndCollect(",
            "if (!std.mem.eql(u8, &header.root, &expected_root)) return error.UnexpectedSparseRoot;",
            "for (values[height][offset..][0..cols]) |*value| value.* = try c.felt();",
            "return error.DuplicateProjectedValue;",
            "tree.hashLeaf(values[0][offset..][0..cols])",
            "const left = try childHash(",
            "tree.hashInserted(left, right, values[height][offset..][0..cols])",
            "tree.hashUpper(left, right)",
            "if (used != count) return error.WitnessTooLong;",
            "if (!std.mem.eql(u8, &root, &expected_root)) return error.RootMismatch;",
            "return .{ .allocator = allocator, .profile = expected, .values = values };"),
        "src/core/pcs/transposed_merkle.zig": "\n".join((
            _zig_body("pub fn children(",
                "if (level == 0) return .{ 0, 1 };",
                "const first = (index & 1) | ((index >> 1) << 2);",
                "return .{ first, first | 2 };"),
            _zig_body("pub fn parent(",
                "if (level == 1) return 0;",
                "return (index & 1) | ((index >> 2) << 1);"),
            _zig_body("pub fn sibling(",
                "return index ^ (if (level == 1) @as(usize, 1) else @as(usize, 2));"),
        )),
        "src/core/pcs/transposed_merkle_cascade.zig": "\n".join((
            _zig_body("pub fn hashLeaf(",
                'h.update("S31XDL03");', "hashValues(&h, values);",
                "return h.finalize();"),
            _zig_body("pub fn hashUpper(",
                'h.update("S31XDU03");', "h.update(&left);",
                "h.update(&right);", "return h.finalize();"),
            _zig_body("pub fn hashInserted(",
                "const pair = hashUpper(left, right);", 'h.update("S31XDI03");',
                "h.update(&pair);", "hashValues(&h, values);",
                "return h.finalize();"),
        )),
        "src/prover/pcs/transposed_cascade_experimental.zig": _zig_body(
            "fn commitImpl(",
            "for (layers[k], 0..) |*leaf, row|",
            "leaf.* = xdm.hashLeaf(values[0..source_columns[0].len]);",
            "const pair = topology.children(level, row);",
            "if (height < source_columns.len) {",
            "node.* = xdm.hashInserted(left, right, values[0..source_columns[height].len]);",
            "node.* = xdm.hashUpper(left, right);"),
        "src/core/pcs/transposed_paired_sparse.zig": _zig_body(
            "pub fn fromVerifiedOpenings(",
            "if (raw_queries.len != profile.query_count or claims.len != profile.height_count)",
            "if (height_claims.len != profile.columns[height]) return error.InvalidSparseShape;",
            "coefficient.* = try constraints.complexConjugateLineCoeffs(point, claim, QM31.one());",
            "const original = opened.at(height, query, j, col);",
            "const quotient = numerator.mulCM31(inverse);",
            "answer = answer.add(pair[0].mul(QM31.fromBase(original)))",
            "values[height][query * 2 + j] = answer;"),
        "src/core/pcs/paired_sparse_relation_experimental.zig": _zig_body(
            "pub fn verifyAndExtract(",
            "try cascade.verifyAgainstStatement(a, proof, &staged, statement);",
            "const opened = try xdm.verifyAndCollect(",
            "try relation.check(a);",
            "channel.* = staged;"),
    }


class Cas05SourceProfileTests(unittest.TestCase):
    def test_fixed_source_custody_rejects_hostile_rewiring(self) -> None:
        source = _custody_fixture()
        check_fixed_source_custody(source)
        edits = (
            ("src/core/pcs/paired_sparse_cascade_experimental.zig",
             "if (!expected.eql(actual)) return false;",
             "if (!expected.eql(actual)) return true;"),
            ("src/core/pcs/paired_sparse_cascade_experimental.zig",
             "staged.mixFelts(height);",
             "// staged.mixFelts(height);"),
            ("src/core/pcs/paired_sparse_cascade_experimental.zig",
             "if (!matches(statement, proof)) return error.UnexpectedSparseStatement;",
             "if (matches(statement, proof)) return error.UnexpectedSparseStatement;"),
            ("src/core/pcs/transposed_merkle_sparse.zig",
             "return error.DuplicateProjectedValue;",
             "return error.InvalidSparseProjection;"),
            ("src/core/pcs/transposed_merkle_sparse.zig",
             "if (!std.mem.eql(u8, &root, &expected_root)) return error.RootMismatch;",
             "// root check removed"),
            ("src/core/pcs/transposed_merkle.zig",
             "@as(usize, 1) else @as(usize, 2)",
             "@as(usize, 1) else @as(usize, 1)"),
            ("src/core/pcs/transposed_merkle.zig",
             "((index >> 2) << 1)",
             "((index >> 1) << 1)"),
            ("src/core/pcs/transposed_merkle_cascade.zig",
             'h.update("S31XDI03");',
             'h.update("S31XDU03");'),
            ("src/prover/pcs/transposed_cascade_experimental.zig",
             "node.* = xdm.hashInserted(left, right, values[0..source_columns[height].len]);",
             "node.* = xdm.hashUpper(left, right);"),
            ("src/core/pcs/transposed_paired_sparse.zig",
             "const original = opened.at(height, query, j, col);",
             "const original = untrusted.at(height, query, j, col);"),
            ("src/core/pcs/paired_sparse_relation_experimental.zig",
             "try relation.check(a);",
             "// relation.check(a) removed"),
        )
        for path, old, new in edits:
            with self.subTest(path=path, old=old):
                changed = dict(source)
                changed[path] = changed[path].replace(old, new)
                with self.assertRaisesRegex(ValueError, "custody"):
                    check_fixed_source_custody(changed)

        changed = dict(source)
        path = "src/core/pcs/paired_sparse_cascade_experimental.zig"
        changed[path] = changed[path].replace(
            "staged.mixFelts(height);\nconst batch = staged.drawSecureFelt();",
            "const batch = staged.drawSecureFelt();\nstaged.mixFelts(height);")
        with self.assertRaisesRegex(ValueError, "reordered"):
            check_fixed_source_custody(changed)

    def test_source_pin_rejects_changed_bytes_and_roster(self) -> None:
        sources = {"verifier.zig": b"source-v1", "prover.zig": b"source-v1"}
        expected = {name: hashlib.sha256(data).hexdigest()
                    for name, data in sources.items()}
        self.assertEqual(verify_hashes(sources, expected), expected)
        with self.assertRaisesRegex(ValueError, "source changed"):
            verify_hashes({**sources, "verifier.zig": b"source-v2"}, expected)
        with self.assertRaisesRegex(ValueError, "roster changed"):
            verify_hashes({"verifier.zig": b"source-v1"}, expected)

    def test_sparse_verifier_legacy_and_cas05_host_caps_are_distinct(self) -> None:
        wide = profile_geometry(22, 8, 1, 232, (1,) * 8, THETA)
        self.assertTrue(wide["native_sparse_verifier_visible_caps_pass"])
        self.assertFalse(wide["legacy_xdm03_dense_host_visible_caps_pass"])
        self.assertFalse(wide["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertGreater(wide["native_cas05_host_preflight_estimate_bytes"],
                           wide["native_cas05_host_preflight_budget_bytes"])
        self.assertEqual(wide["terminal_domain_rows"], 1 << 14)
        self.assertEqual(wide["terminal_qm31_coefficient_words"], 1 << 13)
        self.assertEqual(wide["paper_protocol3_indices_if_refined"],
                         {"n": 21, "r": 7})
        self.assertEqual(wide["candidate_N_if_D0_equals_N_times_B_squared"],
                         1 << 20)
        self.assertEqual(wide["minimum_idealized_BCS_round_count"], 13)
        self.assertIsNone(wide["native_BCS_round_count_R"])
        self.assertTrue(wide["candidate_theta_in_strict_unique_decoding_interval"])
        self.assertTrue(wide["published_single_point_small_table_numeric_all_pass"])
        self.assertFalse(wide["cas05_two_point_uniqueness_threshold_derived"])
        self.assertFalse(wide["derived_batch_oracle_substitution_proved"])
        self.assertFalse(wide["native_profile_or_theorem_admitted"])

        host = profile_geometry(16, 8, 1, 232, (1,) * 8, THETA)
        self.assertTrue(host["legacy_xdm03_dense_host_visible_caps_pass"])
        self.assertTrue(host["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertEqual(host["terminal_qm31_coefficient_words"], 128)
        # This crosses only the legacy XDM03 full-fiber cap.
        exceeded = profile_geometry(16, 8, 1, 257, (1,) * 8, THETA)
        self.assertFalse(exceeded["legacy_xdm03_dense_host_visible_caps_pass"])
        self.assertTrue(exceeded["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertTrue(exceeded["native_sparse_verifier_visible_caps_pass"])

        # The native k=17,H=2 fixture from stwo-zig #264 is accepted by
        # CAS05's preflight but remains outside legacy XDM03.
        k17 = profile_geometry(17, 2, 1, 3, (1, 1), THETA)
        self.assertFalse(k17["legacy_xdm03_dense_host_visible_caps_pass"])
        self.assertTrue(k17["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertEqual(k17["native_cas05_host_merkle_tree_bytes"],
                         ((1 << 18) - 1) * 32)
        self.assertEqual(k17["native_cas05_host_logical_borrowed_source_bytes"],
                         ((1 << 17) + (1 << 16)) * 4)
        self.assertEqual(k17["native_cas05_host_preflight_estimate_bytes"], 9175008)
        self.assertEqual(k17["native_cas05_host_preflight_budget_bytes"],
                         192 * 1024 * 1024)
        self.assertFalse(k17["native_profile_or_theorem_admitted"])

        k21 = profile_geometry(21, 8, 1, 232, (1,) * 8, THETA)
        self.assertTrue(k21["native_cas05_bounded_sparse_host_visible_caps_pass"])
        k22_narrow = profile_geometry(22, 2, 1, 3, (1, 1), THETA)
        self.assertTrue(k22_narrow["native_sparse_verifier_visible_caps_pass"])
        self.assertFalse(k22_narrow["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertGreater(k22_narrow["native_cas05_host_merkle_tree_bytes"],
                           k22_narrow["native_cas05_host_preflight_budget_bytes"])

    def test_sparse_wire_and_theorem_conditions_are_distinct(self) -> None:
        too_wide = profile_geometry(22, 8, 1, 1 << 14, (64,) * 8, THETA)
        self.assertFalse(too_wide["native_sparse_verifier_visible_caps_pass"])
        self.assertFalse(too_wide["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertTrue(too_wide["published_single_point_small_table_numeric_all_pass"])
        # A large theta can violate the paper condition even for a native
        # shape that satisfies the visible source caps.
        bad_theta = profile_geometry(16, 8, 1, 1, (1,) * 8,
                                     Fraction(999, 1000))
        self.assertTrue(bad_theta["legacy_xdm03_dense_host_visible_caps_pass"])
        self.assertTrue(bad_theta["native_cas05_bounded_sparse_host_visible_caps_pass"])
        self.assertFalse(bad_theta["candidate_theta_in_strict_unique_decoding_interval"])
        self.assertFalse(bad_theta["published_single_point_small_table_numeric_all_pass"])
        self.assertFalse(bad_theta["native_profile_or_theorem_admitted"])

    def test_two_point_ood_universe_is_not_single_point_universe(self) -> None:
        support = conditional_ood_support()
        self.assertEqual(support["published_protocol4_single_point_support"],
                         Q**4 - Q - 2)
        self.assertEqual(support["section_4_5_two_point_candidate_support"],
                         Q**4 - Q**2)
        self.assertEqual(support["native_guarded_seed_image_if_uniform"],
                         (Q**2 - 1)**2)
        self.assertEqual(support["two_point_minus_guarded"], Q**2 - 1)
        self.assertEqual(Fraction(support["two_point_to_guarded_ratio"]),
                         Fraction(Q**2, Q**2 - 1))
        self.assertNotEqual(support["published_protocol4_single_point_support"],
                            support["section_4_5_two_point_candidate_support"])
        self.assertFalse(support["two_point_bad_set_bound_or_adaptive_sampler_proved"])

    def test_rejects_malformed_profiles_without_allocation(self) -> None:
        for args in (
            (22, 8, 0, 232, (1,) * 8, THETA),
            (22, 8, 1, 0, (1,) * 8, THETA),
            (22, 8, 1, 232, (1,) * 7, THETA),
            (22, 9, 1, 232, (1,) * 9, THETA),
            (22, 8, 15, 232, (1,) * 8, THETA),
            (22, 8, 1, 232, (0,) + (1,) * 7, THETA),
            (22, 8, 1, 232, (1,) * 8, Fraction(1)),
        ):
            with self.subTest(args=args), self.assertRaises(ValueError):
                profile_geometry(*args)


if __name__ == "__main__":
    unittest.main()
