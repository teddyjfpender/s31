"""Adversarial controls for the S31 formal evidence gate."""
from __future__ import annotations

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import s31_formal
from scripts.s31_formal_lib import checks
from scripts.s31_formal_lib.protocol_order import check_stage_after

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal/s31"


class FormalGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.coverage = json.loads((FORMAL / "coverage.json").read_text())
        self.bindings = json.loads((FORMAL / "source-bindings.json").read_text())
        self.inventory = checks.inventory(ROOT, s31_formal.lean_code)
        self.theorems = set(self.inventory["theorems"])

    def test_comments_and_literals_do_not_create_false_escapes(self) -> None:
        checks.scan_source('/- axiom /- sorry -/ unsafe -/\n-- admit\n'
                           'def s := "native_decide -- /- axiom"\n', "control", s31_formal.lean_code)

    def test_escapes_in_code_are_rejected(self) -> None:
        for token in ("sorry", "admit", "axiom", "unsafe", "native_decide"):
            with self.subTest(token=token), self.assertRaises(checks.FormalError):
                checks.scan_source(f"theorem cheat : True := by {token}\n", "control", s31_formal.lean_code)

    def test_string_comment_markers_cannot_hide_following_escape(self) -> None:
        for literal in ('"--"', '"/-"', '"a\\\"/-b"'):
            with self.subTest(literal=literal), self.assertRaises(checks.FormalError):
                checks.scan_source(f"def s := {literal}; axiom cheat : False\n", "control", s31_formal.lean_code)

    def test_unterminated_comment_is_rejected(self) -> None:
        with self.assertRaises(checks.FormalError):
            checks.scan_source("/- unterminated", "control", s31_formal.lean_code)

    def test_inventory_preserves_question_mark_names_and_excludes_private(self) -> None:
        names = checks.theorem_names("namespace X\nprivate theorem hidden : True := by trivial\n"
                                     "@[simp] theorem ofNat?_toNat : True := by trivial\nend X\n", s31_formal.lean_code)
        self.assertEqual(names, ["X.ofNat?_toNat"])

    def test_public_input_boundary_proof_projections_are_inventoried(self) -> None:
        prefix = "S31.Functional.SSAPublicInputBinding.InputBoundary."
        expected = {prefix + field for field in (
            "basis1", "basis2", "basis3", "copies", "packAdds", "packMuls",
            "pins", "zero",
        )}
        path = "formal/s31/S31/Gadgets/Functional/SSAPublicInputBinding.lean"
        source = (ROOT / path).read_text()
        fields = set()
        in_structure = False
        for line in source.splitlines():
            if line.startswith("structure InputBoundary "):
                in_structure = True
            elif in_structure and not line.strip():
                break
            elif in_structure:
                field = line.split(":", 1)[0].strip()
                if field.isidentifier():
                    fields.add(prefix + field)
        self.assertEqual(fields, expected)
        self.assertEqual(set(checks.proof_field_projection_names(
            source, path, s31_formal.lean_code)), expected)
        self.assertTrue(expected <= self.theorems)

    def test_old_derived_roster_contains_no_proof_field_projections(self) -> None:
        self.assertEqual(sum(map(len, checks.DERIVED_THEOREMS.values())), 2)
        self.assertFalse(any(".InputBoundary." in name or ".ChipRows." in name
                             or ".BridgeRows." in name or ".Parsed.checked" in name
                             or name == "RiscvRefinement.M31.isLt"
                             for names in checks.DERIVED_THEOREMS.values() for name in names))

    def test_reviewed_proof_field_projections_bind_to_source_fields(self) -> None:
        all_names = set()
        for path, structures in checks.PROOF_FIELD_PROJECTIONS_V1.items():
            source = (ROOT / path).read_text()
            expected = {f"{structure}.{field}"
                        for structure, fields in structures.items() for field in fields}
            self.assertEqual(set(checks.proof_field_projection_names(
                source, path, s31_formal.lean_code)), expected)
            self.assertTrue(expected <= self.theorems)
            all_names.update(expected)
            first_structure, first_fields = next(iter(structures.items()))
            first_field = first_fields[0]
            start = source.index(f"structure {first_structure.rsplit('.', 1)[1]}")
            changed = (source[:start] + source[start:].replace(
                f"  {first_field} :", f"  changed_{first_field} :", 1))
            self.assertNotEqual(changed, source)
            with self.subTest(path=path), self.assertRaises(checks.FormalError):
                checks.proof_field_projection_names(changed, path, s31_formal.lean_code)
        self.assertEqual(len(all_names), 94)

    def test_inherited_projections_require_real_extends_clause(self) -> None:
        for path, structures in checks.INHERITED_PROJECTIONS_V1.items():
            source = (ROOT / path).read_text()
            expected = {f"{structure}.{projection}"
                        for structure, (_, projection) in structures.items()}
            self.assertEqual(set(checks.inherited_projection_names(
                source, path, s31_formal.lean_code)), expected)
            self.assertTrue(expected <= self.theorems)
            for structure, (parent, _) in structures.items():
                start = source.index(f"structure {structure.rsplit('.', 1)[1]}")
                changed = source[:start] + source[start:].replace(
                    f"extends {parent}", "extends OtherContext", 1)
                with self.subTest(path=path), self.assertRaisesRegex(
                        checks.FormalError, "stale inherited projection roster"):
                    checks.inherited_projection_names(changed, path, s31_formal.lean_code)

    def test_tagged_public_block_proof_fields_require_live_source(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
        source = (ROOT / path).read_text()
        prefix = "S31.Functional.RecordAbiV2.TaggedPublicBlock."
        expected = {prefix + "bitWidth", prefix + "range"}
        self.assertTrue(expected <= set(checks.proof_field_projection_names(
            source, path, s31_formal.lean_code)))
        self.assertTrue(expected <= self.theorems)
        for field in ("bitWidth", "range"):
            original = f"  {field} :"
            self.assertIn(original, source)
            for replacement in (f"  renamed_{field} :",
                                f"  -- {field} :"):
                changed = source.replace(original, replacement, 1)
                with self.subTest(field=field, replacement=replacement), \
                        self.assertRaisesRegex(checks.FormalError,
                                                "stale proof-field projection roster"):
                    checks.proof_field_projection_names(
                        changed, path, s31_formal.lean_code)

    def test_reused_m31_projection_rejects_renamed_or_commented_field_spoof(self) -> None:
        path = checks.REUSED[0]
        source = (ROOT / path).read_text()
        field = "  isLt : val < m31Modulus\n"
        self.assertEqual(source.count(field), 1)
        for replacement in (
            field.replace("isLt", "renamedIsLt"),
            "  /- retired proof field /- nested -/\n" + field + "  -/\n",
        ):
            changed = source.replace(field, replacement, 1).replace(
                "end RiscvRefinement\n",
                "theorem M31.isLt : True := by trivial\n\n"
                "end RiscvRefinement\n", 1)
            self.assertIn("RiscvRefinement.M31.isLt",
                          checks.theorem_names(changed, s31_formal.lean_code))
            with self.subTest(replacement=replacement), self.assertRaisesRegex(
                    checks.FormalError, "stale proof-field projection roster"):
                checks.proof_field_projection_names(changed, path, s31_formal.lean_code)

    def test_old_input_boundary_projection_rejects_renamed_or_commented_field_spoof(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/SSAPublicInputBinding.lean"
        source = (ROOT / path).read_text()
        field = "  basis1 : wire 15 = unit ⟨1, by decide⟩\n"
        self.assertEqual(source.count(field), 1)
        for replacement in (
            field.replace("basis1", "renamedBasis1"),
            "  /- retired proof field /- nested -/\n" + field + "  -/\n",
        ):
            changed = source.replace(field, replacement, 1).replace(
                "end S31.Functional.SSAPublicInputBinding\n",
                "theorem InputBoundary.basis1 : True := by trivial\n\n"
                "end S31.Functional.SSAPublicInputBinding\n", 1)
            self.assertIn("S31.Functional.SSAPublicInputBinding.InputBoundary.basis1",
                          checks.theorem_names(changed, s31_formal.lean_code))
            with self.subTest(replacement=replacement), self.assertRaisesRegex(
                    checks.FormalError, "stale proof-field projection roster"):
                checks.proof_field_projection_names(changed, path, s31_formal.lean_code)

    def test_commented_proof_field_cannot_be_spoofed_by_named_lemma(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
        source = (ROOT / path).read_text()
        field = "  exactWidth : words.length = width\n"
        self.assertEqual(source.count(field), 1)
        # The old raw-line parser counted this field in a nested block comment.
        # The explicit lemma can carry the same fully qualified audit name, so
        # checking only the live theorem-name set would miss the substitution.
        commented = source.replace(
            field, "  /- outer /- nested -/\n" + field + "  -/\n", 1)
        spoofed = commented.replace(
            "end S31.Functional.RecordAbiV2\n",
            "theorem WordBlock.exactWidth : True := by trivial\n\n"
            "end S31.Functional.RecordAbiV2\n", 1)
        self.assertIn("S31.Functional.RecordAbiV2.WordBlock.exactWidth",
                      checks.theorem_names(spoofed, s31_formal.lean_code))
        with self.assertRaisesRegex(checks.FormalError, "stale proof-field projection roster"):
            checks.proof_field_projection_names(spoofed, path, s31_formal.lean_code)

    def test_line_and_nested_block_comments_do_not_supply_fields(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
        source = (ROOT / path).read_text()
        field = "  exactWidth : words.length = width\n"
        for decoy in (
            "  -- exactWidth : words.length = width\n",
            "  /- outer /- nested -/\n" + field + "  -/\n",
        ):
            changed = source.replace(field, decoy, 1)
            with self.subTest(decoy=decoy), self.assertRaises(checks.FormalError):
                checks.proof_field_projection_names(changed, path, s31_formal.lean_code)

    def test_string_comment_markers_do_not_hide_real_projection(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
        source = (ROOT / path).read_text()
        changed = source.replace("structure WordBlock", 'def marker := "-- /-"\n\nstructure WordBlock', 1)
        self.assertIn("S31.Functional.RecordAbiV2.WordBlock.exactWidth",
                      checks.proof_field_projection_names(
                          changed, path, s31_formal.lean_code))

    def test_same_basename_in_wrong_namespace_cannot_license_projection(self) -> None:
        path = "formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean"
        source = ("namespace Decoy\n"
                  "structure WordBlock where\n"
                  "  exactWidth : Nat\n"
                  "end Decoy\n"
                  "namespace S31.Functional.RecordAbiV2\n"
                  "theorem WordBlock.exactWidth : True := by trivial\n"
                  "end S31.Functional.RecordAbiV2\n")
        with self.assertRaisesRegex(checks.FormalError, "expected one structure WordBlock"):
            checks.proof_field_projection_names(source, path, s31_formal.lean_code)

    def test_unsupported_declaration_style_is_rejected(self) -> None:
        with self.assertRaises(checks.FormalError):
            checks.theorem_names("namespace X\ntheorem «hidden name» : True := by trivial\nend X\n", s31_formal.lean_code)

    def test_full_coverage_is_valid(self) -> None:
        checks.check_coverage(ROOT, self.bindings["ops"], self.coverage, self.theorems)

    def test_rendered_coverage_count_follows_operation_inventory(self) -> None:
        rendered = checks.render_coverage(self.coverage)
        self.assertIn(
            f"operationCoverage.length = {len(self.coverage['operations'])} := rfl",
            rendered,
        )

    def test_missing_added_duplicate_and_reordered_operations_are_rejected(self) -> None:
        for kind in ("missing", "added", "duplicate", "reordered"):
            value = copy.deepcopy(self.coverage)
            entries = value["operations"]
            if kind == "missing":
                entries.pop()
            elif kind == "added":
                extra = copy.deepcopy(entries[-1]); extra["op"] = "new_operation"; entries.append(extra)
            elif kind == "duplicate":
                entries.append(copy.deepcopy(entries[-1]))
            else:
                entries.reverse()
            with self.subTest(kind=kind), self.assertRaises(checks.FormalError):
                checks.check_coverage(ROOT, self.bindings["ops"], value, self.theorems)

    def test_missing_and_unknown_proofs_are_rejected(self) -> None:
        for proofs in ([], ["S31.Gadgets.unproved"]):
            value = copy.deepcopy(self.coverage)
            value["operations"][0]["gadget_theorems"] = proofs
            with self.subTest(proofs=proofs), self.assertRaises(checks.FormalError):
                checks.check_coverage(ROOT, self.bindings["ops"], value, self.theorems)

    def test_missing_source_function_is_rejected(self) -> None:
        value = copy.deepcopy(self.coverage)
        value["operations"][0]["source"]["function"] = "not_a_compiler_function"
        with self.assertRaises(checks.FormalError):
            checks.check_coverage(ROOT, self.bindings["ops"], value, self.theorems)

    def test_unproved_compiler_claim_is_rejected(self) -> None:
        value = copy.deepcopy(self.coverage)
        value["production_compiler_correctness_proved"] = True
        with self.assertRaises(checks.FormalError):
            checks.check_coverage(ROOT, self.bindings["ops"], value, self.theorems)

    def test_empty_audit_is_rejected(self) -> None:
        for expected in (set(), self.theorems):
            with self.subTest(empty=not expected), self.assertRaises(checks.FormalError):
                checks.check_audit("", expected)

    def test_audit_rejects_missing_extra_duplicate_and_unknown_axiom(self) -> None:
        good = "S31_THEOREM S31.example\nS31_AXIOM S31.example propext\n"
        checks.check_audit(good, {"S31.example"})
        for bad in ("", good + "S31_THEOREM S31.extra\n", good + "S31_THEOREM S31.example\n",
                    good + "S31_AXIOM S31.example sorryAx\n", good + "error: failed\n",
                    good + "S31_AXIOM S31.example propext\n"):
            with self.subTest(bad=bad), self.assertRaises(checks.FormalError):
                checks.check_audit(bad, {"S31.example"})

    def test_audit_requires_exact_reviewed_projection_set(self) -> None:
        projected = "S31.Functional.RecordAbiV2.WordBlock.exactWidth"
        expected = {"S31.example", projected}
        good = f"S31_THEOREM S31.example\nS31_THEOREM {projected}\n"
        checks.check_audit(good, expected)
        for bad in ("S31_THEOREM S31.example\n",
                    good + "S31_THEOREM S31.Functional.RecordAbiV2.WordBlock.unreviewed\n",
                    good + f"S31_AXIOM {projected} sorryAx\n"):
            with self.subTest(bad=bad), self.assertRaises(checks.FormalError):
                checks.check_audit(bad, expected)

    def test_kernel_log_rejects_missing_duplicate_and_failed_module(self) -> None:
        files = {"formal/s31/S31.lean": "digest", "formal/s31/S31/Gadgets/Field.lean": "digest"}
        good = "replaying S31\nreplaying S31.Gadgets.Field\n"
        checks.check_kernel_log(good, files)
        for bad in ("", "replaying S31\n", good + "replaying S31\n",
                    good + "leanchecker found a problem in S31\n"):
            with self.subTest(bad=bad), self.assertRaises(checks.FormalError):
                checks.check_kernel_log(bad, files)

    def test_schedule_report_is_fail_closed(self) -> None:
        valid = {"all_valid": True, "checked": 57, "failed": [],
                 "malformed_rejected": 2,
                 "profiles": ["poseidon_pair", *(f"poseidon_leaf_{n}" for n in (4, 8, 12, 16)),
                              "sha256_compression",
                              *(f"blake2s_{n}_{kind}" for n in range(17)
                                for kind in ("plain", "leaf", "pair"))]}
        self.assertEqual(checks.check_schedule_report(json.dumps(valid)), valid)
        for mutation in ("bad JSON", json.dumps({**valid, "all_valid": False}),
                         json.dumps({**valid, "malformed_rejected": 1}),
                         json.dumps({**valid, "profiles": valid["profiles"][:-1]})):
            with self.subTest(mutation=mutation), self.assertRaises(checks.FormalError):
                checks.check_schedule_report(mutation)

    def test_deleted_or_symlinked_source_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in self.inventory["files"]:
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, path)
            path = root / "formal/s31/S31/Evidence/NonVacuity.lean"
            path.unlink()
            with self.assertRaises(checks.FormalError):
                checks.inventory(root, s31_formal.lean_code)
            path.symlink_to(ROOT / "formal/s31/S31/Evidence/NonVacuity.lean")
            with self.assertRaises(checks.FormalError):
                checks.inventory(root, s31_formal.lean_code)

    def test_unimported_new_theorem_cannot_disappear_from_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in self.inventory["files"]:
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, path)
            (root / "formal/s31/S31/Orphan.lean").write_text(
                "namespace S31.Orphan\ntheorem ignored : True := by trivial\nend S31.Orphan\n")
            expected = set(checks.inventory(root, s31_formal.lean_code)["theorems"])
            log = "".join("S31_THEOREM " + name + "\n" for name in self.theorems)
            with self.assertRaises(checks.FormalError):
                checks.check_audit(log, expected)

    def test_source_drift_changes_generated_bindings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in s31_formal.BINDINGS + ["formal/s31/coverage.json"]:
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, path)
            with patch.object(s31_formal, "ROOT", root), \
                    patch.object(s31_formal, "FORMAL", root / "formal/s31"), \
                    patch.object(s31_formal, "generated_native_square4_topology",
                                 return_value=(FORMAL / "S31/Gadgets/Functional/TextSquare4Native.lean").read_text()):
                before = s31_formal.generated()[root / "formal/s31/source-bindings.json"]
                source = root / s31_formal.RELATION
                source.write_text(source.read_text() + "\n// changed source identity\n")
                after = s31_formal.generated()[root / "formal/s31/source-bindings.json"]
                self.assertNotEqual(before, after)

    def test_functional_specializer_drift_changes_generated_bindings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in s31_formal.BINDINGS + ["formal/s31/coverage.json"]:
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, path)
            with patch.object(s31_formal, "ROOT", root), \
                    patch.object(s31_formal, "FORMAL", root / "formal/s31"), \
                    patch.object(s31_formal, "generated_native_square4_topology",
                                 return_value=(FORMAL / "S31/Gadgets/Functional/TextSquare4Native.lean").read_text()):
                before = s31_formal.generated()[root / "formal/s31/source-bindings.json"]
                source = root / "src/frontends/s31/python/language/specialize.py"
                source.write_text(source.read_text() + "\n# changed specialization identity\n")
                after = s31_formal.generated()[root / "formal/s31/source-bindings.json"]
                self.assertNotEqual(before, after)

    def test_text_square4_compiler_binding_changes_with_source(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for relative in (s31_formal.RELATION, s31_formal.TEXT_SQUARE4):
                target = root / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, target)
            with patch.object(s31_formal, "ROOT", root):
                before = s31_formal.generated_text_square4()
                source = root / s31_formal.TEXT_SQUARE4
                source.write_text(source.read_text().replace("v .* v", "v + v", 1))
                after = s31_formal.generated_text_square4()
                self.assertNotEqual(before, after)

    def test_native_logup_caller_order_mutation_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            relative = s31_formal.QM31_EVALUATOR
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            source = (ROOT / relative).read_text()
            target.write_text(source)
            evaluator = Path("src/frontends/circuit/stark_verifier/constraint_eval.zig")
            (root / evaluator).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / evaluator, root / evaluator)
            with patch.object(s31_formal, "ROOT", root):
                s31_formal.check_native_qm31_relation_schedule()
                target.write_text(source.replace(
                    "ctx.one(), &.{ relation, op0_addr, cols[0]",
                    "ctx.one(), &.{ relation, op1_addr, cols[0]", 1))
                with self.assertRaises(checks.FormalError):
                    s31_formal.check_native_qm31_relation_schedule()
                target.write_text(source.replace(
                    "inline for (qm31_ops_constraints) |constraint|",
                    "inline for (qm31_ops_constraints[1..]) |constraint|", 1))
                with self.assertRaises(checks.FormalError):
                    s31_formal.check_native_qm31_relation_schedule()

    def test_native_eq_logup_caller_mutation_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            relative = s31_formal.QM31_EVALUATOR
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            source = (ROOT / relative).read_text()
            target.write_text(source)
            with patch.object(s31_formal, "ROOT", root):
                s31_formal.check_native_eq_relation_schedule()
                target.write_text(source.replace(
                    "ctx.one(), &.{ relation, in1_address, cols[0]",
                    "ctx.one(), &.{ relation, in0_address, cols[0]", 1))
                with self.assertRaises(checks.FormalError):
                    s31_formal.check_native_eq_relation_schedule()

    def test_composition_draw_before_interaction_commit_is_rejected(self) -> None:
        check_stage_after("commit draw", before="commit", after="draw",
                          count=1, label="control")
        with self.assertRaises(ValueError):
            check_stage_after("draw commit", before="commit", after="draw",
                              count=1, label="control")


if __name__ == "__main__":
    unittest.main()
