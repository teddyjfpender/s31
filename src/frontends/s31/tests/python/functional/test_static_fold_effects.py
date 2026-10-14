"""A static fold cannot hide a partial operation in a dynamic branch."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from text_frontend import SourceError, compile_text


class StaticFoldEffectTests(unittest.TestCase):
    def test_named_partial_step_is_rejected_in_inactive_branch(self) -> None:
        source = """fn risky(acc: [m31; 1], term: [m31; 1]) -> [m31; 1] {
    acc + std::math::inv(term)
}
circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = if flag then std::array::fold(risky, x, [x]) else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_captured_partial_closure_is_rejected_in_inactive_branch(self) -> None:
        source = """circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let risky = fun(acc: [m31; 1], term: [m31; 1]) -> [m31; 1]
        => acc + std::math::inv(term);
    let out = if flag then std::array::fold(risky, x, [x]) else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_higher_order_step_effect_resolves_at_concrete_call(self) -> None:
        source = """fn fold_one(step: Fn([m31; 1], [m31; 1]) -> [m31; 1],
    acc: [m31; 1], term: [m31; 1]) -> [m31; 1] {
    std::array::fold(step, acc, [term])
}
fn risky(acc: [m31; 1], term: [m31; 1]) -> [m31; 1] {
    acc + std::math::inv(term)
}
circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = if flag then fold_one(risky, x, x) else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_eager_array_term_effect_is_not_lost(self) -> None:
        source = """fn add(acc: [m31; 1], term: [m31; 1]) -> [m31; 1] {
    acc + term
}
circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = if flag then std::array::fold(add, x, [std::math::inv(x)]) else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_total_step_remains_available_under_dynamic_condition(self) -> None:
        prelude = """fn add(acc: [m31; 1], term: [m31; 1]) -> [m31; 1] {
    acc + term
}
"""
        body = """circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = if flag then BODY else x;
    out
}"""
        folded, _ = compile_text(prelude + body.replace(
            "BODY", "std::array::fold(add, x, [x])"))
        direct, _ = compile_text(prelude + body.replace("BODY", "add(x, x)"))
        self.assertEqual(folded, direct)


if __name__ == "__main__":
    unittest.main()
