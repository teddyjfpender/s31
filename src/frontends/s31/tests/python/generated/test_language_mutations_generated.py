"""Deterministic lexer/parser/elaborator mutations across source features.

This is a robustness gate, not an independent semantic oracle. Valid programs
are checked against independent values in the other generated suites. Here a
single-token mutation must either compile or produce a located source error;
an IndexError, assertion, or unlocated failure is a frontend defect.
"""

from __future__ import annotations

import hashlib
import random
import re
import sys
import unittest
from pathlib import Path


S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from language.builtins import TOKEN_RE
from text_frontend import SourceError, compile_text


SEED = 0x531C0DE
SOURCES = (
    "arithmetic/functional_square4.s31",
    "control/record_choice.s31",
    "arithmetic/curried_sum.s31",
    "arrays/array_views.s31",
    "math/int_u8_checked.s31",
    "arrays/functional_rotate_hash.s31",
    "math/division/record_i32_division.s31",
)
REPLACEMENTS = (
    "", "(", ")", "{", "}", ";", ":", "=", ",", "let", "private",
    "public", "fn", "if", "0", "1_m31", "[m31; 2]", "unknown_value",
    "@", "λ", "9" * 65,
)
MUTATIONS_PER_SOURCE = 40
LOCATED = re.compile(r"^.+:\d+:\d+:")


def token_spans(source: str) -> list[tuple[int, int, str]]:
    """Choose mutation positions at token boundaries, including symbols."""
    result: list[tuple[int, int, str]] = []
    position = 0
    while position < len(source):
        match = TOKEN_RE.match(source, position)
        if match is None:
            raise AssertionError(f"checked-in source has an unknown token at {position}")
        if match.lastgroup not in {"space", "comment"}:
            result.append((match.start(), match.end(), match.group()))
        position = match.end()
    return result


def corpus() -> list[tuple[str, str]]:
    rng = random.Random(SEED)
    mutants: list[tuple[str, str]] = []
    for name in SOURCES:
        source = (S31 / "examples" / name).read_text()
        spans = token_spans(source)
        if not spans:
            raise AssertionError(f"empty source fixture: {name}")
        for trial in range(MUTATIONS_PER_SOURCE):
            start, end, token = rng.choice(spans)
            replacement = rng.choice((*REPLACEMENTS, token * 2))
            mutants.append((f"{name}:{trial}", source[:start] + replacement + source[end:]))
    return mutants


class LanguageMutationTests(unittest.TestCase):
    def test_comments_and_whitespace_preserve_exact_relation(self) -> None:
        """Lexical trivia must not add circuit nodes or change AIR inputs."""
        rng = random.Random(SEED ^ 0xA11)
        for name in SOURCES:
            source = (S31 / "examples" / name).read_text()
            expected, _ = compile_text(source, name)
            positions = [start for start, _, _ in token_spans(source)]
            for trial in range(12):
                insertion = rng.choice(positions)
                trivia = rng.choice(("  \n\t", "\n// s31 formatting probe\n"))
                changed = source[:insertion] + trivia + source[insertion:]
                with self.subTest(name=name, trial=trial):
                    actual, _ = compile_text(changed, f"{name}:trivia:{trial}")
                    self.assertEqual(actual, expected)

    def test_mutated_programs_fail_closed_with_locations(self) -> None:
        mutants = corpus()
        digest = hashlib.sha256()
        accepted = rejected = 0
        for name, source in mutants:
            digest.update(name.encode() + b"\0" + source.encode() + b"\0")
            with self.subTest(name=name):
                try:
                    relation, _ = compile_text(source, name)
                except SourceError as error:
                    self.assertRegex(str(error), LOCATED)
                    rejected += 1
                else:
                    self.assertIn(relation["version"], (1, 2))
                    self.assertIsInstance(relation["nodes"], list)
                    accepted += 1
        # The corpus hash makes edits to examples or mutations reviewable.
        self.assertEqual(digest.hexdigest(),
                         "b0b047879497df24a6c06f06caf6bad91f9e504999d511d91b06293ac84b6256")
        self.assertEqual((accepted, rejected), (9, 271))


if __name__ == "__main__":
    unittest.main()
