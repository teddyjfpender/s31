"""Fail-closed lexical release checker under a fixed malformed-token corpus."""

from __future__ import annotations

import random
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import UnsupportedFragment, _tokens, parse_source  # noqa: E402
from text_frontend import compile_text  # noqa: E402

SOURCE = S31 / "examples/functional/release_let4/functional.s31"
SEED = 0x5311E7
POOL = ("let", "in", "x", "squared", "result", "square", "+", ".*",
        "(", ")", "=", ";", "0", "4")


class LexicalMutationTests(unittest.TestCase):
    def test_two_thousand_token_mutations_fail_closed_or_agree(self) -> None:
        tokens = _tokens(SOURCE.read_bytes())
        rng = random.Random(SEED)
        accepted = 0
        for case in range(2000):
            changed = tokens.copy()
            for _ in range(1 + rng.randrange(2)):
                choice = rng.randrange(3)
                at = rng.randrange(len(changed))
                if choice == 0:
                    changed[at] = rng.choice(POOL)
                elif choice == 1:
                    changed.pop(at)
                else:
                    changed.insert(at, rng.choice(POOL))
            source = " ".join(changed)
            try:
                checked, _ = parse_source(source.encode())
            except UnsupportedFragment:
                continue
            with self.subTest(case=case):
                self.assertEqual(checked, compile_text(source)[0])
            accepted += 1
        self.assertEqual(accepted, 11)


if __name__ == "__main__":
    unittest.main()
