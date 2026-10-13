"""Exercise the independently parsed source fragment across varied effects.

The corpus spans public/private inputs, field constants, subtraction,
aliases, live assertions, and selected non-final outputs.  It checks the
production compiler against a parser that does not import its lexer or
elaborator.  This is differential evidence, not a proof of native AIR rows.
"""

from __future__ import annotations

import copy
import hashlib
import json
import random
import sys
import unittest
from pathlib import Path


S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.source_relation_fragment import (  # noqa: E402
    UnsupportedSourceRelationFragment,
    check_source_relation,
    parse_source_fragment,
)
from text_frontend import compile_text  # noqa: E402


SEED = 31031
CASES = 1000


def canonical(value: dict) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def sources() -> list[str]:
    rng = random.Random(SEED)
    result: list[str] = []
    for case in range(CASES):
        length = rng.choice((1, 2, 3, 4))
        n_inputs = rng.randrange(1, min(4, 8 // length) + 1)
        visibility = [rng.choice(("public", "private")) for _ in range(n_inputs)]
        if (1 + visibility.count("public")) * length > 8:
            continue
        params = ", ".join(
            f"{visibility[index]} x{index}: [m31; {length}]"
            for index in range(n_inputs)
        )
        lines = [f"circuit generated{case}({params}) -> public [m31; {length}] {{"]
        wires = [f"x{index}" for index in range(n_inputs)]
        for step in range(rng.randrange(1, 10)):
            name = f"n{step}"
            left = rng.choice(wires)
            op = rng.choice(("+", "-", ".*"))
            right = (rng.choice(wires) if rng.randrange(2) else
                     f"splat<{length}>({rng.randrange(30)}_m31)")
            lines.append(f"  let {name} = {left} {op} {right};")
            wires.append(name)
            if rng.randrange(5) == 0:
                alias = f"a{step}"
                lines.append(f"  let {alias} = {name};")
                wires.append(alias)
            if rng.randrange(4) == 0:
                lines.append(f"  assert_eq({rng.choice(wires)}, {rng.choice(wires)});")
        lines.append(f"  {rng.choice(wires[n_inputs:])}\n}}")
        result.append("\n".join(lines) + "\n")
    return result


class EffectfulSourceFragmentGenerated(unittest.TestCase):
    def test_independent_relation_matches_compiler(self) -> None:
        admitted = 0
        excluded = 0
        saw: set[str] = set()
        digest = hashlib.sha256()
        for source in sources():
            data = source.encode()
            digest.update(data + b"\0")
            try:
                independent = parse_source_fragment(data)
            except UnsupportedSourceRelationFragment:
                excluded += 1
                continue
            produced, _ = compile_text(source)
            self.assertEqual(independent, produced, source)
            self.assertEqual(check_source_relation(data, canonical(produced))["capability"],
                             "source-to-relation-only")
            admitted += 1
            saw.update(node["op"] for node in independent["nodes"])
            if independent["assertions"]:
                saw.add("assertions")
            if any(item["visibility"] == "private" for item in independent["inputs"]):
                saw.add("private")
        self.assertGreaterEqual(admitted, 900)
        self.assertGreater(excluded, 0)  # deliberately unsupported repeated assertions
        self.assertEqual(saw, {"add", "sub", "mul", "add_const", "mul_const",
                               "assertions", "private"})
        self.assertEqual(digest.hexdigest(), CORPUS_SHA256)

    def test_changed_relation_semantics_are_rejected(self) -> None:
        checked = 0
        for source in sources():
            data = source.encode()
            try:
                relation = parse_source_fragment(data)
            except UnsupportedSourceRelationFragment:
                continue
            changed = copy.deepcopy(relation)
            first = changed["nodes"][0]
            if "constant" in first:
                first["op"] = ("mul_const" if first["op"] == "add_const"
                               else "add_const")
            else:
                first["op"] = "sub" if first["op"] == "add" else "add"
            with self.assertRaisesRegex(ValueError, "normalized relation differs"):
                check_source_relation(data, canonical(changed))
            checked += 1
            if checked == 32:
                break
        self.assertEqual(checked, 32)


# SHA-256 of each generated source followed by NUL in corpus order.
CORPUS_SHA256 = "62b2e089fb7173c1d3f0c531376f865f1c3fd3b236d1f2666ada0bdfc214d791"


if __name__ == "__main__":
    unittest.main()
