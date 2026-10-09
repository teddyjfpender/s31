"""Every shipped text program must still lower to its reviewed relation."""

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from text_frontend import compile_file


def structural_relation(relation: dict) -> dict:
    """Compare operation edges while ignoring handwritten node names."""
    names = {item["name"]: f"input{index}" for index, item in enumerate(relation["inputs"])}
    nodes = []
    for index, node in enumerate(relation["nodes"]):
        nodes.append({key: names[value] if key in {"lhs", "rhs", "selector"} else value
                      for key, value in node.items() if key != "name"})
        names[node["name"]] = f"node{index}"
    return {
        "inputs": [{key: value for key, value in item.items() if key != "name"}
                   for item in relation["inputs"]],
        "nodes": nodes,
        "assertions": [{key: names[value] for key, value in item.items()}
                       for item in relation["assertions"]],
        "public_outputs": [names[name] for name in relation["public_outputs"]],
    }


class ExampleRelationTests(unittest.TestCase):
    def test_all_sources_compile_and_reviewed_relations_match(self) -> None:
        sources = sorted((S31 / "examples").rglob("*.s31"))
        self.assertTrue(sources)
        reviewed = 0
        for path in sources:
            with self.subTest(source=str(path.relative_to(S31))):
                compiled, _ = compile_file(path)
                reference = path.with_suffix(".s31.json")
                if reference.exists():
                    reviewed += 1
                    self.assertEqual(structural_relation(compiled),
                                     structural_relation(json.loads(reference.read_text())))
        self.assertGreater(reviewed, 0)


if __name__ == "__main__":
    unittest.main()
