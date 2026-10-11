"""Native-free checks for the genuinely new v4 source and claim roster."""

from __future__ import annotations

import unittest

import prospective


class ProspectiveV4Tests(unittest.TestCase):
    def test_new_sources_and_claims_are_disjoint(self) -> None:
        value = prospective.inventory()
        self.assertEqual(value["status"], "design-only-no-native-runner")
        self.assertEqual(list(value["split"]), ["train", "heldout"])
        sources = []
        claims = []
        for group in value["split"].values():
            self.assertEqual(len(group), 4)
            for row in group.values():
                self.assertEqual(len(row["assignment_sha256"]), prospective.CLAIMS)
                self.assertEqual(len(row["statement_sha256"]), prospective.CLAIMS)
                sources.append(row["source_sha256"])
                claims.extend(row["assignment_sha256"] + row["statement_sha256"])
        self.assertEqual(len(set(sources)), 8)
        self.assertEqual(len(set(claims)), 16 * prospective.CLAIMS)
        prior_sources, prior_claims = prospective.prior_hashes()
        self.assertFalse(set(sources) & prior_sources)
        self.assertFalse(set(claims) & prior_claims)

    def test_source_shapes_and_independent_oracle(self) -> None:
        roster = prospective.inventory()["split"]
        for split, programs in prospective.SPLITS.items():
            for shape, count in programs:
                with self.subTest(split=split, shape=shape, count=count):
                    raw, assignment, statement = prospective.case(shape, count, 0)
                    relation = prospective.v3.v2.parse(raw)
                    values = prospective.v3.v2.parse(assignment)
                    self.assertEqual(sum(node["op"] == "repeat" for node in relation["nodes"]),
                                     count)
                    self.assertEqual(len(relation["nodes"]),
                                     roster[split][f"{shape}_n{count}"]["source_nodes"])
                    self.assertEqual(prospective.v3.v2.evaluate_relation(
                        prospective.v3.v2.flat(relation), values),
                        values["public_outputs"])
                    self.assertEqual(len(prospective.v3.v2.parse(statement)["leaves"]), 2)

    def test_out_of_roster_fails(self) -> None:
        with self.assertRaises(ValueError):
            prospective.source("relay", 2)
        with self.assertRaises(ValueError):
            prospective.case("braid", 5, prospective.CLAIMS)
        with self.assertRaises(ValueError):
            prospective.output_words("fork", 6, [1, 2, 3, 4])


if __name__ == "__main__":
    unittest.main()
