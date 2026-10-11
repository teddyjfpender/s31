"""Native-free checks of the paired source, ABI, and prospective schedule."""

import json
import unittest

import design
import protocol
import study
from abi.binding_v2 import statement_from_assignment


class PairedDesignTest(unittest.TestCase):
    def test_oracle_and_typed_mutation(self) -> None:
        for case in protocol.CASES:
            _, calls, rounds = design.spec(case)
            raw_source = design.source(case)
            source = json.loads(raw_source)
            self.assertEqual(source["version"], 2)
            self.assertEqual(len([node for node in source["nodes"]
                                  if node["op"] == "repeat"]), calls)
            self.assertEqual({node["rounds"] for node in source["nodes"]
                              if node["op"] == "repeat"}, {rounds})
            for index in (0, 1, protocol.SCORED):
                assignment = json.loads(design.assignment(case, index))
                self.assertEqual(assignment["public_outputs"]["_s31_0"],
                                 design.output(case,
                                               assignment["public_inputs"]["_s31_abi_input_0"]))
                statement = statement_from_assignment(source, assignment)
                changed = study.changed_statement(raw_source, statement)
                self.assertNotEqual(statement, changed)
                self.assertEqual(json.loads(statement)["leaves"][0],
                                 json.loads(changed)["leaves"][0])

    def test_randomized_order_is_balanced_and_complete(self) -> None:
        schedule = protocol.schedule()
        self.assertEqual(len(schedule), len(protocol.CASES) * protocol.SCORED)
        for case in protocol.CASES:
            rows = [item for item in schedule if item["case"] == case]
            self.assertEqual({item["index"] for item in rows},
                             set(range(1, protocol.SCORED + 1)))
            self.assertEqual(sum(item["order"] == ["direct", "mixed"]
                                 for item in rows), protocol.SCORED // 2)
            self.assertEqual(sum(item["order"] == ["mixed", "direct"]
                                 for item in rows), protocol.SCORED // 2)

    def test_pow_report_parsers(self) -> None:
        self.assertEqual(study.reported_pow(
            b"S31 direct proof: interaction_pow=0.001024s fri_pow=0.049212s\n",
            "direct")["fri_pow_ns"], 49_212_000)
        self.assertEqual(study.reported_pow(
            b'S31_MIXED_NATIVE_PHASE_V1 {"schema":"s31-mixed-native-phase-v1",'
            b'"interaction_pow_ns":10,"fri_pow_ns":20}\n',
            "mixed")["fri_pow_ns"], 20)


if __name__ == "__main__":
    unittest.main()
