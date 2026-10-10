"""Independent value and source-shape checks for nominal fixed-width integers."""

import sys
import unittest
from pathlib import Path

S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


def limbs(value: int, width: int) -> list[int]:
    return [(value >> (16 * i)) & 0xffff for i in range(max(1, width // 16))]


class FixedWidthIntegerTests(unittest.TestCase):
    def assignment(self, relation: dict, width: int, a: int, b: int, result: int | bool) -> dict:
        return {
            "public_inputs": {},
            "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
            "public_outputs": {relation["public_outputs"][0]:
                               [int(result)] if isinstance(result, bool) else limbs(result, width)},
        }

    def test_unsigned_div_rem_all_widths_and_boundaries(self) -> None:
        for width in (8, 16, 32, 64, 128):
            kind = f"u{width}"
            count = max(1, width // 16)
            result_type = kind if width == 128 else f"[u16; {2 * count}]"
            result_expr = "q" if width == 128 else "std::array::concat(std::int::limbs(q), std::int::limbs(r))"
            source = (f"circuit divide(private a: {kind}, private b: {kind}) -> public {result_type} "
                      "{ let (q, r) = std::int::div_rem(a, b); "
                      f"let result = {result_expr}; result }}")
            relation, _ = compile_text(source)
            output_name = relation["public_outputs"][0]
            self.assertEqual([node["op"] for node in relation["nodes"]].count("int_div_rem"), 1)
            divide = next(node for node in relation["nodes"] if node["op"] == "int_div_rem")
            self.assertEqual(divide["constant"], width)
            for a, b in ((0, 1), (1, 2), ((1 << width) - 1, 1),
                         ((1 << width) - 1, (1 << (width - 1)) + 1),
                         (min(123456789, (1 << width) - 1), 7)):
                with self.subTest(width=width, a=a, b=b):
                    q, r = divmod(a, b)
                    expected = limbs(q, width) + ([] if width == 128 else limbs(r, width))
                    assignment = {"public_inputs": {},
                                  "private_inputs": {"a": limbs(a, width), "b": limbs(b, width)},
                                  "public_outputs": {output_name: expected}}
                    self.assertEqual(evaluate_relation(relation, assignment), {output_name: expected})
                    assignment["public_outputs"][output_name] = expected.copy()
                    assignment["public_outputs"][output_name][0 if width == 128 else count] ^= 1
                    with self.assertRaises(OracleError):
                        evaluate_relation(relation, assignment)
            zero = {"public_inputs": {},
                    "private_inputs": {"a": limbs(17, width), "b": limbs(0, width)},
                    "public_outputs": {output_name: [0] * (count if width == 128 else 2 * count)}}
            with self.assertRaisesRegex(OracleError, "division by zero"):
                evaluate_relation(relation, zero)

    def test_signed_div_rem_truncates_toward_zero_and_checks_overflow(self) -> None:
        for width in (8, 16, 32, 64, 128):
            kind = f"i{width}"
            count = max(1, width // 16)
            half = 1 << (width - 1)
            result_type = kind if width == 128 else f"[u16; {2 * count}]"
            result_expr = "q" if width == 128 else "std::array::concat(std::int::limbs(q), std::int::limbs(r))"
            source = (f"circuit divide(private a: {kind}, private b: {kind}) -> public {result_type} "
                      "{ let (q, r) = std::int::div_rem(a, b); "
                      f"let result = {result_expr}; result }}")
            relation, _ = compile_text(source)
            output_name = relation["public_outputs"][0]
            divide = next(node for node in relation["nodes"] if node["op"] == "int_div_rem")
            self.assertEqual(divide["constant"], width | 256)
            for a, b in ((0, 1), (7, 3), (-7, 3), (7, -3), (-7, -3),
                         (-half, 1), (half - 1, -1)):
                with self.subTest(width=width, a=a, b=b):
                    q_magnitude, r_magnitude = divmod(abs(a), abs(b))
                    q = -q_magnitude if (a < 0) != (b < 0) else q_magnitude
                    r = -r_magnitude if a < 0 else r_magnitude
                    expected = limbs(q % (1 << width), width) + (
                        [] if width == 128 else limbs(r % (1 << width), width))
                    assignment = {"public_inputs": {},
                                  "private_inputs": {"a": limbs(a % (1 << width), width),
                                                     "b": limbs(b % (1 << width), width)},
                                  "public_outputs": {output_name: expected}}
                    self.assertEqual(evaluate_relation(relation, assignment), {output_name: expected})
            overflow = {"public_inputs": {},
                        "private_inputs": {"a": limbs(half, width), "b": limbs((1 << width) - 1, width)},
                        "public_outputs": {output_name: [0] * (count if width == 128 else 2 * count)}}
            with self.assertRaisesRegex(OracleError, "division overflow"):
                evaluate_relation(relation, overflow)

    def test_division_projections_use_the_same_relation_operation(self) -> None:
        for function, expected in (("div_checked", 254), ("rem_checked", 255)):
            with self.subTest(function=function):
                source = ("circuit project(private a: i8, private b: i8) -> public i8 "
                          f"{{ std::int::{function}(a, b) }}")
                relation, _ = compile_text(source)
                self.assertEqual([node["op"] for node in relation["nodes"]].count("int_div_rem"), 1)
                assignment = {"public_inputs": {}, "private_inputs": {"a": [249], "b": [3]},
                              "public_outputs": {relation["public_outputs"][0]: [expected]}}
                self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_div_rem_rejects_mixed_and_inactive_branches(self) -> None:
        with self.assertRaisesRegex(SourceError, "equally typed"):
            compile_text("circuit bad(private a: u8, private b: u16) -> public u8 "
                         "{ let (q, r) = std::int::div_rem(a, b); q }")
        with self.assertRaisesRegex(SourceError, "inactive"):
            compile_text("circuit bad(private flag: bit, private a: u8, private b: u8) -> public u8 "
                         "{ if flag then std::int::div_rem(a, b).0 else a }")

    def test_all_ten_types_checked_and_wrapping_add(self) -> None:
        for width in (8, 16, 32, 64, 128):
            for prefix in ("u", "i"):
                kind = f"{prefix}{width}"
                with self.subTest(kind=kind):
                    source = (f"circuit add(private a: {kind}, private b: {kind}) -> public {kind} "
                              "{ std::int::add_wrapping(a, b) }")
                    relation, _ = compile_text(source)
                    self.assertEqual([n["op"] for n in relation["nodes"]],
                                     ["int_view", "int_view", "int_add_wrapping"])
                    spec = width | (256 if prefix == "i" else 0)
                    self.assertTrue(all(n["constant"] == spec for n in relation["nodes"]))
                    a = (1 << width) - 1
                    b = 1
                    expected = 0
                    assignment = self.assignment(relation, width, a, b, expected)
                    self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

                    checked, _ = compile_text(source.replace("add_wrapping", "add_checked"))
                    if prefix == "u":
                        with self.assertRaisesRegex(OracleError, "overflow"):
                            evaluate_relation(checked, self.assignment(checked, width, a, b, expected))
                    else:
                        self.assertEqual(evaluate_relation(
                            checked, self.assignment(checked, width, a, b, expected)),
                            self.assignment(checked, width, a, b, expected)["public_outputs"])
                        high = (1 << (width - 1)) - 1
                        with self.assertRaisesRegex(OracleError, "overflow"):
                            evaluate_relation(checked, self.assignment(checked, width, high, 1, high + 1))

    def test_subtraction_and_signed_order(self) -> None:
        for kind, width, a, b, expected_le in (("u8", 8, 255, 1, False),
                                                ("i8", 8, 255, 1, True),
                                                ("u128", 128, 1 << 127, 1, False),
                                                ("i128", 128, 1 << 127, 1, True)):
            with self.subTest(kind=kind):
                compare, _ = compile_text(
                    f"circuit compare(private a: {kind}, private b: {kind}) -> public bit "
                    "{ std::int::le(a, b) }")
                assignment = self.assignment(compare, width, a, b, expected_le)
                self.assertEqual(evaluate_relation(compare, assignment), assignment["public_outputs"])
                subtract, _ = compile_text(
                    f"circuit subtract(private a: {kind}, private b: {kind}) -> public {kind} "
                    "{ std::int::sub_wrapping(a, b) }")
                result = (a - b) % (1 << width)
                assignment = self.assignment(subtract, width, a, b, result)
                self.assertEqual(evaluate_relation(subtract, assignment), assignment["public_outputs"])

    def test_wrapping_multiplication_all_fixed_width_types(self) -> None:
        for width in (8, 16, 32, 64, 128):
            for prefix in ("u", "i"):
                kind = f"{prefix}{width}"
                with self.subTest(kind=kind):
                    relation, _ = compile_text(
                        f"circuit product(private a: {kind}, private b: {kind}) -> public {kind} "
                        "{ std::int::mul_wrapping(a, b) }")
                    self.assertEqual([node["op"] for node in relation["nodes"]],
                                     ["int_view", "int_view", "int_mul_wrapping"])
                    spec = width | (256 if prefix == "i" else 0)
                    self.assertEqual([node["constant"] for node in relation["nodes"]], [spec] * 3)
                    for a, b in ((0, 17), (1, (1 << width) - 1),
                                 ((1 << width) - 1, 2),
                                 ((1 << (width - 1)) + 3, 19)):
                        expected = (a * b) % (1 << width)
                        assignment = self.assignment(relation, width, a, b, expected)
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"][relation["public_outputs"][0]] = limbs(
                            (expected + 1) % (1 << width), width)
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)

    def test_wrapping_multiplication_is_total_and_type_checked(self) -> None:
        relation, _ = compile_text(
            "circuit choice(private bit: bit, private a: i8, private b: i8) -> public i8 "
            "{ if bit then std::int::mul_wrapping(a, b) else a }")
        self.assertIn("int_mul_wrapping", [node["op"] for node in relation["nodes"]])
        with self.assertRaisesRegex(SourceError, "equally typed"):
            compile_text("circuit bad(private a: u16, private b: i16) -> public u16 "
                         "{ std::int::mul_wrapping(a, b) }")

    def test_checked_multiplication_all_fixed_width_types(self) -> None:
        for width in (8, 16, 32, 64, 128):
            for prefix in ("u", "i"):
                kind = f"{prefix}{width}"
                with self.subTest(kind=kind):
                    relation, _ = compile_text(
                        f"circuit product(private a: {kind}, private b: {kind}) -> public {kind} "
                        "{ std::int::mul_checked(a, b) }")
                    self.assertEqual([node["op"] for node in relation["nodes"]],
                                     ["int_view", "int_view", "int_mul_checked"])
                    spec = width | (256 if prefix == "i" else 0)
                    self.assertEqual([node["constant"] for node in relation["nodes"]], [spec] * 3)
                    if prefix == "u":
                        valid = ((0, (1 << width) - 1, 0),
                                 ((1 << width) - 1, 1, (1 << width) - 1),
                                 (33, 3, 99))
                        overflow = (((1 << width) - 1, 2),
                                    (1 << (width - 1), 2))
                    else:
                        mask = (1 << width) - 1
                        half = 1 << (width - 1)
                        valid = ((mask, 2, mask - 1),
                                 (half, 1, half),
                                 (mask, mask, 1),
                                 (half, 0, 0),
                                 (half - 1, mask, half + 1))
                        overflow = ((half, mask), (half - 1, 2),
                                    (half, 2))
                    for a, b, result in valid:
                        assignment = self.assignment(relation, width, a, b, result)
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                    for a, b in overflow:
                        with self.assertRaisesRegex(OracleError, "multiplication overflow"):
                            evaluate_relation(relation,
                                              self.assignment(relation, width, a, b, 0))

    def test_checked_multiplication_is_partial_in_dynamic_branches(self) -> None:
        with self.assertRaises(SourceError):
            compile_text(
                "circuit choice(private bit: bit, private a: i8, private b: i8) -> public i8 "
                "{ if bit then std::int::mul_checked(a, b) else a }")

    def test_named_multiply_helper_has_no_relation_overhead(self) -> None:
        direct = ("circuit product(private a: u32, private b: u32) -> public u32 "
                  "{ std::int::mul_wrapping(a, b) }")
        via_function = (
            "fn multiply(a: u32, b: u32) -> u32 { std::int::mul_wrapping(a, b) } "
            "circuit product(private a: u32, private b: u32) -> public u32 "
            "{ multiply(a, b) }"
        )
        direct_relation, _ = compile_text(direct)
        functional_relation, _ = compile_text(via_function)
        self.assertEqual(direct_relation, functional_relation)

        checked_direct, _ = compile_text(direct.replace("mul_wrapping", "mul_checked"))
        checked_function, _ = compile_text(via_function.replace("mul_wrapping", "mul_checked"))
        self.assertEqual(checked_direct, checked_function)

    def test_byte_range_and_explicit_limb_conversion(self) -> None:
        relation, _ = compile_text(
            "circuit from_limbs(public raw: [u16; 1]) -> public u8 "
            "{ std::int::from_limbs_u8(raw) }")
        output = relation["public_outputs"][0]
        self.assertEqual(relation["nodes"][0]["op"], "int_view")
        self.assertEqual(evaluate_relation(relation, {"public_inputs": {"raw": [255]},
                          "private_inputs": {}, "public_outputs": {output: [255]}}), {output: [255]})
        with self.assertRaisesRegex(OracleError, "exceeds 8 bits"):
            evaluate_relation(relation, {"public_inputs": {"raw": [256]},
                               "private_inputs": {}, "public_outputs": {output: [256]}})
        with self.assertRaisesRegex(SourceError, "requires \\[u16; 1\\]"):
            compile_text("circuit bad(private x: [u16; 2]) -> public u8 { std::int::from_limbs_u8(x) }")

    def test_nominal_mismatch_and_reinterpret(self) -> None:
        with self.assertRaisesRegex(SourceError, "equally typed"):
            compile_text("circuit bad(private a: u16, private b: i16) -> public u16 "
                         "{ std::int::add_checked(a, b) }")
        relation, _ = compile_text(
            "circuit reinterpret(private a: i8, private b: i8) -> public u8 "
            "{ std::int::reinterpret_u8(std::int::add_wrapping(a, b)) }")
        assignment = self.assignment(relation, 8, 255, 0, 255)
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_checked_casts_all_source_destination_pairs(self) -> None:
        kinds = [(f"{sign}{width}", width, sign == "i")
                 for sign in ("u", "i") for width in (8, 16, 32, 64, 128)]
        for source_kind, source_width, source_signed in kinds:
            source_limit = 1 << source_width
            patterns = {0, 1, source_limit // 2 - 1, source_limit // 2,
                        source_limit // 2 + 1, source_limit - 1}
            for target_kind, target_width, target_signed in kinds:
                with self.subTest(source=source_kind, target=target_kind):
                    relation, _ = compile_text(
                        f"circuit convert(private x: {source_kind}) -> public {target_kind} "
                        f"{{ std::int::cast_checked_{target_kind}(x) }}")
                    self.assertEqual([node["op"] for node in relation["nodes"]],
                                     ["int_view", "int_cast_checked"])
                    self.assertEqual(relation["nodes"][-1]["constant"],
                                     (source_width | (256 if source_signed else 0)) |
                                     ((target_width | (256 if target_signed else 0)) << 9))
                    output = relation["public_outputs"][0]
                    low = -(1 << (target_width - 1)) if target_signed else 0
                    high = (1 << (target_width - 1)) - 1 if target_signed else (1 << target_width) - 1
                    for pattern in patterns:
                        value = pattern - source_limit if source_signed and pattern >= source_limit // 2 else pattern
                        assignment = {"public_inputs": {}, "private_inputs": {"x": limbs(pattern, source_width)},
                                      "public_outputs": {output: limbs(value % (1 << target_width), target_width)}}
                        if low <= value <= high:
                            self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
                        else:
                            with self.assertRaisesRegex(OracleError, "cast overflow"):
                                evaluate_relation(relation, assignment)

    def test_checked_cast_cannot_fail_in_inactive_branch(self) -> None:
        with self.assertRaises(SourceError):
            compile_text("circuit bad(private b: bit, private x: i16) -> public i8 "
                         "{ if b then std::int::cast_checked_i8(x) else std::int::cast_checked_i8(x) }")

    def test_bitwise_operations_on_all_ten_types(self) -> None:
        for width in (8, 16, 32, 64, 128):
            mask = (1 << width) - 1
            patterns = ((0x55 * ((1 << width) - 1) // 255) & mask,
                        (0xaa * ((1 << width) - 1) // 255) & mask)
            for prefix in ("u", "i"):
                kind = f"{prefix}{width}"
                for operation, expected in (("bit_and", patterns[0] & patterns[1]),
                                            ("bit_or", patterns[0] | patterns[1]),
                                            ("bit_xor", patterns[0] ^ patterns[1]),
                                            ("bit_not", (~patterns[0]) & mask)):
                    with self.subTest(kind=kind, operation=operation):
                        arguments = "a" if operation == "bit_not" else "a, b"
                        relation, _ = compile_text(
                            f"circuit bits(private a: {kind}, private b: {kind}) -> public {kind} "
                            f"{{ std::int::{operation}({arguments}) }}")
                        op = f"int_{operation}"
                        self.assertEqual(relation["nodes"][-1]["op"], op)
                        assignment = self.assignment(relation, width, *patterns, expected)
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"][relation["public_outputs"][0]] = limbs(
                            (expected + 1) & mask, width)
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)

    def test_bitwise_chain_is_total_and_static_helper_is_zero_cost(self) -> None:
        direct = ("circuit bits(private a: u32, private b: u32) -> public u32 "
                  "{ std::int::bit_xor(std::int::bit_and(a, b), std::int::bit_not(a)) }")
        helper = ("fn mix(a: u32, b: u32) -> u32 { "
                  "std::int::bit_xor(std::int::bit_and(a, b), std::int::bit_not(a)) } "
                  "circuit bits(private a: u32, private b: u32) -> public u32 { mix(a, b) }")
        self.assertEqual(compile_text(direct)[0], compile_text(helper)[0])
        relation, _ = compile_text(
            "circuit choose(private pick: bit, private a: u8, private b: u8) -> public u8 "
            "{ if pick then std::int::bit_xor(a, b) else std::int::bit_not(a) }")
        self.assertIn("int_bit_xor", [node["op"] for node in relation["nodes"]])

    def test_bitwise_rejects_nominal_mismatch_and_extra_metadata(self) -> None:
        with self.assertRaisesRegex(SourceError, "equally typed"):
            compile_text("circuit bad(private a: u16, private b: i16) -> public u16 "
                         "{ std::int::bit_xor(a, b) }")
        relation, _ = compile_text("circuit bits(private a: u8) -> public u8 "
                                   "{ std::int::bit_not(a) }")
        relation["nodes"][-1]["index"] = 0
        assignment = {"public_inputs": {}, "private_inputs": {"a": [1]},
                      "public_outputs": {relation["public_outputs"][0]: [254]}}
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_static_shifts_and_rotations_at_boundaries(self) -> None:
        cases = [
            ("u8", "shl", 1, 128, 0, 1),
            ("u8", "shr_logical", 8, 255, 0, 8),
            ("i8", "shr_arithmetic", 1, 253, 254, 1),
            ("i8", "shr_arithmetic", 80, 253, 255, 8),
            ("u32", "rotl", 16, 0x12345678, 0x56781234, 16),
            ("u32", "rotr", 4, 0x12345678, 0x81234567, 4),
            ("u32", "shl", 16, 0x12345678, 0x56780000, 16),
            ("u32", "shr_logical", 16, 0x12345678, 0x1234, 16),
            ("i128", "shr_arithmetic", 127, (1 << 128) - 2, (1 << 128) - 1, 127),
            ("u128", "rotl", 128, 1 << 127, 1 << 127, 0),
            ("u128", "rotr", 129, 1, 1 << 127, 1),
        ]
        for kind, operation, source_count, pattern, expected, normalized in cases:
            with self.subTest(kind=kind, operation=operation, count=source_count):
                width = int(kind[1:])
                relation, _ = compile_text(
                    f"circuit shift(private a: {kind}) -> public {kind} "
                    f"{{ let result = std::int::{operation}<{source_count}>(a); result }}")
                self.assertEqual(relation["nodes"][-1]["op"], f"int_{operation}")
                self.assertEqual(relation["nodes"][-1]["index"], normalized)
                assignment = {"public_inputs": {}, "private_inputs": {"a": limbs(pattern, width)},
                              "public_outputs": {"result": limbs(expected, width)}}
                self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
                assignment["public_outputs"]["result"][0] ^= 1
                with self.assertRaises(OracleError):
                    evaluate_relation(relation, assignment)

    def test_static_shift_rejects_invalid_metadata_and_unsigned_arithmetic(self) -> None:
        with self.assertRaisesRegex(SourceError, "requires a signed"):
            compile_text("circuit bad(private a: u8) -> public u8 "
                         "{ std::int::shr_arithmetic<1>(a) }")
        with self.assertRaises(SourceError):
            compile_text("circuit bad(private a: u8) -> public u8 { std::int::shl(a) }")
        relation, _ = compile_text("circuit shift(private a: i16) -> public i16 "
                                   "{ std::int::rotr<1>(a) }")
        relation["nodes"][-1]["index"] = 16
        assignment = {"public_inputs": {}, "private_inputs": {"a": [1]},
                      "public_outputs": {relation["public_outputs"][0]: [32768]}}
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
