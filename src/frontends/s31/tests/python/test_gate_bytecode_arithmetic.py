"""Pinned Gate bytecode scalar replay and changed-cell controls."""

from __future__ import annotations

import hashlib
import struct
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT / "scripts"))

from export_s31_direct_gate_bytecode_arithmetic import (  # noqa: E402
    BUNDLE, check_composition_source_contract,
    check_composition_opening_source_contract,
    check_circle_factor_source_contract,
    check_base_vm_source_contract,
    check_ext_vm_source_contract,
    check_extension_source_decoder_contract,
    check_rebound_extension_source_contract,
    check_transcript_parameter_source_contract, check_oods_opening_source_contract,
    decoded_program, evaluate_row,
    gate_program,
)
from export_s31_direct_gate_evaluator_fixture import (  # noqa: E402
    add, arithmetic, base, denominator, interaction_residuals, mul, scale, sub,
)


def first_row() -> tuple[tuple[int, ...], ...]:
    return ((0, 0, 1, 0, 22, 22, 23, 2),
            (0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49),
            (1, 2, 3, 4, 5, 6, 7, 8),
            (9, 10, 11, 12, 13, 14, 15, 16))


def second_row() -> tuple[tuple[int, ...], ...]:
    return ((0, 0, 1, 0, 23, 23, 24, 4),
            (0, 1, 4, 49, 0, 1, 4, 49, 0, 1, 16, 2401),
            (17, 18, 19, 20, 21, 22, 23, 24),
            (25, 26, 27, 28, 29, 30, 31, 32))


def combine(parts: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    """Native secure_col basis (1, i, u, iu), for arbitrary QM31 parts."""
    result = base(0)
    for value, basis in zip(parts, (base(1), (0, 1, 0, 0),
                                    (0, 0, 1, 0), (0, 0, 0, 1)), strict=True):
        result = add(result, mul(value, basis))
    return result


def replay_oods(program, fixed, main, current, previous, alpha, z, scaled):
    """Independent opcode replay with nonbase QM31 trace-mask samples."""
    base_insts, ext_insts, roots = program
    registers = [base(0)] * len(base_insts)
    for op, tree, dst, a, b, imm in base_insts:
        if op == 0:
            registers[dst] = ((fixed, main, previous if imm == -1 else current)
                              [tree][a])
        elif op == 3:
            registers[dst] = base(a)
        else:
            registers[dst] = {4: add, 5: sub, 6: mul}[op](registers[a], registers[b])
    powers = []
    power = base(1)
    for _ in range(5):
        power = mul(power, alpha)
        powers.append(power)
    params = (*powers, z, scaled)
    extension = [base(0)] * len(ext_insts)
    for op, _reserved, dst, a, b, c, d in ext_insts:
        if op == 0:
            extension[dst] = combine(tuple(registers[index] for index in (a, b, c, d)))
        elif op == 1:
            extension[dst] = params[a]
        elif op == 2:
            extension[dst] = combine(tuple(map(base, (a, b, c, d))))
        elif op == 6:
            extension[dst] = sub(base(0), extension[a])
        else:
            extension[dst] = {3: add, 4: sub, 5: mul}[op](extension[a], extension[b])
    return tuple(extension[root] for root in roots)


def oods_denominator(address, limbs, alpha, z):
    result = limbs[3]
    for word in (limbs[2], limbs[1], limbs[0], address, base(378353459)):
        result = add(mul(result, alpha), word)
    return sub(result, z)


class GateBytecodeArithmeticTest(unittest.TestCase):
    def setUp(self) -> None:
        self.bundle = BUNDLE.read_bytes()
        self.program = decoded_program(gate_program(self.bundle))

    def check_row(self, row: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
        fixed, main, current, previous = row
        actual = evaluate_row(self.program, fixed, main, current, previous,
                              base(2), base(7), base(11), 512)
        pair, last = interaction_residuals(fixed, main, current, previous)
        self.assertEqual(tuple(base(value) for value in arithmetic(fixed, main)),
                         actual[:9])
        self.assertEqual((pair, last), actual[9:])
        return actual

    def test_all_eleven_roots_on_two_source_rows(self) -> None:
        for row in (first_row(), second_row()):
            with self.subTest(row=row[0][4]):
                actual = self.check_row(row)
                self.assertEqual(actual[:9], (base(0),) * 9)

    def test_changed_cells_reach_expected_root_families(self) -> None:
        original = self.check_row(first_row())
        fixed, main, current, previous = first_row()
        changed_fixed = list(fixed)
        changed_fixed[1], changed_fixed[2] = changed_fixed[2], changed_fixed[1]
        changed_main = list(main)
        changed_main[8], changed_main[11] = changed_main[11], changed_main[8]
        changed_current = list(current)
        changed_current[0], changed_current[4] = changed_current[4], changed_current[0]
        changed_previous = list(previous)
        changed_previous[4] += 1
        self.assertNotEqual(self.check_row((tuple(changed_fixed), main, current, previous))[:9],
                            original[:9])
        self.assertNotEqual(self.check_row((fixed, tuple(changed_main), current, previous))[:9],
                            original[:9])
        self.assertNotEqual(self.check_row((fixed, main, tuple(changed_current), previous))[9],
                            original[9])
        self.assertNotEqual(self.check_row((fixed, main, current, tuple(changed_previous)))[10],
                            original[10])

    def test_extension_roots_with_nonbase_challenges(self) -> None:
        alpha, z, claimed = (2, 3, 5, 7), (11, 13, 17, 19), (23, 29, 31, 37)
        for fixed, main, current, previous in (first_row(), second_row()):
            actual = evaluate_row(self.program, fixed, main, current, previous,
                                  alpha, z, claimed, 512)
            semantic = (fixed[0], fixed[3], fixed[1], fixed[2], *fixed[4:])
            left = denominator(semantic[4], main[:4], alpha, z)
            right = denominator(semantic[5], main[4:8], alpha, z)
            output = denominator(semantic[6], main[8:12], alpha, z)
            first = current[:4]
            last = current[4:]
            previous_last = previous[4:]
            pair = sub(mul(first, mul(left, right)), add(left, right))
            difference = add(sub(sub(last, previous_last), first),
                             scale(claimed, pow(512, -1, (1 << 31) - 1)))
            singleton = add(mul(difference, output), base(semantic[7]))
            self.assertEqual(actual[9:], (pair, singleton))

    def test_arithmetic_roots_over_nonbase_oods_cells(self) -> None:
        """The verifier runs base opcodes over QM31, not row-local M31."""
        for seed in (3, 211, 104729):
            fixed = tuple(tuple(seed + 17 * i + j for j in range(4)) for i in range(8))
            main = tuple(tuple(seed + 31 * i + 2 * j for j in range(4)) for i in range(12))
            registers = [base(0)] * 134
            for opcode, tree, dst, a, b, imm in self.program[0][:122]:
                if opcode == 0:
                    self.assertEqual(imm, 0)
                    registers[dst] = (fixed, main)[tree][a]
                elif opcode == 3:
                    registers[dst] = base(a)
                elif opcode == 4:
                    registers[dst] = add(registers[a], registers[b])
                elif opcode == 5:
                    registers[dst] = sub(registers[a], registers[b])
                elif opcode == 6:
                    registers[dst] = mul(registers[a], registers[b])
                else:
                    self.fail("unsupported arithmetic bytecode opcode")
            roots = tuple(registers[index] for index in
                          (24, 28, 31, 34, 37, 61, 85, 103, 121))
            fa, fs, fm, fp = fixed[0], fixed[3], fixed[1], fixed[2]
            x, y, output = main[:4], main[4:8], main[8:12]
            product = (
                sub(add(sub(mul(x[0], y[0]), mul(x[1], y[1])),
                        scale(sub(mul(x[2], y[2]), mul(x[3], y[3])), 2)),
                    add(mul(x[2], y[3]), mul(x[3], y[2]))),
                add(add(add(mul(x[0], y[1]), mul(x[1], y[0])),
                        scale(add(mul(x[2], y[3]), mul(x[3], y[2])), 2)),
                    sub(mul(x[2], y[2]), mul(x[3], y[3]))),
                sub(add(sub(mul(x[0], y[2]), mul(x[1], y[3])),
                        mul(x[2], y[0])), mul(x[3], y[1])),
                add(add(add(mul(x[0], y[3]), mul(x[1], y[2])),
                        mul(x[2], y[1])), mul(x[3], y[0])),
            )
            expected = (sub(add(add(fa, fs), add(fm, fp)), base(1)),
                        mul(fa, sub(fa, base(1))),
                        mul(fs, sub(fs, base(1))),
                        mul(fm, sub(fm, base(1))),
                        mul(fp, sub(fp, base(1))))
            # Each output limb uses the same four selector polynomials.
            for i in range(4):
                weighted = add(add(mul(product[i], fm),
                                   mul(add(x[i], y[i]), fa)),
                               add(mul(sub(x[i], y[i]), fs),
                                   mul(mul(x[i], y[i]), fp)))
                expected += (sub(output[i], weighted),)
            self.assertEqual(roots, expected)

    def test_base_vm_native_opcode_source_mutations_rejected(self) -> None:
        verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/"
                    "resident_verifier.zig").read_text()
        check_base_vm_source_contract(verifier)
        for old, new in (
            ("base[instruction.dst] = switch (instruction.op)",
             "base[instruction.a] = switch (instruction.op)"),
            ("                    instruction.a,\n"
             "                    instruction.imm,\n"
             "                )",
             "                    instruction.b,\n"
             "                    instruction.imm,\n"
             "                )"),
            (".constant => QM31.fromBase(M31.fromCanonical(instruction.a))",
             ".constant => QM31.fromBase(M31.fromCanonical(instruction.b))"),
            (".add => base[instruction.a].add(base[instruction.b])",
             ".add => base[instruction.a].mul(base[instruction.b])"),
            (".sub => base[instruction.a].sub(base[instruction.b])",
             ".sub => base[instruction.a].add(base[instruction.b])"),
            (".mul => base[instruction.a].mul(base[instruction.b])",
             ".mul => base[instruction.a].add(base[instruction.b])"),
        ):
            self.assertIn(old, verifier)
            with self.subTest(old=old), self.assertRaisesRegex(
                ValueError, "native Gate base opcode source contract changed"
            ):
                check_base_vm_source_contract(verifier.replace(old, new, 1))

    def test_base_vm_rejects_decoy_comment_and_string_arms(self) -> None:
        verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/"
                    "resident_verifier.zig").read_text()
        original = ".add => base[instruction.a].add(base[instruction.b])"
        changed = ".add => base[instruction.a].mul(base[instruction.b])"
        self.assertIn(original, verifier)
        for decoy in (f"\n// {original}\n",
                      f"\n/* {original} */\n",
                      f'\nconst decoy = "{original}";\n'):
            with self.subTest(decoy=decoy), self.assertRaisesRegex(
                ValueError, "native Gate base opcode source contract changed"
            ):
                check_base_vm_source_contract(verifier.replace(original, changed, 1) + decoy)

    def test_base_vm_rejects_post_switch_register_clobber(self) -> None:
        verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/"
                    "resident_verifier.zig").read_text()
        end = ".inv => try base[instruction.a].inv(),\n            };"
        self.assertEqual(verifier.count(end), 1)
        changed = verifier.replace(end, end + "\n            base[instruction.dst] = QM31.zero();", 1)
        with self.assertRaisesRegex(
            ValueError, "native Gate base opcode source contract changed"
        ):
            check_base_vm_source_contract(changed)

    def test_ext_vm_rejects_decoy_and_post_switch_clobber(self) -> None:
        verifier = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/"
                    "resident_verifier.zig").read_text()
        check_ext_vm_source_contract(verifier)
        old = ".add => extension[instruction.a].add(extension[instruction.b])"
        changed = verifier.replace(old,
                                   ".add => extension[instruction.a].mul(extension[instruction.b])",
                                   1) + f"\n// {old}\n"
        with self.assertRaisesRegex(
            ValueError, "native Gate extension opcode source contract changed"
        ):
            check_ext_vm_source_contract(changed)
        end = ".neg => extension[instruction.a].neg(),\n            };"
        self.assertEqual(verifier.count(end), 1)
        clobber = verifier.replace(end,
                                   end + "\n            extension[instruction.dst] = QM31.zero();",
                                   1)
        with self.assertRaisesRegex(
            ValueError, "native Gate extension opcode source contract changed"
        ):
            check_ext_vm_source_contract(clobber)

    def test_logup_roots_over_nonbase_oods_cells(self) -> None:
        """All sampled columns may be nonbase at the verifier's OODS point."""
        for seed in (3, 211, 104729):
            groups = tuple(tuple(tuple((seed + 17 * group + 31 * index +
                                      7 * limb * (group + 1)) % ((1 << 31) - 1)
                                     for limb in range(4))
                                 for index in range(size))
                           for group, size in enumerate((8, 12, 8, 8)))
            fixed, main, current, previous = groups
            alpha, z, scaled = (2, 3, 5, 7), (11, 13, 17, 19), (23, 29, 31, 37)
            actual = replay_oods(self.program, *groups, alpha, z, scaled)
            d0 = oods_denominator(fixed[4], main[:4], alpha, z)
            d1 = oods_denominator(fixed[5], main[4:8], alpha, z)
            dout = oods_denominator(fixed[6], main[8:12], alpha, z)
            first = combine(current[:4])
            last = combine(current[4:])
            prev = combine(previous[4:])
            expected_pair = sub(mul(first, mul(d0, d1)), add(d0, d1))
            expected_last = add(mul(add(sub(sub(last, prev), first), scaled), dout),
                                fixed[7])
            self.assertEqual(actual[9:], (expected_pair, expected_last))

    def test_interaction_mask_order(self) -> None:
        offsets = [[] for _ in range(8)]
        for op, tree, _dst, a, _b, imm in self.program[0]:
            if op == 0 and tree == 2 and imm not in offsets[a]:
                offsets[a].append(imm)
        self.assertEqual(offsets, [[0]] * 4 + [[-1, 0]] * 4)

    def test_native_mask_and_proof_conversion_source_order(self) -> None:
        """Guard the native source statements to which the Lean slot model binds."""
        engine = ROOT / "deps/stwo-zig/src"
        geometry = (engine / "frontends/cairo/witness/resident_geometry.zig").read_text()
        verifier = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
        conversion = (engine / "integrations/circuit_cpu/verifier_proof.zig").read_text()
        self.assertIn("offsets[instruction.a].append(allocator, instruction.imm)",
                      geometry)
        self.assertIn("point.add(step.mulSigned(offset))", geometry)
        self.assertIn("offsetIndex(offsets[local_column].items, offset)", verifier)
        self.assertIn("mask.items[interaction][global][sample_index]", verifier)
        self.assertIn("2 => .{ .at_oods = samples[1], .at_prev = samples[0] }",
                      conversion)
        self.assertIn("1 => .{ .at_oods = samples[0], .at_prev = null }",
                      conversion)

    def test_selected_composition_quotient_and_fold_order(self) -> None:
        """Recheck the selected eleven-root order and common zeroifier factor."""
        fixed, main, current, previous = first_row()
        roots = evaluate_row(self.program, fixed, main, current, previous,
                             (2, 3, 5, 7), (11, 13, 17, 19),
                             (23, 29, 31, 37), 512)
        coefficient, inverse = (41, 43, 47, 53), (59, 61, 67, 71)

        def fold(values):
            total = base(0)
            for value in values:
                total = add(mul(total, coefficient), value)
            return total

        self.assertEqual(fold(tuple(mul(root, inverse) for root in roots)),
                         mul(fold(roots), inverse))
        reordered = (*roots[:9], roots[10], roots[9])
        self.assertNotEqual(fold(roots), fold(reordered))
        engine = ROOT / "deps/stwo-zig/src"
        verifier = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
        accumulator = (engine / "core/air/accumulation.zig").read_text()
        component_fold = (engine / "core/air/components.zig").read_text()
        check_composition_source_contract(verifier, accumulator, component_fold)
        self.assertIn("const denominator_inverse = try zeroifier.inv();", verifier)
        self.assertIn("const evaluation = extension[root].mul(denominator_inverse);",
                      verifier)
        self.assertIn("accumulator.accumulate(evaluation);", verifier)
        self.assertIn("self.accumulation = self.accumulation.mul(self.random_coeff).add(evaluation);",
                      accumulator)
        with self.assertRaisesRegex(ValueError, "native Gate quotient accumulation source changed"):
            check_composition_source_contract(
                verifier.replace("extension[root].mul(denominator_inverse)",
                                 "extension[root]"), accumulator, component_fold)
        with self.assertRaisesRegex(ValueError, "native Gate quotient accumulation source changed"):
            check_composition_source_contract(
                verifier,
                accumulator.replace("self.accumulation.mul(self.random_coeff).add(evaluation)",
                                    "self.accumulation.add(evaluation).mul(self.random_coeff)"),
                component_fold)

    def test_selected_transcript_claim_parameter_source(self) -> None:
        native = (ROOT / "src/frontends/s31/runtime/native_verifier.zig").read_text()
        engine = ROOT / "deps/stwo-zig/src"
        lookup = (engine / "core/channel/lookup_transcript.zig").read_text()
        resident = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
        check_transcript_parameter_source_contract(native, lookup, resident)
        with self.assertRaisesRegex(ValueError, "lookup challenge/claim transcript mapping changed"):
            check_transcript_parameter_source_contract(
                native, lookup.replace(".z = values[0], .alpha = values[1]",
                                       ".z = values[1], .alpha = values[0]"), resident)
        with self.assertRaisesRegex(ValueError, "selected direct Gate transcript/claim order changed"):
            check_transcript_parameter_source_contract(
                native.replace("mixInteractionClaim(&channel, sums[0..sum_count]);",
                               "mixInteractionClaim(&channel, sums[1..sum_count]);"),
                lookup, resident)
        with self.assertRaisesRegex(ValueError, "resident Gate extension parameter mapping changed"):
            check_transcript_parameter_source_contract(
                native, lookup,
                resident.replace("self.claimed_sum.mulM31(claimed_scale)",
                                 "self.claimed_sum"))
        for original, changed in (
            (".lookup_z => self.lookup_z,", ".lookup_z => self.lookup_alpha,"),
            (".lookup_alpha_power => |power| self.lookup_alpha.pow(power),",
             ".lookup_alpha_power => |power| self.lookup_alpha.pow(power + 1),"),
            (".claimed_sum_scaled => self.claimed_sum.mulM31(claimed_scale),",
             ".claimed_sum_scaled => self.claimed_sum,"),
        ):
            with self.subTest(arm=original):
                decoy = resident.replace(original, changed, 1) + "\n// " + original + "\n"
                with self.assertRaisesRegex(ValueError, "resident Gate extension parameter mapping changed"):
                    check_transcript_parameter_source_contract(native, lookup, decoy)
        clobber = resident.replace(
            "        return out;\n    }\n\n    fn evaluateProgram",
            "        out[0] = self.lookup_z;\n        return out;\n    }\n\n    fn evaluateProgram",
            1,
        )
        self.assertNotEqual(clobber, resident)
        with self.assertRaisesRegex(ValueError, "resident Gate extension parameter mapping changed"):
            check_transcript_parameter_source_contract(native, lookup, clobber)
        native_marker = "mixInteractionClaim(&channel, sums[0..sum_count]);"
        prefix, suffix = native.rsplit(native_marker, 1)
        native_decoy = (prefix +
                        "mixInteractionClaim(&channel, sums[1..sum_count]);" +
                        suffix + "\n// " + native_marker + "\n")
        with self.assertRaisesRegex(ValueError, "selected direct Gate transcript/claim order changed"):
            check_transcript_parameter_source_contract(native_decoy, lookup, resident)

    def test_extension_source_decoder_rejects_tag_rebind_with_comment_decoy(self) -> None:
        decoder = (ROOT / "deps/stwo-zig/src/frontends/cairo/witness/composition_bundle.zig").read_text()
        check_extension_source_decoder_contract(decoder)
        for original, changed in (
            ("break :blk .lookup_z;", "break :blk .claimed_sum_scaled;"),
            ("break :blk .{ .lookup_alpha_power = power };", "break :blk .lookup_z;"),
            ("break :blk .claimed_sum_scaled;", "break :blk .lookup_z;"),
        ):
            with self.subTest(arm=original):
                mutant = decoder.replace(original, changed, 1) + "\n// " + original + "\n"
                with self.assertRaisesRegex(ValueError, "native Gate extension source decoder changed"):
                    check_extension_source_decoder_contract(mutant)

    def test_rebound_extension_sources_are_copied_without_reordering(self) -> None:
        air = (ROOT / "deps/stwo-zig/src/integrations/circuit_cpu/air.zig").read_text()
        check_rebound_extension_source_contract(air)
        original = "allocator.dupe(composition.ExtSource, source.ext_sources)"
        changed = "allocator.dupe(composition.ExtSource, source.ext_sources[1..])"
        mutant = air.replace(original, changed, 1) + "\n// " + original + "\n"
        with self.assertRaisesRegex(ValueError, "native Gate rebound extension source copy changed"):
            check_rebound_extension_source_contract(mutant)
        original_store = ".ext_sources = sources,"
        changed_store = ".ext_sources = sources[1..],"
        mutant_store = air.replace(original_store, changed_store, 1) + "\n// " + original_store + "\n"
        with self.assertRaisesRegex(ValueError, "native Gate rebound extension source copy changed"):
            check_rebound_extension_source_contract(mutant_store)
        pre_copy = air.replace(
            "    const sources = try allocator.dupe(composition.ExtSource, source.ext_sources);",
            "    source.ext_sources[0] = source.ext_sources[1];\n"
            "    const sources = try allocator.dupe(composition.ExtSource, source.ext_sources);",
            1,
        )
        self.assertNotEqual(pre_copy, air)
        with self.assertRaisesRegex(ValueError, "native Gate rebound extension source copy changed"):
            check_rebound_extension_source_contract(pre_copy)

    def test_oods_claim_uses_the_same_sample_tree_as_opening_check(self) -> None:
        engine = ROOT / "deps/stwo-zig/src"
        core = (engine / "core/verifier.zig").read_text()
        resident = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
        check_oods_opening_source_contract(core, resident)
        with self.assertRaisesRegex(ValueError, "native OODS claim/sample pass-through changed"):
            check_oods_opening_source_contract(
                core.replace("&proof.commitment_scheme_proof.sampled_values,",
                             "&other_sampled_values,"), resident)
        with self.assertRaisesRegex(ValueError, "native PCS proof forwarding changed"):
            check_oods_opening_source_contract(
                core.replace("verifyValuesWithProofCapture(allocator, sample_points, pcs_proof, channel, challenges, capture)",
                             "verifyValuesWithProofCapture(allocator, sample_points, other_proof, channel, challenges, capture)"),
                resident)
        with self.assertRaisesRegex(ValueError, "resident Gate OODS sample read changed"):
            check_oods_opening_source_contract(
                core, resident.replace("mask.items[0][global][0]",
                                       "mask.items[0][local_column][0]"))
        with self.assertRaisesRegex(ValueError, "resident Gate OODS sample read changed"):
            check_oods_opening_source_contract(
                core, resident.replace("mask.items[interaction][global][sample_index]",
                                       "mask.items[interaction][global][0]"))

    def test_split_one_composition_extraction_source(self) -> None:
        engine = ROOT / "deps/stwo-zig/src"
        core = (engine / "core/verifier.zig").read_text()
        proof = (engine / "core/proof.zig").read_text()
        types = (engine / "core/verifier_types.zig").read_text()
        resident = (engine / "frontends/cairo/witness/resident_verifier.zig").read_text()
        components = (engine / "core/air/components.zig").read_text()
        field = (engine / "core/fields/qm31.zig").read_text()
        def check(*args):
            return check_composition_opening_source_contract(*args)
        check(core, proof, types, resident, components, field)
        with self.assertRaisesRegex(ValueError, "default composition split changed"):
            check(core, proof, types.replace("COMPOSITION_LOG_SPLIT: u32 = 1",
                                             "COMPOSITION_LOG_SPLIT: u32 = 2"),
                  resident, components, field)
        with self.assertRaisesRegex(ValueError, "composition sampled-value extraction changed"):
            check(core, proof.replace("chunk_index * qm31.SECURE_EXTENSION_DEGREE + coordinate_index",
                                      "coordinate_index * chunk_count + chunk_index"),
                  types, resident, components, field)
        with self.assertRaisesRegex(ValueError, "composition sampled-value extraction changed"):
            check(core, proof.replace("if (column.len != 1) return null;",
                                      "if (column.len == 0) return null;"),
                  types, resident, components, field)
        with self.assertRaisesRegex(ValueError, "composition chunk reconstruction changed"):
            check(core, proof.replace("factor.mul(chunk_evals[input_index + 1])",
                                      "factor.mul(chunk_evals[input_index])"),
                  types, resident, components, field)
        with self.assertRaisesRegex(ValueError, "native composition coordinate basis changed"):
            check(core, proof, types, resident, components,
                  field.replace("QM31.fromU32Unchecked(0, 0, 1, 0)",
                                "QM31.fromU32Unchecked(0, 1, 0, 0)"))

    def test_oods_seed_circle_factor_source(self) -> None:
        engine = ROOT / "deps/stwo-zig/src/core"
        core = (engine / "verifier.zig").read_text()
        circle = (engine / "circle.zig").read_text()
        proof = (engine / "proof.zig").read_text()
        types = (engine / "verifier_types.zig").read_text()
        check_circle_factor_source_contract(core, circle, proof, types)
        with self.assertRaisesRegex(ValueError, "native checked OODS seed/point path changed"):
            check_circle_factor_source_contract(
                core.replace("pointFromOodsSeed(oods_seed)",
                             "pointFromOodsSeed(other_seed)"), circle, proof, types)
        with self.assertRaisesRegex(ValueError, "native checked OODS seed/point path changed"):
            check_circle_factor_source_contract(
                core.replace("return VerificationError.InvalidOodsSeed;",
                             "return VerificationError.InvalidStructure;"), circle, proof, types)
        with self.assertRaisesRegex(ValueError, "native checked OODS seed/point path changed"):
            check_circle_factor_source_contract(
                core.replace("secureFieldPointFromRandomSeedChecked(seed)",
                             "secureFieldPointFromRandomSeed(seed)"), circle, proof, types)
        with self.assertRaisesRegex(ValueError, "native OODS seed-to-circle map changed"):
            check_circle_factor_source_contract(
                core, circle.replace("const y = t.add(t).mul(one_plus_t_square_inv);",
                                     "const y = t.mul(one_plus_t_square_inv);"), proof, types)
        with self.assertRaisesRegex(ValueError, "native circle repeated-double arithmetic changed"):
            check_circle_factor_source_contract(
                core, circle.replace("out = out.double();", "out = out.add(self);"), proof, types)
        with self.assertRaisesRegex(ValueError, "native composition factor selection changed"):
            check_circle_factor_source_contract(
                core, circle,
                proof.replace("point.repeatedDouble(parent_log - 2).x",
                              "point.repeatedDouble(parent_log - 1).x"), types)

    def test_changed_installed_bundle_is_rejected(self) -> None:
        mutation = bytearray(self.bundle)
        mutation[-32] ^= 1
        self.assertNotEqual(hashlib.sha256(mutation).hexdigest(),
                            hashlib.sha256(self.bundle).hexdigest())
        with self.assertRaisesRegex(ValueError, "installed AIR bundle digest changed"):
            gate_program(bytes(mutation))

    def test_rehashed_root_order_is_rejected(self) -> None:
        mutation = bytearray(gate_program(self.bundle))
        # Root section is the last 44 bytes of the fixed selected program.
        mutation[-44], mutation[-40] = mutation[-40], mutation[-44]
        semantic = 0xCBF29CE484222325
        for byte in mutation[216:]:
            semantic ^= byte
            semantic = (semantic * 0x100000001B3) & ((1 << 64) - 1)
        struct.pack_into("<Q", mutation, 16, semantic)
        with self.assertRaisesRegex(ValueError, "selected Gate semantic identity changed"):
            decoded_program(bytes(mutation))

    def test_rehashed_previous_mask_read_is_rejected(self) -> None:
        mutation = bytearray(gate_program(self.bundle))
        # Base instruction 126 is column 4 at offset -1. Replace with 0.
        struct.pack_into("<i", mutation, 216 + 126 * 16 + 12, 0)
        semantic = 0xCBF29CE484222325
        for byte in mutation[216:]:
            semantic ^= byte
            semantic = (semantic * 0x100000001B3) & ((1 << 64) - 1)
        struct.pack_into("<Q", mutation, 16, semantic)
        with self.assertRaisesRegex(ValueError, "selected Gate semantic identity changed"):
            decoded_program(bytes(mutation))

    def test_previous_mask_opcode_changes_only_singleton_row_root(self) -> None:
        """The selected -1 read has semantic effect, beyond its pinned digest."""
        base_insts, ext_insts, roots = self.program
        changed_base = list(base_insts)
        op, tree, dst, column, auxiliary, offset = changed_base[126]
        self.assertEqual((op, tree, column, offset), (0, 2, 4, -1))
        changed_base[126] = (op, tree, dst, column, auxiliary, 0)
        fixed, main, current, previous = first_row()
        arguments = (fixed, main, current, previous,
                     base(2), base(7), base(11), 512)
        honest = evaluate_row(self.program, *arguments)
        changed = evaluate_row((changed_base, ext_insts, roots), *arguments)
        self.assertEqual(honest[:10], changed[:10])
        self.assertNotEqual(honest[10], changed[10])


if __name__ == "__main__":
    unittest.main()
