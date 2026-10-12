-- Generated from the exact checked STWZEVA/1 qm31_ops program.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Native rebind changes domain log size (23 to 9), not these instructions.
import S31.Gadgets.Air.DirectGatePolynomial

namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

open S31.Gadgets.Packed

open S31.Gadgets.Air.DirectGateEvaluatorCells

open S31.Gadgets.Air.DirectGatePolynomial

set_option linter.unusedVariables false

/-- The first nine installed roots are secure-column injections of
base registers 24, 28, 31, 34, 37, 61, 85, 103, 121.
Registers 25 in their other coordinates are the bytecode constant zero. -/
def bytecodeArithmeticOver {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) : List K := Id.run do
  let r0 : K := cells.localFixed 0
  let r1 : K := cells.localFixed 1
  let r2 : K := cells.localFixed 2
  let r3 : K := cells.localFixed 3
  let r4 : K := cells.localFixed 4
  let r5 : K := cells.localFixed 5
  let r6 : K := cells.localFixed 6
  let r7 : K := cells.localFixed 7
  let r8 : K := cells.main 0
  let r9 : K := cells.main 1
  let r10 : K := cells.main 2
  let r11 : K := cells.main 3
  let r12 : K := cells.main 4
  let r13 : K := cells.main 5
  let r14 : K := cells.main 6
  let r15 : K := cells.main 7
  let r16 : K := cells.main 8
  let r17 : K := cells.main 9
  let r18 : K := cells.main 10
  let r19 : K := cells.main 11
  let r20 : K := r0 + r3
  let r21 : K := r20 + r1
  let r22 : K := r21 + r2
  let r23 : K := 1
  let r24 : K := r22 - r23
  let r25 : K := 0
  let r26 : K := 1
  let r27 : K := r0 - r26
  let r28 : K := r0 * r27
  let r29 : K := 1
  let r30 : K := r3 - r29
  let r31 : K := r3 * r30
  let r32 : K := 1
  let r33 : K := r1 - r32
  let r34 : K := r1 * r33
  let r35 : K := 1
  let r36 : K := r2 - r35
  let r37 : K := r2 * r36
  let r38 : K := r8 * r12
  let r39 : K := r9 * r13
  let r40 : K := r38 - r39
  let r41 : K := r10 * r14
  let r42 : K := r11 * r15
  let r43 : K := r41 - r42
  let r44 : K := 2
  let r45 : K := r44 * r43
  let r46 : K := r40 + r45
  let r47 : K := r10 * r15
  let r48 : K := r46 - r47
  let r49 : K := r11 * r14
  let r50 : K := r48 - r49
  let r51 : K := r50 * r1
  let r52 : K := r8 + r12
  let r53 : K := r52 * r0
  let r54 : K := r51 + r53
  let r55 : K := r8 - r12
  let r56 : K := r55 * r3
  let r57 : K := r54 + r56
  let r58 : K := r8 * r12
  let r59 : K := r58 * r2
  let r60 : K := r57 + r59
  let r61 : K := r16 - r60
  let r62 : K := r8 * r13
  let r63 : K := r9 * r12
  let r64 : K := r62 + r63
  let r65 : K := r10 * r15
  let r66 : K := r11 * r14
  let r67 : K := r65 + r66
  let r68 : K := 2
  let r69 : K := r68 * r67
  let r70 : K := r64 + r69
  let r71 : K := r10 * r14
  let r72 : K := r70 + r71
  let r73 : K := r11 * r15
  let r74 : K := r72 - r73
  let r75 : K := r74 * r1
  let r76 : K := r9 + r13
  let r77 : K := r76 * r0
  let r78 : K := r75 + r77
  let r79 : K := r9 - r13
  let r80 : K := r79 * r3
  let r81 : K := r78 + r80
  let r82 : K := r9 * r13
  let r83 : K := r82 * r2
  let r84 : K := r81 + r83
  let r85 : K := r17 - r84
  let r86 : K := r8 * r14
  let r87 : K := r9 * r15
  let r88 : K := r86 - r87
  let r89 : K := r10 * r12
  let r90 : K := r88 + r89
  let r91 : K := r11 * r13
  let r92 : K := r90 - r91
  let r93 : K := r92 * r1
  let r94 : K := r10 + r14
  let r95 : K := r94 * r0
  let r96 : K := r93 + r95
  let r97 : K := r10 - r14
  let r98 : K := r97 * r3
  let r99 : K := r96 + r98
  let r100 : K := r10 * r14
  let r101 : K := r100 * r2
  let r102 : K := r99 + r101
  let r103 : K := r18 - r102
  let r104 : K := r8 * r15
  let r105 : K := r9 * r14
  let r106 : K := r104 + r105
  let r107 : K := r10 * r13
  let r108 : K := r106 + r107
  let r109 : K := r11 * r12
  let r110 : K := r108 + r109
  let r111 : K := r110 * r1
  let r112 : K := r11 + r15
  let r113 : K := r112 * r0
  let r114 : K := r111 + r113
  let r115 : K := r11 - r15
  let r116 : K := r115 * r3
  let r117 : K := r114 + r116
  let r118 : K := r11 * r15
  let r119 : K := r118 * r2
  let r120 : K := r117 + r119
  let r121 : K := r19 - r120
  return [r24, r28, r31, r34, r37, r61, r85, r103, r121]

/-- Ring-polynomial identity for arbitrary sampled base-column
values. This includes native QM31 OODS samples. -/
theorem bytecode_arithmetic_over_eq {K : Type*} [CommRing K]
    (cells : ArithmeticCells K) :
    bytecodeArithmeticOver cells = modeledArithmetic cells := by
  simp [bytecodeArithmeticOver, modeledArithmetic]

def bytecodeArithmetic (cells : Cells) : List F :=
  bytecodeArithmeticOver (fromM31Cells cells)

/-- The generic identity specializes to the earlier M31 model. -/
theorem bytecode_arithmetic_eq (cells : Cells) :
    bytecodeArithmetic cells = arithmetic cells := by
  simpa [bytecodeArithmetic, bytecode_arithmetic_over_eq] using
    modeled_m31_eq_pure cells

/-- Zero arithmetic roots of the selected program enforce the
decoded Gate operation and output for arbitrary local cells. -/
theorem bytecode_zero_decodes (cells : Cells)
    (hzero : ∀ residual ∈ bytecodeArithmetic cells, residual = 0) :
    ∃ op, (decodedRow cells).flags = S31.Gadgets.Air.Qm31Ops.encode op ∧
      (decodedRow cells).output = S31.Gadgets.Air.Qm31Ops.evaluate op
        (decodedRow cells).in0 (decodedRow cells).in1 := by
  apply arithmetic_zero_decodes cells
  simpa [bytecode_arithmetic_eq] using hzero

end S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
