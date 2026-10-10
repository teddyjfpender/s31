-- Generated from the exact checked STWZEVA/1 qm31_ops program.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Native rebind changes domain log size (23 to 9), not these instructions.
import S31.Gadgets.Air.DirectGateEvaluatorCells

namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

open S31.Gadgets.Packed

open S31.Gadgets.Air.DirectGateEvaluatorCells

set_option linter.unusedVariables false

/-- The first nine installed roots are secure-column injections of
base registers 24, 28, 31, 34, 37, 61, 85, 103, 121.
Registers 25 in their other coordinates are the bytecode constant zero. -/
def bytecodeArithmetic (cells : Cells) : List F := Id.run do
  let r0 : F := cells.localFixed 0
  let r1 : F := cells.localFixed 1
  let r2 : F := cells.localFixed 2
  let r3 : F := cells.localFixed 3
  let r4 : F := cells.localFixed 4
  let r5 : F := cells.localFixed 5
  let r6 : F := cells.localFixed 6
  let r7 : F := cells.localFixed 7
  let r8 : F := cells.main 0
  let r9 : F := cells.main 1
  let r10 : F := cells.main 2
  let r11 : F := cells.main 3
  let r12 : F := cells.main 4
  let r13 : F := cells.main 5
  let r14 : F := cells.main 6
  let r15 : F := cells.main 7
  let r16 : F := cells.main 8
  let r17 : F := cells.main 9
  let r18 : F := cells.main 10
  let r19 : F := cells.main 11
  let r20 : F := r0 + r3
  let r21 : F := r20 + r1
  let r22 : F := r21 + r2
  let r23 : F := 1
  let r24 : F := r22 - r23
  let r25 : F := 0
  let r26 : F := 1
  let r27 : F := r0 - r26
  let r28 : F := r0 * r27
  let r29 : F := 1
  let r30 : F := r3 - r29
  let r31 : F := r3 * r30
  let r32 : F := 1
  let r33 : F := r1 - r32
  let r34 : F := r1 * r33
  let r35 : F := 1
  let r36 : F := r2 - r35
  let r37 : F := r2 * r36
  let r38 : F := r8 * r12
  let r39 : F := r9 * r13
  let r40 : F := r38 - r39
  let r41 : F := r10 * r14
  let r42 : F := r11 * r15
  let r43 : F := r41 - r42
  let r44 : F := 2
  let r45 : F := r44 * r43
  let r46 : F := r40 + r45
  let r47 : F := r10 * r15
  let r48 : F := r46 - r47
  let r49 : F := r11 * r14
  let r50 : F := r48 - r49
  let r51 : F := r50 * r1
  let r52 : F := r8 + r12
  let r53 : F := r52 * r0
  let r54 : F := r51 + r53
  let r55 : F := r8 - r12
  let r56 : F := r55 * r3
  let r57 : F := r54 + r56
  let r58 : F := r8 * r12
  let r59 : F := r58 * r2
  let r60 : F := r57 + r59
  let r61 : F := r16 - r60
  let r62 : F := r8 * r13
  let r63 : F := r9 * r12
  let r64 : F := r62 + r63
  let r65 : F := r10 * r15
  let r66 : F := r11 * r14
  let r67 : F := r65 + r66
  let r68 : F := 2
  let r69 : F := r68 * r67
  let r70 : F := r64 + r69
  let r71 : F := r10 * r14
  let r72 : F := r70 + r71
  let r73 : F := r11 * r15
  let r74 : F := r72 - r73
  let r75 : F := r74 * r1
  let r76 : F := r9 + r13
  let r77 : F := r76 * r0
  let r78 : F := r75 + r77
  let r79 : F := r9 - r13
  let r80 : F := r79 * r3
  let r81 : F := r78 + r80
  let r82 : F := r9 * r13
  let r83 : F := r82 * r2
  let r84 : F := r81 + r83
  let r85 : F := r17 - r84
  let r86 : F := r8 * r14
  let r87 : F := r9 * r15
  let r88 : F := r86 - r87
  let r89 : F := r10 * r12
  let r90 : F := r88 + r89
  let r91 : F := r11 * r13
  let r92 : F := r90 - r91
  let r93 : F := r92 * r1
  let r94 : F := r10 + r14
  let r95 : F := r94 * r0
  let r96 : F := r93 + r95
  let r97 : F := r10 - r14
  let r98 : F := r97 * r3
  let r99 : F := r96 + r98
  let r100 : F := r10 * r14
  let r101 : F := r100 * r2
  let r102 : F := r99 + r101
  let r103 : F := r18 - r102
  let r104 : F := r8 * r15
  let r105 : F := r9 * r14
  let r106 : F := r104 + r105
  let r107 : F := r10 * r13
  let r108 : F := r106 + r107
  let r109 : F := r11 * r12
  let r110 : F := r108 + r109
  let r111 : F := r110 * r1
  let r112 : F := r11 + r15
  let r113 : F := r112 * r0
  let r114 : F := r111 + r113
  let r115 : F := r11 - r15
  let r116 : F := r115 * r3
  let r117 : F := r114 + r116
  let r118 : F := r11 * r15
  let r119 : F := r118 * r2
  let r120 : F := r117 + r119
  let r121 : F := r19 - r120
  return [r24, r28, r31, r34, r37, r61, r85, r103, r121]

/-- Universal M31 arithmetic correspondence for the selected
installed bytecode prefix; LogUp roots 9–10 remain separate. -/
theorem bytecode_arithmetic_eq (cells : Cells) :
    bytecodeArithmetic cells = arithmetic cells := by
  simp [bytecodeArithmetic, arithmetic, decodedRow, semanticFixed,
    S31.Gadgets.Air.NativeQm31Air.residuals,
    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal]

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
