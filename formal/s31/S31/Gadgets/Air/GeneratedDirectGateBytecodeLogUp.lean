-- Generated from checked STWZEVA/1 qm31_ops LogUp roots 9–10.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Sample authentication and OODS shift provenance remain separate.
import S31.Gadgets.Air.DirectGateOodsLogUp

namespace S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp

set_option linter.unusedVariables false

/-- Unique offsets in bytecode instruction order, as used by native
`resident_geometry.componentOffsets` and `traceValue`. -/
def interactionOffsets (column : Fin 8) : List Int :=
  match column.val with
  | 0 => [0]
  | 1 => [0]
  | 2 => [0]
  | 3 => [0]
  | 4 => [-1, 0]
  | 5 => [-1, 0]
  | 6 => [-1, 0]
  | 7 => [-1, 0]
  | _ => []

/-- Native `offsetIndex` returns the first matching sample slot. -/
def offsetIndex : List Int → Int → Option Nat
  | [], _ => none
  | first :: rest, wanted =>
      if first == wanted then some 0 else (offsetIndex rest wanted).map (· + 1)

def interactionMaskRead (samples : Fin 8 → List QM)
    (column : Fin 8) (offset : Int) : Option QM :=
  (offsetIndex (interactionOffsets column) offset).bind fun index =>
    (samples column)[index]?

/-- For columns 4–7, native `at_prev` is sample slot zero and
`at_oods` is sample slot one; columns 0–3 have only `at_oods`. -/
theorem mask_slots (column : Fin 8) :
    (if column.val < 4 then
      interactionOffsets column = [0] ∧
        offsetIndex (interactionOffsets column) 0 = some 0 ∧
        offsetIndex (interactionOffsets column) (-1) = none
    else
      interactionOffsets column = [-1, 0] ∧
        offsetIndex (interactionOffsets column) (-1) = some 0 ∧
        offsetIndex (interactionOffsets column) 0 = some 1) := by
  fin_cases column <;> decide

/-- The selected previous/current roots use precisely these two
sample positions for each last-column limb. -/
theorem last_mask_reads (samples : Fin 8 → List QM)
    (column : Fin 8) (h : 4 ≤ column.val) :
    interactionMaskRead samples column (-1) = (samples column)[0]? ∧
      interactionMaskRead samples column 0 = (samples column)[1]? := by
  fin_cases column <;> simp_all [interactionMaskRead, interactionOffsets, offsetIndex]

/-- Native base registers execute in QM31 at an OODS point. The
seven extension parameters are `[α, α², α³, α⁴, α⁵, z, claimedScaled]`. -/
def bytecodeLogup (cells : Cells) (alpha z claimedScaled : QM) :
    QM × QM := Id.run do
  let r4 : QM := cells.localFixed 4
  let r5 : QM := cells.localFixed 5
  let r6 : QM := cells.localFixed 6
  let r7 : QM := cells.localFixed 7
  let r8 : QM := cells.main 0
  let r9 : QM := cells.main 1
  let r10 : QM := cells.main 2
  let r11 : QM := cells.main 3
  let r12 : QM := cells.main 4
  let r13 : QM := cells.main 5
  let r14 : QM := cells.main 6
  let r15 : QM := cells.main 7
  let r16 : QM := cells.main 8
  let r17 : QM := cells.main 9
  let r18 : QM := cells.main 10
  let r19 : QM := cells.main 11
  let r25 : QM := 0
  let r122 : QM := cells.interaction 0
  let r123 : QM := cells.interaction 1
  let r124 : QM := cells.interaction 2
  let r125 : QM := cells.interaction 3
  let r126 : QM := cells.previousInteraction 4
  let r127 : QM := cells.interaction 4
  let r128 : QM := cells.previousInteraction 5
  let r129 : QM := cells.interaction 5
  let r130 : QM := cells.previousInteraction 6
  let r131 : QM := cells.interaction 6
  let r132 : QM := cells.previousInteraction 7
  let r133 : QM := cells.interaction 7
  let e9 : QM := alpha ^ 1
  let e10 : QM := fromPartialEvals r4 r25 r25 r25
  let e11 : QM := e9 * e10
  let e12 : QM := 378353459
  let e13 : QM := e12 + e11
  let e14 : QM := alpha ^ 2
  let e15 : QM := fromPartialEvals r8 r25 r25 r25
  let e16 : QM := e14 * e15
  let e17 : QM := e13 + e16
  let e18 : QM := alpha ^ 3
  let e19 : QM := fromPartialEvals r9 r25 r25 r25
  let e20 : QM := e18 * e19
  let e21 : QM := e17 + e20
  let e22 : QM := alpha ^ 4
  let e23 : QM := fromPartialEvals r10 r25 r25 r25
  let e24 : QM := e22 * e23
  let e25 : QM := e21 + e24
  let e26 : QM := alpha ^ 5
  let e27 : QM := fromPartialEvals r11 r25 r25 r25
  let e28 : QM := e26 * e27
  let e29 : QM := e25 + e28
  let e30 : QM := z
  let e31 : QM := e29 - e30
  let e32 : QM := alpha ^ 1
  let e33 : QM := fromPartialEvals r5 r25 r25 r25
  let e34 : QM := e32 * e33
  let e35 : QM := 378353459
  let e36 : QM := e35 + e34
  let e37 : QM := alpha ^ 2
  let e38 : QM := fromPartialEvals r12 r25 r25 r25
  let e39 : QM := e37 * e38
  let e40 : QM := e36 + e39
  let e41 : QM := alpha ^ 3
  let e42 : QM := fromPartialEvals r13 r25 r25 r25
  let e43 : QM := e41 * e42
  let e44 : QM := e40 + e43
  let e45 : QM := alpha ^ 4
  let e46 : QM := fromPartialEvals r14 r25 r25 r25
  let e47 : QM := e45 * e46
  let e48 : QM := e44 + e47
  let e49 : QM := alpha ^ 5
  let e50 : QM := fromPartialEvals r15 r25 r25 r25
  let e51 : QM := e49 * e50
  let e52 : QM := e48 + e51
  let e53 : QM := z
  let e54 : QM := e52 - e53
  let e55 : QM := fromPartialEvals r7 r25 r25 r25
  let e56 : QM := -e55
  let e57 : QM := alpha ^ 1
  let e58 : QM := fromPartialEvals r6 r25 r25 r25
  let e59 : QM := e57 * e58
  let e60 : QM := 378353459
  let e61 : QM := e60 + e59
  let e62 : QM := alpha ^ 2
  let e63 : QM := fromPartialEvals r16 r25 r25 r25
  let e64 : QM := e62 * e63
  let e65 : QM := e61 + e64
  let e66 : QM := alpha ^ 3
  let e67 : QM := fromPartialEvals r17 r25 r25 r25
  let e68 : QM := e66 * e67
  let e69 : QM := e65 + e68
  let e70 : QM := alpha ^ 4
  let e71 : QM := fromPartialEvals r18 r25 r25 r25
  let e72 : QM := e70 * e71
  let e73 : QM := e69 + e72
  let e74 : QM := alpha ^ 5
  let e75 : QM := fromPartialEvals r19 r25 r25 r25
  let e76 : QM := e74 * e75
  let e77 : QM := e73 + e76
  let e78 : QM := z
  let e79 : QM := e77 - e78
  let e80 : QM := 1
  let e81 : QM := e54 * e80
  let e82 : QM := 1
  let e83 : QM := e31 * e82
  let e84 : QM := e81 + e83
  let e85 : QM := e31 * e54
  let e86 : QM := fromPartialEvals r122 r123 r124 r125
  let e87 : QM := e86 * e85
  let e88 : QM := e87 - e84
  let e89 : QM := fromPartialEvals r126 r128 r130 r132
  let e90 : QM := fromPartialEvals r127 r129 r131 r133
  let e91 : QM := e90 - e89
  let e92 : QM := e91 - e86
  let e93 : QM := claimedScaled
  let e94 : QM := e92 + e93
  let e95 : QM := e94 * e79
  let e96 : QM := e95 - e56
  return (e88, e96)

/-- Polynomial equality of the installed LogUp root pair over
arbitrary QM31 fixed, main, and interaction samples. -/
theorem bytecode_logup_eq (cells : Cells) (alpha z claimedScaled : QM) :
    bytecodeLogup cells alpha z claimedScaled =
      (pair cells alpha z, last cells alpha z claimedScaled) := by
  dsimp [bytecodeLogup, pair, last, inputZeroDenominator,
    inputOneDenominator, outputDenominator, denominator,
    firstColumn, lastColumn, previousLastColumn]
  simp only [fromPartialEvals_three_zero, pow_succ, Prod.mk.injEq]
  constructor <;> ring

end S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
