import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
import S31.Gadgets.Air.DirectGateNativeIndices

/-!
Concrete 512-row previous-mask index and the selected Gate bytecode's OODS
sample positions. This models index/slot selection, not authenticated proof
openings or the Zig machine-word implementation of `@bitReverse`.
-/

namespace S31.Gadgets.Air.DirectGateOodsMask

open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-- Reverse exactly the nine significant index bits of a 512-row Gate trace. -/
def bitReverse9 (row : Fin 512) : Fin 512 :=
  ⟨(BitVec.ofNat 9 row.val).reverse.toNat, by
    have h := (BitVec.ofNat 9 row.val).reverse.isLt
    omega⟩

theorem bitReverse9_involutive :
    ∀ row : Fin 512, bitReverse9 (bitReverse9 row) = row := by
  intro row
  apply Fin.ext
  simp [bitReverse9, BitVec.ofNat_toNat]

/-- Arithmetic expansion of the nine-bit reversal used by the independent
native exhaustive test's bit loop. -/
def reverseNineArithmetic (value : Nat) : Nat :=
  256 * (value % 2) + 128 * (value / 2 % 2) +
  64 * (value / 4 % 2) + 32 * (value / 8 % 2) +
  16 * (value / 16 % 2) + 8 * (value / 32 % 2) +
  4 * (value / 64 % 2) + 2 * (value / 128 % 2) +
  value / 256 % 2

set_option maxRecDepth 10000 in
theorem bitReverse9_eq_arithmetic :
    ∀ row : Fin 512,
      (bitReverse9 row).val = reverseNineArithmetic row.val := by
  decide

def directPrevious512 : Equiv.Perm (Fin 512) :=
  directPrevious 256 (by decide) bitReverse9 bitReverse9_involutive

/-- The equal-size branch of `previousBitReversedCircleDomainIndex` at the
direct Gate trace's 512-row shape. Matching Zig's bit reverse and circle
index functions to this arithmetic definition remains source correspondence. -/
theorem direct_previous512_formula (row : Fin 512) :
    directPrevious512 row =
      bitReverse9 (cosetToCircleIndex 256
        (cosetPrevEquiv 256 (by decide)
          (circleToCosetIndex 256 (bitReverse9 row)))) := by
  rfl

theorem direct_previous512_bijective :
    Function.Bijective directPrevious512 :=
  directPrevious512.bijective

/-- Row-level analogue of the selected interaction opening mask. This is a
model of which source rows an offset requests, not a claim that an OODS
opening equals a row value. -/
def rowMask (trace : Fin 512 → Fin 8 → QM) (row : Fin 512)
    (column : Fin 8) : List QM :=
  if column.val < 4 then [trace row column]
  else [trace (directPrevious512 row) column, trace row column]

theorem row_mask_previous (trace : Fin 512 → Fin 8 → QM)
    (row : Fin 512) (column : Fin 8) (h : 4 ≤ column.val) :
    interactionMaskRead (rowMask trace row) column (-1) =
      some (trace (directPrevious512 row) column) := by
  fin_cases column <;>
    simp_all [interactionMaskRead, interactionOffsets, offsetIndex, rowMask]

theorem row_mask_current (trace : Fin 512 → Fin 8 → QM)
    (row : Fin 512) (column : Fin 8) :
    interactionMaskRead (rowMask trace row) column 0 =
      some (trace row column) := by
  fin_cases column <;>
    simp_all [interactionMaskRead, interactionOffsets, offsetIndex, rowMask]

/-- Shape-preserving model of the two cases in native
`verifier_proof.zig`: one sample becomes `at_oods`; two ordered samples
become `(at_prev, at_oods)` before being stored as `(at_oods, at_prev)`. -/
def proofWireOfSamples : List QM → Option (QM × Option QM)
  | [oods] => some (oods, none)
  | [previous, oods] => some (oods, some previous)
  | _ => none

theorem row_mask_proof_wire (trace : Fin 512 → Fin 8 → QM)
    (row : Fin 512) (column : Fin 8) :
    proofWireOfSamples (rowMask trace row column) =
      some (trace row column,
        if column.val < 4 then none
        else some (trace (directPrevious512 row) column)) := by
  fin_cases column <;> simp [proofWireOfSamples, rowMask]

/-- An OODS sample at offset `-1` is requested at the point shifted by the
negative trace step; the selected last interaction columns request that
offset in slot zero and the current point in slot one. -/
def shiftedPoint {P : Type*} [AddGroup P] (oods traceStep : P)
    (offset : Int) : P :=
  oods + offset • traceStep

def sampledPoint {P : Type*} [AddGroup P] (oods traceStep : P)
    (column : Fin 8) (slot : Nat) : Option P :=
  (interactionOffsets column)[slot]?.map (shiftedPoint oods traceStep)

theorem last_sample_points {P : Type*} [AddGroup P]
    (oods traceStep : P) (column : Fin 8) (h : 4 ≤ column.val) :
    sampledPoint oods traceStep column 0 = some (oods - traceStep) ∧
      sampledPoint oods traceStep column 1 = some oods := by
  fin_cases column <;>
    simp_all [sampledPoint, interactionOffsets, shiftedPoint, sub_eq_add_neg]

end S31.Gadgets.Air.DirectGateOodsMask
