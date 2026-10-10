import S31.Gadgets.Air.DecodedDirectGateTrace
import S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-!
The direct Gate component stores its eight fixed columns in semantic order,
but the selected captured AIR reads them in local order
`[0, 2, 3, 1, 4, 5, 6, 7]`. Its final interaction column also reads the
previous *coset* row after bit reversal, not the previous storage index.

These are pure index identities. The premise that the installed bundle uses
this local read vector, and the premise that the native mask implements the
source predecessor, are still external to Lean. No PCS/FRI claim is made.
-/

namespace S31.Gadgets.Air.DirectGateNativeIndices

open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-- Position in the selected AIR's local fixed-column list to semantic
position in `DecodedDirectGateTrace.fixed`. -/
def airLocalToSemantic (i : Fin 8) : Fin 8 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 7

def semanticToAirLocal (i : Fin 8) : Fin 8 :=
  match i.val with
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | _ => 7

theorem local_semantic_inverse :
    ∀ i : Fin 8, semanticToAirLocal (airLocalToSemantic i) = i := by
  intro i
  fin_cases i <;> rfl

theorem semantic_local_inverse :
    ∀ i : Fin 8, airLocalToSemantic (semanticToAirLocal i) = i := by
  intro i
  fin_cases i <;> rfl

def fixedReadOrder : Fin 8 ≃ Fin 8 where
  toFun := airLocalToSemantic
  invFun := semanticToAirLocal
  left_inv := local_semantic_inverse
  right_inv := semantic_local_inverse

/-- A local captured-AIR fixed-column read, assuming the manifest's local
index list is exactly `fixedReadOrder`. -/
def airLocalFixed {logSize : Nat}
    (trace : DecodedDirectGateTrace logSize)
    (row : Fin (2 ^ logSize)) (local : Fin 8) :
    S31.Gadgets.Packed.F :=
  trace.fixed row (fixedReadOrder local)

theorem local_fixed_at_semantic {logSize : Nat}
    (trace : DecodedDirectGateTrace logSize)
    (row : Fin (2 ^ logSize)) (semantic : Fin 8) :
    airLocalFixed trace row (fixedReadOrder.symm semantic) =
      trace.fixed row semantic := by
  simp [airLocalFixed]

/-- The equal-size-domain predecessor for any even direct trace size.
The bit-reversal implementation is supplied with its involution law, so
this definition does not claim a Zig machine-word theorem. -/
def directPrevious (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (hinvolution : ∀ row,
      bitReverseIndex (bitReverseIndex row) = row) :
    Equiv.Perm (Fin (2 * m)) :=
  nativePrevMask m hm
    (bitReverseEquivOfInvolution bitReverseIndex hinvolution)

theorem direct_previous_source_formula (m : Nat) (hm : 0 < m)
    (bitReverseIndex : Fin (2 * m) → Fin (2 * m))
    (hinvolution : ∀ row,
      bitReverseIndex (bitReverseIndex row) = row)
    (row : Fin (2 * m)) :
    directPrevious m hm bitReverseIndex hinvolution row =
      sourcePreviousIndex m hm bitReverseIndex row := by
  rfl

/-- Direct sixteen-row fixture specialization. The remaining native
obligation is to match `utils.bitReverseIndex` and the installed `at_prev`
mask to this function. -/
def directPrevious16 : Equiv.Perm (Fin 16) :=
  directPrevious 8 (by decide) bitReverse4 bitReverse4_involutive

theorem direct_previous16_source_formula (row : Fin 16) :
    directPrevious16 row =
      bitReverse4 (cosetToCircleIndex 8
        (cosetPrevEquiv 8 (by decide)
          (circleToCosetIndex 8 (bitReverse4 row)))) := by
  rfl

theorem direct_previous16_bijective :
    Function.Bijective directPrevious16 :=
  directPrevious16.bijective

/-- This premise must come from the selected native mask and trace order;
it is not inferred from an arbitrary decoded trace. -/
def PreviousMaskMatches (trace : DecodedDirectGateTrace 4) : Prop :=
  trace.prev = directPrevious16

theorem decoded_last_at_previous16
    (trace : DecodedDirectGateTrace 4)
    (hmask : PreviousMaskMatches trace) (row : Fin 16) :
    lastColumn trace (trace.prev row) =
      lastColumn trace (directPrevious16 row) := by
  change trace.prev = directPrevious16 at hmask
  rw [hmask]

end S31.Gadgets.Air.DirectGateNativeIndices
