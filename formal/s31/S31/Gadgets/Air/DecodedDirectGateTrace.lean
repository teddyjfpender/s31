import S31.Gadgets.Air.NativeGateRawSoundness

/-!
An interface for the next native direct-Gate correspondence step. It decodes
the eight fixed, twelve main, and eight interaction M31 cells of each logical
`qm31_ops` row. `airPair` and `airLast` stand for outputs of the *selected
production evaluator* at those cells. The two evaluator equalities and the
all-row zero premise below are obligations, not facts established here by the
native verifier or its PCS/FRI proof.
-/

namespace S31.Gadgets.Air.DecodedDirectGateTrace

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.NativeGateRawSoundness

abbrev Event := GateLookup.Event

/-- An abstract view of the exact direct-profile column geometry. The row
permutation, selected evaluator outputs, and external event lists must be
bound to the installed key and proof by a separate native/PCS argument. -/
structure Trace (logSize : Nat) where
  fixed : Fin (2 ^ logSize) → Fin 8 → F
  main : Fin (2 ^ logSize) → Fin 12 → F
  interaction : Fin (2 ^ logSize) → Fin 8 → F
  prev : Equiv.Perm (Fin (2 ^ logSize))
  airPair : Fin (2 ^ logSize) → GateSecure
  airLast : Fin (2 ^ logSize) → GateSecure
  claimed : GateSecure
  externalUses : List Event
  externalYields : List Event

def row {logSize : Nat} (trace : Trace logSize)
    (i : Fin (2 ^ logSize)) : Row :=
  { in0Address := (trace.fixed i 4).val,
    in1Address := (trace.fixed i 5).val,
    outAddress := (trace.fixed i 6).val,
    flags := ⟨trace.fixed i 0, trace.fixed i 1,
      trace.fixed i 2, trace.fixed i 3⟩,
    in0 := ⟨trace.main i 0, trace.main i 1,
      trace.main i 2, trace.main i 3⟩,
    in1 := ⟨trace.main i 4, trace.main i 5,
      trace.main i 6, trace.main i 7⟩,
    output := ⟨trace.main i 8, trace.main i 9,
      trace.main i 10, trace.main i 11⟩,
    multiplicity := (trace.fixed i 7).val }

def firstColumn {logSize : Nat} (trace : Trace logSize)
    (i : Fin (2 ^ logSize)) : GateSecure :=
  ⟨⟨trace.interaction i 0, trace.interaction i 1⟩,
    ⟨trace.interaction i 2, trace.interaction i 3⟩⟩

def lastColumn {logSize : Nat} (trace : Trace logSize)
    (i : Fin (2 ^ logSize)) : GateSecure :=
  ⟨⟨trace.interaction i 4, trace.interaction i 5⟩,
    ⟨trace.interaction i 6, trace.interaction i 7⟩⟩

/-- Conditional bridge from decoded cells to the existing raw Gate model.

`hPairEvaluator` and `hLastEvaluator` assert that the selected production AIR
program, at every decoded row, emits the source-extracted two-lookup and
singleton residuals. `hAuthenticatedRows` is the **cryptographic** obligation:
verifier acceptance must imply zero evaluator outputs for one trace bound to
the three commitments, except with the separately quantified PCS/FRI error.
`hPublicClosure` is the verifier's claimed-sum check, after independently
matching its public tuples and signs to these external lists. None of these
three links follows merely from this structure's existence. -/
theorem decoded_cells_to_raw_accepts {logSize : Nat}
    (trace : Trace logSize)
    (alpha z : GateSecure)
    (hPairEvaluator : ∀ i,
      trace.airPair i = NativeLogUpAir.pair
        (nativeRowPair (row trace i) alpha z).1
        (nativeRowPair (row trace i) alpha z).2
        (firstColumn trace i))
    (hLastEvaluator : ∀ i,
      trace.airLast i = NativeLogUpAir.single
        (nativeYieldTerm (row trace i) alpha z)
        (lastColumn trace i - lastColumn trace (trace.prev i) -
          firstColumn trace i +
          trace.claimed / ((2 ^ logSize : Nat) : GateSecure)))
    (hAuthenticatedRows : ∀ i,
      trace.airPair i = 0 ∧ trace.airLast i = 0)
    (hPublicClosure : trace.claimed +
      productionReciprocalSum trace.externalUses alpha z -
      productionReciprocalSum trace.externalYields alpha z = 0) :
    rawInteractionAccepts logSize trace.prev (row trace)
      trace.externalUses trace.externalYields alpha z := by
  apply (native_raw_accepts_iff logSize trace.prev (row trace)
    trace.externalUses trace.externalYields alpha z).mp
  refine ⟨firstColumn trace, lastColumn trace, trace.claimed, ?_, ?_,
    hPublicClosure⟩
  · intro i
    rw [← hPairEvaluator i]
    exact (hAuthenticatedRows i).1
  · intro i
    rw [← hLastEvaluator i]
    exact (hAuthenticatedRows i).2

end S31.Gadgets.Air.DecodedDirectGateTrace
