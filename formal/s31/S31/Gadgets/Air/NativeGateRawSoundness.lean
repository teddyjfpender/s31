import S31.Gadgets.Air.NativeLogUpAirProof
import S31.Gadgets.Air.GateAirRawSoundness

namespace S31.Gadgets.Air.NativeGateRawSoundness
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.NativeLogUpAirProof

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- Rebuild Gate terms from the source-extracted native key polynomial. -/
def nativeUseTerm (event : Event) (alpha z : GateSecure) :
    S31.Gadgets.Air.LogUpInteraction.Term GateSecure :=
  { numerator := 1,
    denominator := NativeLogUpAir.combine (eventTuple event) alpha z }

def nativeYieldTerm (row : S31.Gadgets.Air.GateLookup.Row)
    (alpha z : GateSecure) :
    S31.Gadgets.Air.LogUpInteraction.Term GateSecure :=
  { numerator := -(row.multiplicity : GateSecure),
    denominator := NativeLogUpAir.combine
      (eventTuple (row.outAddress, row.output)) alpha z }

def nativeRowPair (row : S31.Gadgets.Air.GateLookup.Row)
    (alpha z : GateSecure) :
    S31.Gadgets.Air.LogUpInteraction.Term GateSecure ×
      S31.Gadgets.Air.LogUpInteraction.Term GateSecure :=
  (nativeUseTerm (row.in0Address, row.in0) alpha z,
    nativeUseTerm (row.in1Address, row.in1) alpha z)

theorem native_use_term_eq (event : Event) (alpha z : GateSecure) :
    nativeUseTerm event alpha z = useTerm event alpha z := by
  simp [nativeUseTerm, useTerm, native_combine_eq]

theorem native_yield_term_eq (row : S31.Gadgets.Air.GateLookup.Row)
    (alpha z : GateSecure) :
    nativeYieldTerm row alpha z = yieldTerm row alpha z := by
  simp [nativeYieldTerm, yieldTerm, native_combine_eq]

theorem native_row_pair_eq (row : S31.Gadgets.Air.GateLookup.Row)
    (alpha z : GateSecure) :
    nativeRowPair row alpha z = rowPair row alpha z := by
  simp [nativeRowPair, rowPair, native_use_term_eq]

/-- The raw Gate AIR acceptance statement with residuals generated from the
production Zig LogUp builder. The external Gate contribution is still a
modeled sum, rather than a source-extracted component AIR. -/
def nativeRawInteractionAccepts (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → S31.Gadgets.Air.GateLookup.Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) : Prop :=
  ∃ firstColumn lastColumn : Fin (2 ^ logSize) → GateSecure,
  ∃ claimed : GateSecure,
    (∀ i, NativeLogUpAir.pair (nativeRowPair (rows i) alpha z).1
      (nativeRowPair (rows i) alpha z).2 (firstColumn i) = 0) ∧
    (∀ i, NativeLogUpAir.single (nativeYieldTerm (rows i) alpha z)
      (lastColumn i - lastColumn (prev i) - firstColumn i +
        claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) ∧
    claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

theorem native_raw_accepts_iff (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → S31.Gadgets.Air.GateLookup.Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) :
    nativeRawInteractionAccepts logSize prev rows
      externalUses externalYields alpha z ↔
      rawInteractionAccepts logSize prev rows
        externalUses externalYields alpha z := by
  simp only [nativeRawInteractionAccepts, rawInteractionAccepts,
    native_row_pair_eq, native_yield_term_eq,
    native_pair_eq, native_single_eq]

/-- Outside the explicit collision and zero-denominator exceptional set,
source-extracted Gate residuals cannot close a fixed invalid multiset. -/
theorem native_raw_accepts_only_exceptional (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → S31.Gadgets.Air.GateLookup.Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (haccept : nativeRawInteractionAccepts logSize prev rows
      externalUses externalYields alpha z) :
    (alpha, z) ∈ exceptionalPairs (List.ofFn rows)
      externalUses externalYields := by
  classical
  apply raw_accepting_pairs_subset_exceptional logSize prev rows
    externalUses externalYields
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (native_raw_accepts_iff logSize prev rows
      externalUses externalYields alpha z).mp haccept⟩

end S31.Gadgets.Air.NativeGateRawSoundness
