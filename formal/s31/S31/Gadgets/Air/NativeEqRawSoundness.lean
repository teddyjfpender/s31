import S31.Gadgets.Air.NativeGateRawSoundness
import S31.Gadgets.Air.GateEqRawSoundness

namespace S31.Gadgets.Air.NativeEqRawSoundness
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.NativeGateRawSoundness
open S31.Gadgets.Air.GateEqRawSoundness
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.EqGateInteraction
open S31.Gadgets.Air.EqRows
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.NativeLogUpAirProof

abbrev Event := S31.Gadgets.Air.GateLookup.Event

def nativeEqPair (row : EqRow) (alpha z : GateSecure) :=
  (nativeUseTerm (row.leftAddress, row.value) alpha z,
    nativeUseTerm (row.rightAddress, row.value) alpha z)

theorem native_eq_pair_eq (row : EqRow) (alpha z : GateSecure) :
    nativeEqPair row alpha z = eqPair row alpha z := by
  simp [nativeEqPair, eqPair, native_use_term_eq]

/-- Arithmetic and Eq raw interaction equations using the source-extracted
Gate key and LogUp residual builders. External component sums remain modeled. -/
def nativeCombinedRawAccepts (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → S31.Gadgets.Air.GateLookup.Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) : Prop :=
  ∃ arithFirst arithLast : Fin (2 ^ arithLogSize) → GateSecure,
  ∃ eqColumn : Fin (2 ^ eqLogSize) → GateSecure,
  ∃ arithClaim eqClaim : GateSecure,
    (∀ i, NativeLogUpAir.pair
      (nativeRowPair (arithRows i) alpha z).1
      (nativeRowPair (arithRows i) alpha z).2 (arithFirst i) = 0) ∧
    (∀ i, NativeLogUpAir.single
      (nativeYieldTerm (arithRows i) alpha z)
      (arithLast i - arithLast (arithPrev i) - arithFirst i +
        arithClaim / ((2 ^ arithLogSize : Nat) : GateSecure)) = 0) ∧
    (∀ i, NativeLogUpAir.pair
      (nativeEqPair (eqRows i) alpha z).1
      (nativeEqPair (eqRows i) alpha z).2
      (eqColumn i - eqColumn (eqPrev i) +
        eqClaim / ((2 ^ eqLogSize : Nat) : GateSecure)) = 0) ∧
    arithClaim + eqClaim +
      productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

theorem native_combined_raw_accepts_iff (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → S31.Gadgets.Air.GateLookup.Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) :
    nativeCombinedRawAccepts arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields alpha z ↔
      combinedRawAccepts arithLogSize eqLogSize arithPrev eqPrev
        arithRows eqRows externalUses externalYields alpha z := by
  simp only [nativeCombinedRawAccepts, combinedRawAccepts,
    native_row_pair_eq, native_yield_term_eq, native_eq_pair_eq,
    native_pair_eq, native_single_eq]

theorem native_combined_accepts_only_exceptional
    (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → S31.Gadgets.Air.GateLookup.Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (haccept : nativeCombinedRawAccepts arithLogSize eqLogSize
      arithPrev eqPrev arithRows eqRows
      externalUses externalYields alpha z) :
    (alpha, z) ∈
      S31.Gadgets.Air.GateAirRawSoundness.exceptionalPairs
        (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
        externalYields := by
  classical
  apply combined_accepting_pairs_subset_exceptional arithLogSize eqLogSize
    arithPrev eqPrev arithRows eqRows externalUses externalYields
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (native_combined_raw_accepts_iff arithLogSize eqLogSize
      arithPrev eqPrev arithRows eqRows
      externalUses externalYields alpha z).mp haccept⟩

end S31.Gadgets.Air.NativeEqRawSoundness
