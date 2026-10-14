import S31.Gadgets.Air.CompositionFold
import S31.Gadgets.Air.NativeGateRawSoundness

/-!
The production `finalizeLogupInPairs` appends the two Gate interaction
residuals after the nine local arithmetic residuals.  This module uses its
source-exported expression, not an independently written finalizer formula.
The samples here are fixed field values; authenticating them as evaluations
of proof-committed low-degree columns is a separate PCS/AIR obligation.
-/

namespace S31.Gadgets.Air.NativeGateFinalizerBridge

open Polynomial
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.NativeGateRawSoundness
open S31.Gadgets.Air.NativeLogUpBatches
open S31.Gadgets.Air.NativeLogUpBatchesProof
open S31.Gadgets.Air.CompositionFold

/-- Exactly the native Gate row's nine arithmetic and two LogUp residuals,
using the source-extracted Gate key and the native pair/single term order. -/
def rowConstraints (row : Row) (alpha z : GateSecure)
    (first previous last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure) : List GateSecure :=
  qm31RowConstraints row.flags row.in0 row.in1 row.output
    (nativeRowPair row alpha z).1 (nativeRowPair row alpha z).2
    (nativeYieldTerm row alpha z) first previous last claimed nInstances

/-- The full source-extracted Gate finalizer, including its arithmetic prefix,
is the Horner fold of the eleven residuals above. -/
theorem native_finalizer_eq_fold (row : Row) (alpha z : GateSecure)
    (first previous last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure) :
    threeTermWithPrefix
      (fold rho ((S31.Gadgets.Air.NativeQm31Air.residuals
        row.flags row.in0 row.in1 row.output).map
          S31.Gadgets.Air.GateChallenge.liftBase))
      (nativeRowPair row alpha z).1 (nativeRowPair row alpha z).2
      (nativeYieldTerm row alpha z) first previous last rho claimed nInstances =
    fold rho (rowConstraints row alpha z first previous last claimed nInstances) := by
  exact (qm31_row_fold_eq_native_tail row.flags row.in0 row.in1 row.output
    (nativeRowPair row alpha z).1 (nativeRowPair row alpha z).2
    (nativeYieldTerm row alpha z) first previous last rho claimed nInstances).symm

/-- When this fixed row is invalid, at most ten composition coefficients can
make its eleven-residual fold vanish.  The set is empty for a valid row. -/
noncomputable def badCoefficients (row : Row) (alpha z : GateSecure)
    (first previous last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure) : Finset GateSecure :=
  let residuals := rowConstraints row alpha z first previous last claimed nInstances
  if polynomial residuals = 0 then ∅ else (polynomial residuals).roots.toFinset

theorem bad_coefficients_card_le_ten (row : Row) (alpha z : GateSecure)
    (first previous last : Fin 4 → GateSecure)
    (claimed nInstances : GateSecure) :
    (badCoefficients row alpha z first previous last claimed nInstances).card ≤ 10 := by
  classical
  by_cases hzero : polynomial
      (rowConstraints row alpha z first previous last claimed nInstances) = 0
  · simp [badCoefficients, hzero]
  · have hbad : ∃ r ∈ rowConstraints row alpha z first previous last claimed nInstances,
        r ≠ 0 := by
      by_contra h
      push Not at h
      exact hzero ((polynomial_eq_zero_iff _).mpr h)
    have hbound := qm31_row_bad_coeff_roots_card_le_ten
      row.flags row.in0 row.in1 row.output
      (nativeRowPair row alpha z).1 (nativeRowPair row alpha z).2
      (nativeYieldTerm row alpha z) first previous last claimed nInstances hbad
    change (if polynomial
      (rowConstraints row alpha z first previous last claimed nInstances) = 0
      then (∅ : Finset GateSecure)
      else (polynomial
        (rowConstraints row alpha z first previous last claimed nInstances)).roots.toFinset).card ≤ 10
    rw [if_neg hzero]
    exact (Multiset.toFinset_card_le _).trans hbound

/-- A zero native fold outside the row's explicit root set means every
arithmetic and interaction residual is zero.  This is a fixed-sample algebraic
statement, before OODS/PCS authentication and Fiat--Shamir analysis. -/
theorem finalizer_zero_implies_all_residuals (row : Row) (alpha z : GateSecure)
    (first previous last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure)
    (hfinal : threeTermWithPrefix
      (fold rho ((S31.Gadgets.Air.NativeQm31Air.residuals
        row.flags row.in0 row.in1 row.output).map
          S31.Gadgets.Air.GateChallenge.liftBase))
      (nativeRowPair row alpha z).1 (nativeRowPair row alpha z).2
      (nativeYieldTerm row alpha z) first previous last rho claimed nInstances = 0)
    (hgood : rho ∉ badCoefficients row alpha z first previous last
      claimed nInstances) :
    ∀ residual ∈ rowConstraints row alpha z first previous last
      claimed nInstances, residual = 0 := by
  classical
  let rs := rowConstraints row alpha z first previous last claimed nInstances
  have hfold : fold rho rs = 0 := by
    rw [← native_finalizer_eq_fold]
    exact hfinal
  by_cases hzero : polynomial rs = 0
  · exact (polynomial_eq_zero_iff rs).mp hzero
  · have hroot : rho ∈ (polynomial rs).roots := by
      exact (mem_roots hzero).mpr (by
        rw [IsRoot, eval_polynomial]
        exact hfold)
    exact False.elim (hgood (by
      simpa [badCoefficients, rs, hzero] using
        (Multiset.mem_toFinset.mpr hroot)))

/-- A whole Gate component whose *native folded* row expressions vanish
outside the explicit composition-coefficient roots satisfies the existing
raw Gate interaction AIR model.  The previous-row samples are obtained from
one cyclic row permutation of the same last interaction column. -/
theorem folded_rows_imply_raw_acceptance (logSize : Nat)
    (previousRow : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (first last : Fin (2 ^ logSize) → Fin 4 → GateSecure)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (alpha z rho claimed : GateSecure)
    (hfold : ∀ i,
      threeTermWithPrefix
        (fold rho ((S31.Gadgets.Air.NativeQm31Air.residuals
          (rows i).flags (rows i).in0 (rows i).in1 (rows i).output).map
            S31.Gadgets.Air.GateChallenge.liftBase))
        (nativeRowPair (rows i) alpha z).1
        (nativeRowPair (rows i) alpha z).2
        (nativeYieldTerm (rows i) alpha z)
        (first i) (last (previousRow i)) (last i)
        rho claimed ((2 ^ logSize : Nat) : GateSecure) = 0)
    (hgood : ∀ i, rho ∉ badCoefficients (rows i) alpha z
      (first i) (last (previousRow i)) (last i)
      claimed ((2 ^ logSize : Nat) : GateSecure))
    (hclosure : claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0) :
    nativeRawInteractionAccepts logSize previousRow rows
      externalUses externalYields alpha z := by
  refine ⟨(fun i => decode (first i)), (fun i => decode (last i)),
    claimed, ?_, ?_, hclosure⟩
  · intro i
    have hall := finalizer_zero_implies_all_residuals (rows i) alpha z
      (first i) (last (previousRow i)) (last i) rho claimed
      ((2 ^ logSize : Nat) : GateSecure) (hfold i) (hgood i)
    have hp : pairResidual (nativeRowPair (rows i) alpha z).1
        (nativeRowPair (rows i) alpha z).2 (decode (first i)) = 0 :=
      hall _ (by simp [rowConstraints, qm31RowConstraints])
    exact hp
  · intro i
    have hall := finalizer_zero_implies_all_residuals (rows i) alpha z
      (first i) (last (previousRow i)) (last i) rho claimed
      ((2 ^ logSize : Nat) : GateSecure) (hfold i) (hgood i)
    have hs : singleResidual (nativeYieldTerm (rows i) alpha z)
        (decode (last i) - decode (last (previousRow i)) - decode (first i) +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0 :=
      hall _ (by simp [rowConstraints, qm31RowConstraints])
    exact hs

/-- The source-extracted full native Gate finalizer inherits the fixed
invalid-multiset exceptional-pair theorem, conditional on row-value custody,
the public/external claim equation, and avoidance of bad composition roots. -/
theorem folded_rows_accept_only_exceptional (logSize : Nat)
    (previousRow : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (first last : Fin (2 ^ logSize) → Fin 4 → GateSecure)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (alpha z rho claimed : GateSecure)
    (hfold : ∀ i,
      threeTermWithPrefix
        (fold rho ((S31.Gadgets.Air.NativeQm31Air.residuals
          (rows i).flags (rows i).in0 (rows i).in1 (rows i).output).map
            S31.Gadgets.Air.GateChallenge.liftBase))
        (nativeRowPair (rows i) alpha z).1
        (nativeRowPair (rows i) alpha z).2
        (nativeYieldTerm (rows i) alpha z)
        (first i) (last (previousRow i)) (last i)
        rho claimed ((2 ^ logSize : Nat) : GateSecure) = 0)
    (hgood : ∀ i, rho ∉ badCoefficients (rows i) alpha z
      (first i) (last (previousRow i)) (last i)
      claimed ((2 ^ logSize : Nat) : GateSecure))
    (hclosure : claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0) :
    (alpha, z) ∈ S31.Gadgets.Air.GateAirRawSoundness.exceptionalPairs
      (List.ofFn rows) externalUses externalYields := by
  exact native_raw_accepts_only_exceptional logSize previousRow rows
    externalUses externalYields alpha z
    (folded_rows_imply_raw_acceptance logSize previousRow rows first last
      externalUses externalYields alpha z rho claimed hfold hgood hclosure)

end S31.Gadgets.Air.NativeGateFinalizerBridge
