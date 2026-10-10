import S31.Gadgets.Functional.TextSquare4TraceRows
import S31.Gadgets.Air.NativeGateRawSoundness

/-!
A fixed forged public fourth-power claim makes the modeled Gate multiset
unbalanced. The source-extracted raw LogUp AIR can then accept that fixed
witness only for the formally bounded exceptional challenge pairs. This is
an ideal-challenge algebra result, not a PCS/Fiat-Shamir theorem.
-/

namespace S31.Functional.TextSquare4RawSoundness

open S31
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.NativeGateRawSoundness
open S31.Functional.TextSquare4GateJoin
open S31.Functional.TextSquare4TraceRows

noncomputable def nativeAcceptingPairs (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    nativeRawInteractionAccepts logSize prev rows externalUses
      externalYields pair.1 pair.2

theorem native_accepting_pairs_eq_raw (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    nativeAcceptingPairs logSize prev rows externalUses externalYields =
      rawAcceptingPairs logSize prev rows externalUses externalYields := by
  classical
  ext pair
  simp only [nativeAcceptingPairs, rawAcceptingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact native_raw_accepts_iff logSize prev rows
    externalUses externalYields pair.1 pair.2

/-- A fixed wrong four-word public result has at most this many ideal
challenge pairs that satisfy the source-extracted raw Gate interaction AIR.
The bound is `(5s² + 2s + 3n) · |QM31|`, where `s` is the number of distinct
Gate event tuples and `n` the number of padded arithmetic rows. The ideal
challenge-pair space has size `|QM31|²`.

The premises identify the source-generated 23-gate path in the padded row
list, pin public/constant events, and cover declared producers. The native
trace-to-row and transcript distribution bridges remain open. -/
theorem forged_claim_native_raw_acceptance_card_le
    (logSize : Nat) (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields :
      List S31.Gadgets.Air.GateLookup.Event)
    (wire : Nat → S31.Gadgets.Packed.Quad)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ TextSquare4Air.fourth input)
    (hcovered : ∀ address value,
      address < TextSquare4Native.declaredVarCount →
      (address, value) ∈ allYields (List.ofFn rows) externalYields →
      (address, value) ∈ declaredEvents wire)
    (hpath : nativePathRows (List.ofFn rows))
    (hpins : pinnedEvents
      (allYields (List.ofFn rows) externalYields) input claimed)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allUses (List.ofFn rows) externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allYields (List.ofFn rows) externalYields).count event < 2147483647) :
    (nativeAcceptingPairs logSize prev rows
      externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card +
        (denominatorEvents (List.ofFn rows)).length) *
        Fintype.card GateSecure := by
  have hwrong : ¬ balanced (List.ofFn rows) externalUses externalYields := by
    intro hbalance
    exact hforged (native_public_claim_of_exported_producers
      (List.ofFn rows) externalUses externalYields wire
      input claimed hbalance hcovered hpath hpins)
  rw [native_accepting_pairs_eq_raw]
  exact raw_false_acceptance_card_le logSize prev rows
    externalUses externalYields hcanonical huses hyields hwrong

set_option maxRecDepth 4096 in
/-- The same bound for the exact 512-row padded circuit schedule checked by
the native exporter. The source's two square rows are at positions 502 and
503; all selected gate rows are named in `selectedRows`. -/
theorem forged_claim_emitted_row_acceptance_card_le
    (prev : Equiv.Perm
      (Fin TextSquare4Native.paddedArithmeticRowCount))
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (externalUses externalYields :
      List S31.Gadgets.Air.GateLookup.Event)
    (wire : Nat → S31.Gadgets.Packed.Quad)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ TextSquare4Air.fourth input)
    (hcovered : ∀ address value,
      address < TextSquare4Native.declaredVarCount →
      (address, value) ∈ allYields (List.ofFn rows) externalYields →
      (address, value) ∈ declaredEvents wire)
    (hselected : selectedRows rows)
    (hpins : pinnedEvents
      (allYields (List.ofFn rows) externalYields) input claimed)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allUses (List.ofFn rows) externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allYields (List.ofFn rows) externalYields).count event < 2147483647) :
    (nativeAcceptingPairs 9 prev rows
      externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card +
        1536) * Fintype.card GateSecure := by
  have hden : (denominatorEvents (List.ofFn rows)).length = 1536 := by
    rw [denominator_events_length, List.length_ofFn]
    norm_num [TextSquare4Native.paddedArithmeticRowCount]
  have hbound := forged_claim_native_raw_acceptance_card_le
    9 prev rows externalUses externalYields wire input claimed
    hforged hcovered (selected_rows_imply_path rows hselected)
    hpins hcanonical huses hyields
  simpa only [hden] using hbound

end S31.Functional.TextSquare4RawSoundness
