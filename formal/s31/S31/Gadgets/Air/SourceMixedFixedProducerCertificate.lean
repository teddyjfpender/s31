import S31.Gadgets.Air.SourceMixedFixedScheduleBridge

/-!
The pinned N1/N8 complete fixed-column exports determine every active Gate
producer address, including rows outside the selected public path. The
source-owned boundary still has to identify its 512 rows with the decoded
trace and certify that it has no separate baseline yields.
-/

namespace S31.Gadgets.Air.SourceMixedFixedProducerCertificate

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateProducerCheck
open S31.Gadgets.Air.GateProducerRoster
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedProducerCheck
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The fixed output-address and multiplicity columns, filtered exactly as
the logical-producer roster filters zero-multiplicity rows. -/
def fixedActiveAddresses (fixed : Fin 512 → Fin 8 → F) : List Nat :=
  activeAddresses (List.ofFn (fun i : Fin 512 =>
    ((fixed i ⟨6, by decide⟩).val, (fixed i ⟨7, by decide⟩).val)))

theorem checked_roster_eq_fixed_active {N : Nat} (boundary : Boundary N)
    (trace : Trace 9) (fixed : Fin 512 → Fin 8 → F)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = fixed i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hbaseline : boundary.baselineYields = []) :
    (checkedRoster boundary).map Prod.fst =
      fixedActiveAddresses fixed := by
  simp only [checkedRoster, logical_address_roster]
  simp [Boundary.jointGateSource, GateSource.gateRows,
    GateSource.gateExternalYields, hbaseline]
  rw [← hrows, active_rows_addresses_eq]
  unfold fixedActiveAddresses
  congr 1
  simp only [nativeRows, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, DecodedDirectGateTrace.row, Prod.mk.injEq]
  exact ⟨congrArg ZMod.val (hfixed i ⟨6, by decide⟩),
    congrArg ZMod.val (hfixed i ⟨7, by decide⟩)⟩

theorem n1_fixed_scan :
    (scan 512 ∅ (fixedActiveAddresses N1.fixedAt)).isSome = true := by
  decide

theorem n8_fixed_scan :
    (scan 512 ∅ (fixedActiveAddresses N8.fixedAt)).isSome = true := by
  decide

theorem n1_producer_scan (boundary : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hbaseline : boundary.baselineYields = []) :
    ∃ result, scan 512 ∅ ((checkedRoster boundary).map Prod.fst) =
      some result := by
  rw [checked_roster_eq_fixed_active boundary trace N1.fixedAt
    hfixed hrows hbaseline]
  cases hscan : scan 512 ∅ (fixedActiveAddresses N1.fixedAt) with
  | none =>
      have h := n1_fixed_scan
      simp [hscan] at h
  | some result => exact ⟨result, rfl⟩

theorem n8_producer_scan (boundary : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hbaseline : boundary.baselineYields = []) :
    ∃ result, scan 512 ∅ ((checkedRoster boundary).map Prod.fst) =
      some result := by
  rw [checked_roster_eq_fixed_active boundary trace N8.fixedAt
    hfixed hrows hbaseline]
  cases hscan : scan 512 ∅ (fixedActiveAddresses N8.fixedAt) with
  | none =>
      have h := n8_fixed_scan
      simp [hscan] at h
  | some result => exact ⟨result, rfl⟩

end S31.Gadgets.Air.SourceMixedFixedProducerCertificate
