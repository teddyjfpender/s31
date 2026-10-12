import S31.Gadgets.Functional.Correspondence.AliasJoinedFixedRoster
import S31.Gadgets.Functional.Correspondence.HonestConstantIslandAgreement
import S31.Gadgets.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

/-!
Alias source admission constructs the complete direct-Gate physical model
without a separately checked producer-only source spelling. The remaining
premises are executable checks for the constant island and bounded address
ledger. The result is a synthetic decoded trace, not a statement about native
commitment openings or PCS/FRI verifier soundness.
-/

namespace S31.Functional.Correspondence.AliasCheckedFullModeledComposition

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirRows
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.AcceptedPublicFixedCells
open S31.Functional.Correspondence.AliasJoinedFixedRoster
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.HonestConstantIslandAgreement
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

/-- The exact three-file alias check supplies an eager execution. Therefore
all source and public projected ports lie below the island's fresh allocation,
even when the selected output is an early producer. -/
theorem checked_alias_projected_ports_below_island
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∀ cell ∈ projectedCells certificate,
      cell.in0 < 33 + certificate.instructions.length ∧
      cell.in1 < 33 + certificate.instructions.length ∧
      cell.out < 33 + certificate.instructions.length := by
  let input : Lanes := fun _ => 0
  obtain ⟨output, hexecute⟩ := checked_alias_executes sourceBytes
    normalizedBytes canonicalBytes certificate input halias
  have houtput := selected_output_id_bound_of_execution certificate
    input output hexecute
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have htrace : AcceptsTrace [input] certificate.instructions final :=
        executing_trace_has_air_rows certificate.instructions [input]
          final hrun
      exact projected_ports_below_island certificate input htrace houtput

/-- The projected public boundary pins every island seed it shares with a
source/public cell. This is derived from the alias check, not from an assumed
agreement between separately supplied witness functions. -/
theorem checked_alias_boundary_shared_agreement
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (projectedWire : Nat → Quad)
    (input output : Lanes) (values : List Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      projectedWire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate)
      projectedWire output)
    (hunit : projectedWire 1 = unit ⟨0, by decide⟩)
    (hseed : SeedValues certificate values) :
    SharedAgreement certificate projectedWire values := by
  have hports := checked_alias_projected_ports_below_island
    sourceBytes normalizedBytes canonicalBytes certificate halias
  have hseeds := boundary_seed_values certificate projectedWire input
    output values hinput houtput hunit hseed
  intro cell hcell address hport hconstant
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).1)
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).2.1)
  rcases List.mem_singleton.mp hport with ha
  exact hseeds address hconstant (ha ▸ (hports cell hcell).2.2)

/-- Every admitted bounded alias has one complete 512-row modeled local
arithmetic witness. The selected output, source and public boundary, and
constant island use one coherent address assignment. -/
theorem checked_alias_joined_local_arithmetic_exists
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (island : List ColumnCell) (values : List Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) = packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input := by
  obtain ⟨projectedWire, output, hdenotation, hsource, hinput,
    houtput, hselected, hunit⟩ :=
    checked_alias_public_boundary_exists sourceBytes normalizedBytes
      canonicalBytes certificate input halias
  have hseed : SeedValues certificate values :=
    (NativeConstantIslandCertificate.check_sound certificate island values
      hisland).2.2.2.1
  have hshared : SharedAgreement certificate projectedWire values :=
    checked_alias_boundary_shared_agreement sourceBytes normalizedBytes
      canonicalBytes certificate projectedWire input output values halias
      hinput houtput hunit hseed
  let wire := mergedWire certificate projectedWire values
  have hprojected : ∀ cell ∈ projectedCells certificate,
      cellAccepts cell projectedWire :=
    projected_cells_accept certificate projectedWire input output
      hsource hinput houtput hunit
  have hislandAccept : ∀ cell ∈ island,
      cellAccepts cell (wireOfValues values) :=
    checked_cells_arithmetic certificate island values hisland
  have hjoined : ∀ cell ∈ joinedCells certificate island,
      cellAccepts cell wire := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojectedCell | hislandCell
    · have h0 := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.in0 (by simp)
      have h1 := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.in1 (by simp)
      have ho := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.out (by simp)
      simpa only [wire, cellAccepts, h0, h1, ho] using
        hprojected cell hprojectedCell
    · have hsound := checked_cells_sound certificate island values
        hisland cell hislandCell
      have h0 := merged_island_port certificate projectedWire values
        cell.in0 hsound.2.1
      have h1 := merged_island_port certificate projectedWire values
        cell.in1 hsound.2.2.1
      have ho := merged_island_port certificate projectedWire values
        cell.out hsound.2.2.2.1
      simpa only [wire, cellAccepts, h0, h1, ho] using
        hislandAccept cell hislandCell
  have hroster := checked_alias_joined_roster_complete sourceBytes
    normalizedBytes canonicalBytes certificate island values halias hisland
  have hnotconstant : ¬ constantAddress certificate
      (address certificate.output) := by
    have hexecute := checked_alias_executes sourceBytes normalizedBytes
      canonicalBytes certificate input halias
    obtain ⟨out, hout⟩ := hexecute
    have hbound := selected_output_id_bound_of_execution certificate
      input out hout
    simp only [constantAddress, address]
    omega
  exact ⟨wire, output, hdenotation, hroster.1, hroster.2.2.2,
    checked_alias_joined_fixed_matches sourceBytes normalizedBytes
      canonicalBytes certificate island values wire halias hisland,
    arithmetic_complete (joinedCells certificate island) wire hjoined,
    by simpa [wire, mergedWire, hnotconstant] using hselected,
    merged_input_boundary certificate projectedWire values input hinput hseed⟩

/-- The checked alias fixed roster is a permutation of physical positions
0 through 511. This follows from complete coverage and unique row indices.
-/
theorem checked_alias_joined_position_perm
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ((joinedCells certificate island).map ColumnCell.traceRow).Perm
      (List.range 512) := by
  have hroster := checked_alias_joined_roster_complete sourceBytes
    normalizedBytes canonicalBytes certificate island values halias hisland
  apply (List.perm_ext_iff_of_nodup hroster.2.1 List.nodup_range).2
  intro row
  constructor
  · intro hmem
    obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hmem
    exact List.mem_range.mpr (heq ▸ hroster.2.2.1 cell hcell)
  · intro hmem
    obtain ⟨cell, hcell, heq⟩ := hroster.2.2.2
      ⟨row, List.mem_range.mp hmem⟩
    exact List.mem_map.mpr ⟨cell, hcell, heq⟩

/-- The bounded address ledger balances all 512 decoded Gate rows of the
modeled trace, including the alias's eager trailing producers. -/
theorem checked_alias_joined_decoded_gate_balance
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad) (wire : Nat → Quad)
    (externalUses externalYields : List Nat)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    balanced (nativeRows (trace (joinedCells certificate island) wire))
      (wireEvents wire externalUses) (wireEvents wire externalYields) := by
  have hroster := checked_alias_joined_roster_complete sourceBytes
    normalizedBytes canonicalBytes certificate island values halias hisland
  have hcanonical := checked_alias_joined_canonical sourceBytes
    normalizedBytes canonicalBytes certificate island values halias hisland
  have hrows := decoded_rows_perm (joinedCells certificate island) wire
    hroster.2.1 hroster.2.2.1 hcanonical
    (checked_alias_joined_position_perm sourceBytes normalizedBytes
      canonicalBytes certificate island values halias hisland)
  exact balanced_of_rows_perm _ _ _ _ hrows
    (CheckedGateAddressLedger.check_sound _ wire _ _ hledger)

/-- Exact alias/source/relation/IR admission plus checked island and address
ledger construct a complete 512-row synthetic decoded physical trace for
every public input. All local arithmetic roots vanish, every fixed tuple
matches, the public input and selected output are pinned, and the trace's
own Gate events balance. No producer-only direct spelling is a premise. -/
theorem checked_alias_full_modeled_trace
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (island : List ColumnCell) (values : List Quad)
    (externalUses externalYields : List Nat)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      physical = traceWithExternal (joinedCells certificate island) wire
        externalUses externalYields ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island, fixedMatches physical cell) ∧
      allArithmeticRootsZero physical ∧
      wire (address certificate.output) = packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  obtain ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
    harithmetic, hselected, hinput⟩ :=
    checked_alias_joined_local_arithmetic_exists sourceBytes
      normalizedBytes canonicalBytes certificate input island values
      halias hisland
  let physical := traceWithExternal (joinedCells certificate island) wire
    externalUses externalYields
  have hfixedPhysical : ∀ cell ∈ joinedCells certificate island,
      fixedMatches physical cell := by
    intro cell hcell
    simpa [physical, traceWithExternal] using hfixed cell hcell
  have harithmeticPhysical : allArithmeticRootsZero physical := by
    simpa [physical, traceWithExternal] using harithmetic
  have hbalance : balanced (nativeRows physical) physical.externalUses
      physical.externalYields := by
    simpa [physical, traceWithExternal] using
      checked_alias_joined_decoded_gate_balance sourceBytes
        normalizedBytes canonicalBytes certificate island values wire
        externalUses externalYields halias hisland hledger
  exact ⟨wire, output, physical, hdenotation, rfl, hlength, hcoverage,
    hfixedPhysical, harithmeticPhysical, hselected, hinput, hbalance⟩

end S31.Functional.Correspondence.AliasCheckedFullModeledComposition
