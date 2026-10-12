import S31.Gadgets.Functional.Correspondence.AliasCheckedFullModeledComposition

/-!
The fixed Gate yield count is the number of consumers of an output address.
This module computes it from the alias-derived projected rows, the checked
constant/padding *address schedule*, and the nine public feeder addresses.
Input island multiplicities are erased before either the count or the checker
is evaluated. The island's selectors, addresses, values, and arithmetic still
require a checked certificate; this is not a Lean implementation of Zig's
constant-address generator or a native PCS-opening authentication theorem.
-/

namespace S31.Functional.Correspondence.AliasDerivedGateMultiplicities

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSAPublicInputBinding
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.AliasCheckedFullModeledComposition
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

set_option maxRecDepth 8192

/-- The direct Gate public boundary supplies the unit at address 2 and eight
scalar input words at addresses 3–10. It supplies no Gate yields. -/
def publicFeeders : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- Erase every untrusted output-use count while preserving the island's
physical row, selector, and three address columns. -/
def addressSchedule (island : List ColumnCell) : List ColumnCell :=
  island.map (fun cell => { cell with mults := 0 })

/-- All Gate reads are fixed by the admitted source/public projected rows and
the island address schedule. The supplied island multiplicities do not occur
in this expression. -/
def scheduledReads (certificate : Certificate) (island : List ColumnCell) :
    List Nat :=
  readAddresses (joinedCells certificate (addressSchedule island)) publicFeeders

/-- The unique intended output multiplicity for a producer at `address` in
the zero-external-yield direct Gate profile. -/
def outputUseCount (certificate : Certificate) (island : List ColumnCell)
    (address : Nat) : Nat :=
  (scheduledReads certificate island).count address

/-- Install source/schedule-derived multiplicities on every island cell.
The input's `mults` fields are discarded first, so they cannot affect the
constructed fixed roster or its subsequent check. -/
def derivedIsland (certificate : Certificate) (island : List ColumnCell) :
    List ColumnCell :=
  (addressSchedule island).map fun cell =>
    { cell with mults := outputUseCount certificate island cell.out }

/-- Projected multiplicities are emitted by the source/public row
constructors. Check that those source-derived counts equal the same global
read count used to fill the island. -/
def projectedCountsCheck (certificate : Certificate)
    (island : List ColumnCell) : Bool :=
  (projectedCells certificate).all fun cell =>
    decide (cell.mults = outputUseCount certificate island cell.out)

theorem derived_island_ignores_supplied_multiplicities
    (certificate : Certificate) (first second : List ColumnCell)
    (hschedule : addressSchedule first = addressSchedule second) :
    derivedIsland certificate first = derivedIsland certificate second := by
  simp only [derivedIsland, outputUseCount, scheduledReads, hschedule]

theorem derived_island_has_read_counts
    (certificate : Certificate) (island : List ColumnCell) :
    ∀ cell ∈ derivedIsland certificate island,
      cell.mults = outputUseCount certificate island cell.out := by
  intro cell hcell
  obtain ⟨scheduled, _, rfl⟩ := List.mem_map.mp hcell
  rfl

theorem projected_counts_check_sound (certificate : Certificate)
    (island : List ColumnCell)
    (hcheck : projectedCountsCheck certificate island = true) :
    ∀ cell ∈ projectedCells certificate,
      cell.mults = outputUseCount certificate island cell.out := by
  intro cell hcell
  change (projectedCells certificate).all (fun cell =>
    decide (cell.mults = outputUseCount certificate island cell.out)) = true
    at hcheck
  exact of_decide_eq_true
    ((List.all_eq_true.mp hcheck) cell hcell)

/-- A single executable admission check for the fully derived roster. The
constant certificate validates the address schedule and coherent value table;
the bounded ledger validates that all projected producer counts also agree
and every read has a matching yield. No caller-provided island count is read.
-/
def check (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad) : Bool :=
  (NativeConstantIslandCertificate.check certificate
      (derivedIsland certificate island) values &&
    projectedCountsCheck certificate island) &&
    CheckedGateAddressLedger.check
      (joinedCells certificate (derivedIsland certificate island))
      publicFeeders []

theorem check_ignores_supplied_multiplicities
    (certificate : Certificate) (first second : List ColumnCell)
    (values : List Quad)
    (hschedule : addressSchedule first = addressSchedule second) :
    check certificate first values = check certificate second values := by
  simp [check, derived_island_ignores_supplied_multiplicities
    certificate first second hschedule, projectedCountsCheck,
    outputUseCount, scheduledReads, hschedule]
  rfl

/-- A successful checker fixes every one of the 512 output-use counts to the
read count of the source-plus-island address schedule and public feeders. -/
theorem checked_joined_has_read_counts (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad)
    (hcheck : check certificate island values = true) :
    ∀ cell ∈ joinedCells certificate (derivedIsland certificate island),
      cell.mults = outputUseCount certificate island cell.out := by
  have hparts := hcheck
  simp only [check, Bool.and_eq_true] at hparts
  intro cell hcell
  rcases List.mem_append.mp hcell with hprojected | hisland
  · exact projected_counts_check_sound certificate island
      hparts.1.2
      cell hprojected
  · exact derived_island_has_read_counts certificate island cell hisland

/-- Source bytes plus the checked address/value schedule construct the full
512-row trace with source-derived Gate multiplicities. The only supplied
island fixed words that survive are positions, selectors, and addresses.
Native column authentication, PCS/FRI, and LogUp soundness remain separate.
-/
theorem checked_alias_derived_full_modeled_trace
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (island : List ColumnCell) (values : List Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hcheck : check certificate island values = true) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      physical = traceWithExternal
        (joinedCells certificate (derivedIsland certificate island)) wire
        publicFeeders [] ∧
      (joinedCells certificate (derivedIsland certificate island)).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈
        joinedCells certificate (derivedIsland certificate island),
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate (derivedIsland certificate island),
        fixedMatches physical cell) ∧
      (∀ cell ∈ joinedCells certificate (derivedIsland certificate island),
        cell.mults = outputUseCount certificate island cell.out) ∧
      allArithmeticRootsZero physical ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  have hparts := hcheck
  simp only [check, Bool.and_eq_true] at hparts
  have hisland : NativeConstantIslandCertificate.check certificate
      (derivedIsland certificate island) values = true :=
    hparts.1.1
  have hledger : CheckedGateAddressLedger.check
      (joinedCells certificate (derivedIsland certificate island))
      publicFeeders [] = true :=
    hparts.2
  obtain ⟨wire, output, physical, hdenotation, hphysical, hlength,
    hcoverage, hfixed, harithmetic, hselected, hinput, hbalance⟩ :=
    checked_alias_full_modeled_trace sourceBytes normalizedBytes
      canonicalBytes certificate input (derivedIsland certificate island)
      values publicFeeders [] halias hisland hledger
  exact ⟨wire, output, physical, hdenotation, hphysical, hlength,
    hcoverage, hfixed, checked_joined_has_read_counts certificate island
      values hcheck,
    harithmetic, hselected, hinput, hbalance⟩

end S31.Functional.Correspondence.AliasDerivedGateMultiplicities
