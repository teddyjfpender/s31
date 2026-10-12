import S31.Gadgets.Functional.SSANativePolynomialRows
import S31.Gadgets.Air.GateLookup

/-!
An exact Gate-event join for the bounded direct-gate SSA source rows. In the
native AIR, each physical source row has two Gate uses and its output is a
Gate yield repeated by a fixed multiplicity. Under exact multiset balance
and unique produced values per circuit address, those physical row values
induce one coherent logical wire map. This discharges the free wire-map
premise of `SSANativePolynomialRows` for source rows.

The production LogUp protocol checks a challenge-compressed relation, not
literal list permutation. Its soundness reduction, row/column commitment
authentication, and PCS/FRI acceptance remain outside this theorem.
-/

namespace S31.Functional.SSAGateLookupWireMap

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows

/-- Choose the unique yielded QM31 value at an address, if one exists.
The default value at an unproduced address is irrelevant to the theorem. -/
noncomputable def wireOfProduced (produced : List Event) (address : Nat) : Quad :=
  by
    classical
    exact if h : ∃ value, (address, value) ∈ produced then
      Classical.choose h else base 0

theorem wire_of_produced_event (produced : List Event)
    (hunique : uniqueProduced produced) (address : Nat) (value : Quad)
    (hmember : (address, value) ∈ produced) :
    wireOfProduced produced address = value := by
  classical
  have hex : ∃ v, (address, v) ∈ produced := ⟨value, hmember⟩
  unfold wireOfProduced
  simp only [dif_pos hex]
  exact hunique address (Classical.choose hex) value
    (Classical.choose_spec hex) hmember

/-- The already checked one-row Gate example has a concrete, nonempty
producer map. Its locally valid forged read cannot enter that map under
exact balance. -/
theorem honest_example_has_coherent_wire :
    wireOfProduced (allYields [honestExample] exampleExternalYields) 7 = base 5 ∧
    wireOfProduced (allYields [honestExample] exampleExternalYields) 9 = base 8 := by
  have hunique : uniqueProduced (allYields [honestExample] exampleExternalYields) := by
    intro address left right hleft hright
    simp [allYields, Row.yields, honestExample, exampleExternalYields] at hleft hright
    rcases hleft with hleft | hleft | hleft <;>
      rcases hright with hright | hright | hright <;>
      simp_all
  constructor
  · exact wire_of_produced_event _ hunique 7 (base 5) (by decide)
  · exact wire_of_produced_event _ hunique 9 (base 8) (by decide)

theorem locally_valid_forged_gate_still_rejected :
    S31.Gadgets.Air.Qm31Ops.accepts forgedExample.flags forgedExample.in0
      forgedExample.in1 forgedExample.output ∧
      ¬ balanced [forgedExample] forgedExternalUses exampleExternalYields :=
  ⟨forged_example_local, forged_example_rejected⟩

/-- One actual AIR row at the exported trace index, with its Gate addresses,
selector and multiplicity equal to the projected source cell. The local nine
operation residuals vanish on the physical row values. -/
def sourceGateRows (certificate : Certificate)
    (observedCells : List ColumnCell) (rows : List Row) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ observedCells, ∃ row : Row,
      rows[cell.traceRow]? = some row ∧
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      row.flags = cellFlags cell ∧
      row.in0Address = cell.in0 ∧
      row.in1Address = cell.in1 ∧
      row.outAddress = cell.out ∧
      row.multiplicity = cell.mults ∧
      0 < row.multiplicity ∧
      S31.Gadgets.Air.Qm31Ops.accepts row.flags row.in0 row.in1 row.output

/-- Literal Gate balance and producer uniqueness force every matched source
row's two reads and output to be values in the same canonical address map.
This is the precise ideal lookup premise consumed by the previous source-row
polynomial theorem. -/
theorem exact_gate_implies_source_cells_evaluated
    (certificate : Certificate) (observedCells : List ColumnCell)
    (rows : List Row) (externalUses externalYields : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hsource : sourceGateRows certificate observedCells rows) :
    sourceCellsEvaluated certificate observedCells
      (wireOfProduced (allYields rows externalYields)) := by
  intro instruction hmember
  obtain ⟨cell, hcell, row, hindex, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
    _, hpositive, hair⟩ := hsource instruction hmember
  have hrow : row ∈ rows := by
    obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hindex
    rw [← hvalue]
    exact List.getElem_mem hbound
  let produced := allYields rows externalYields
  have huses := row_input_use rows externalUses row hrow
  have hread0 : (row.in0Address, row.in0) ∈ produced :=
    hbalance.mem_iff.mp huses.1
  have hread1 : (row.in1Address, row.in1) ∈ produced :=
    hbalance.mem_iff.mp huses.2
  have hyield : (row.outAddress, row.output) ∈ produced :=
    row_output_yield rows externalYields row hrow hpositive
  have hwire0 : wireOfProduced produced row.in0Address = row.in0 :=
    wire_of_produced_event produced hunique _ _ hread0
  have hwire1 : wireOfProduced produced row.in1Address = row.in1 :=
    wire_of_produced_event produced hunique _ _ hread1
  have hwireOut : wireOfProduced produced row.outAddress = row.output :=
    wire_of_produced_event produced hunique _ _ hyield
  refine ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, ?_⟩
  change S31.Gadgets.Air.Qm31Ops.accepts (cellFlags cell)
    (wireOfProduced produced cell.in0)
    (wireOfProduced produced cell.in1)
    (wireOfProduced produced cell.out)
  rw [← hflags, ← haddr0, ← haddr1, ← haddrOut,
    hwire0, hwire1, hwireOut]
  exact hair

/-- Exact Gate balance replaces the abstract coherent-wire premise in the
bounded source-to-AIR value theorem. The packed input's producer event is
still a separate public-boundary premise; its Gate derivation is future work.
`hsource` identifies the actual physical source rows by exported trace index.
-/
theorem checked_source_output_of_exact_gate
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (input : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hsource : sourceGateRows certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (address 0, S31.Gadgets.Air.Qm31Ops.packM31 input) ∈
      allYields rows externalYields) :
    observedCells = expectedCells certificate totalAddRows ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
          wireOfProduced (allYields rows externalYields)
            (address certificate.output) =
              S31.Gadgets.Air.Qm31Ops.packM31 output := by
  let produced := allYields rows externalYields
  let wire := wireOfProduced produced
  have hinput : wire (address 0) = S31.Gadgets.Air.Qm31Ops.packM31 input :=
    wire_of_produced_event produced hunique _ _ hinputYield
  have hpolynomials : nativePolynomialRows certificate wire :=
    source_cells_imply_polynomial_rows certificate observedCells wire
      (exact_gate_implies_source_cells_evaluated certificate observedCells
        rows externalUses externalYields hbalance hunique hsource)
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hrelation
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hrelation
    | some parsed => exact ⟨parsed, by simpa [hp]⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input hrelation]
    exact hdenotation
  exact ⟨hcells, output, hdenotation,
    selected_wire_matches_execution certificate wire input output
      hinput hpolynomials hexecute⟩

end S31.Functional.SSAGateLookupWireMap
