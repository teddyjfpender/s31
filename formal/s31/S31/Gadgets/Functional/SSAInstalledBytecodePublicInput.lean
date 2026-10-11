import S31.Gadgets.Functional.SSAInstalledBytecodePublicOutput
import S31.Gadgets.Functional.SSAPublicInputBinding

/-!
The four public input words are positive Gate events at addresses 3--6.
Physical copy, basis-multiply, and pack-add rows force the source input at
address 22 to be their four-lane packing. The final pack row must have a
positive output multiplicity. This follows from `physicalGateBytecodeRows`
for the exact source-derived input cells. Proving that successful source
parsing gives this positive multiplicity for the native row remains a
compiler-invariant obligation.
Without it the row does not yield an event, and the earlier
source Gate theorem's `hinputYield` cannot be inferred.

The module composes ideal exact Gate balance with source-derived projected
cells and installed local arithmetic bytecode. It does not prove that the
native verifier authenticates these events or opened trace cells, nor that
LogUp implies exact balance or that PCS/FRI and Fiat--Shamir are sound.
-/

namespace S31.Functional.SSAInstalledBytecodePublicInput

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAGateLookupWireMap
open S31.Functional.SSAInstalledBytecodeGateJoin
open S31.Functional.SSAInstalledBytecodePublicOutput

/-- Exact physical input-cell rows, zero/basis producers, and four public
input scalar events establish the existing local `InputBoundary` on the
unique Gate producer map. The extra four pointwise identity rows are checked
by `physicalGateBytecodeRows`; their values are also joined by Gate balance.
-/
theorem input_boundary_of_exact_gate
    (certificate : Certificate) (totalAddRows : Nat)
    (observedCells : List ColumnCell) (input : Lanes)
    (rows : List Row) (externalUses externalYields : List Event)
    (hcells : observedCells = expectedInputCells certificate totalAddRows)
    (hrows : physicalGateBytecodeRows observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈ allYields rows externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈ allYields rows externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈ allYields rows externalYields)
    (hpublicPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈ externalYields) :
    InputBoundary certificate totalAddRows
      (wireOfProduced (allYields rows externalYields)) input := by
  let produced := allYields rows externalYields
  have heval := physical_cells_evaluated observedCells rows externalUses
    externalYields hrows hbalance hunique
  refine ⟨wire_of_produced_event produced hunique _ _ hzero,
    ?_, ?_,
    wire_of_produced_event produced hunique _ _ hbasis1,
    wire_of_produced_event produced hunique _ _ hbasis2,
    wire_of_produced_event produced hunique _ _ hbasis3,
    ?_, ?_⟩
  · intro i
    have hcell :
        expectedInputCopyCell certificate i.val ∈ observedCells := by
      rw [hcells, expectedInputCells]
      apply List.mem_append_right
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨i.val, by simpa using i.isLt, rfl⟩
    have hrow := heval _ hcell
    change accepts (encode .add)
      (wireOfProduced produced
        ((expectedInputCopyCell certificate i.val).in0))
      (wireOfProduced produced
        ((expectedInputCopyCell certificate i.val).in1))
      (wireOfProduced produced
        ((expectedInputCopyCell certificate i.val).out)) at hrow
    exact hrow
  · intro i
    apply wire_of_produced_event produced hunique
    apply List.mem_append_right
    exact hpublicPins i
  · intro i
    have hcell : expectedPackMulCell totalAddRows i.val ∈ observedCells := by
      rw [hcells, expectedInputCells]
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨i.val, by simpa using i.isLt, rfl⟩
    have hrow := heval _ hcell
    change accepts (encode .mul)
      (wireOfProduced produced
        ((expectedPackMulCell totalAddRows i.val).in0))
      (wireOfProduced produced
        ((expectedPackMulCell totalAddRows i.val).in1))
      (wireOfProduced produced
        ((expectedPackMulCell totalAddRows i.val).out)) at hrow
    exact hrow
  · intro i
    have hcell : expectedPackAddCell certificate i.val ∈ observedCells := by
      rw [hcells, expectedInputCells]
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨i.val, by simpa using i.isLt, rfl⟩
    have hrow := heval _ hcell
    change accepts (encode .add)
      (wireOfProduced produced
        ((expectedPackAddCell certificate i.val).in0))
      (wireOfProduced produced
        ((expectedPackAddCell certificate i.val).in1))
      (wireOfProduced produced
        ((expectedPackAddCell certificate i.val).out)) at hrow
    exact hrow

/-- A positive source-input use count makes the final pack row's
output available to Gate. Its value is then fixed by the four public pins
and the six local pack equations, rather than assumed as a packed event. -/
theorem packed_input_yield_of_exact_gate
    (certificate : Certificate) (totalAddRows : Nat)
    (observedCells : List ColumnCell) (input : Lanes)
    (rows : List Row) (externalUses externalYields : List Event)
    (hcells : observedCells = expectedInputCells certificate totalAddRows)
    (hrows : physicalGateBytecodeRows observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈ allYields rows externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈ allYields rows externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈ allYields rows externalYields)
    (hpublicPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈ externalYields) :
    (address 0, packM31 input) ∈ allYields rows externalYields := by
  let produced := allYields rows externalYields
  have hboundary := input_boundary_of_exact_gate certificate totalAddRows
    observedCells input rows externalUses externalYields hcells hrows
    hbalance hunique hzero hbasis1 hbasis2 hbasis3 hpublicPins
  have hpacked : wireOfProduced produced (address 0) = packM31 input := by
    simpa [address] using packed_input_bound certificate totalAddRows
      (wireOfProduced produced) input hboundary
  let cell := expectedPackAddCell certificate 2
  have hcell : cell ∈ observedCells := by
    rw [hcells, expectedInputCells]
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨2, by decide, rfl⟩
  obtain ⟨row, hindex, _, _, _, haddrOut, _, hm, _⟩ := hrows cell hcell
  have hrow : row ∈ rows := by
    obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hindex
    rw [← hvalue]
    exact List.getElem_mem hbound
  have hyield : (row.outAddress, row.output) ∈ produced :=
    row_output_yield rows externalYields row hrow hm
  have hrowAddress : row.outAddress = address 0 := by
    simpa [cell, expectedPackAddCell, address] using haddrOut
  have hrowValue : row.output = packM31 input := by
    have hwire : wireOfProduced produced row.outAddress = row.output :=
      wire_of_produced_event produced hunique _ _ hyield
    rw [hrowAddress] at hwire
    exact hwire.symm.trans hpacked
  simpa [hrowAddress, hrowValue] using hyield

/-- Full ideal-Gate public IO join for the bounded four-lane fragment. All
source, input and output projected rows are physical installed-bytecode rows;
the native proof acceptance and probabilistic lookup-to-exact-balance steps
remain explicit obligations outside this theorem. -/
theorem bytecode_exact_gate_public_io_sound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (sourceCells inputCells outputCells : List ColumnCell)
    (input claimed : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hsourceCells : sourceCells = expectedCells certificate totalAddRows)
    (hsourceRows : sourceGateBytecodeRows certificate sourceCells rows)
    (hinputCells : inputCells = expectedInputCells certificate totalAddRows)
    (hinputRows : physicalGateBytecodeRows inputCells rows)
    (houtputCells : outputCells = expectedOutputCells certificate totalAddRows)
    (houtputRows : physicalGateBytecodeRows outputCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈ allYields rows externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈ allYields rows externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈ allYields rows externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈ allYields rows externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields rows externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈ externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈ externalYields) :
    denotation sourceBytes input = some claimed := by
  have hinputYield := packed_input_yield_of_exact_gate certificate
    totalAddRows inputCells input rows externalUses externalYields
    hinputCells hinputRows hbalance hunique hzero
    hbasis1 hbasis2 hbasis3 hpublicInputPins
  exact bytecode_exact_gate_public_claim_sound sourceBytes normalizedBytes
    certificate totalAddRows sourceCells outputCells input claimed rows
    externalUses externalYields hrelation hsourceCells hsourceRows
    houtputCells houtputRows hbalance hunique hinputYield hzero
    hmaskBasis hinverseBasis hpublicOutputPins

end S31.Functional.SSAInstalledBytecodePublicInput
