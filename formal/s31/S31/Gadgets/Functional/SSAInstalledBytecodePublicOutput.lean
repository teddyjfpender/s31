import S31.Gadgets.Functional.SSAInstalledBytecodeGateJoin
import S31.Gadgets.Functional.SSAOutputAirCells
import S31.Gadgets.Air.UnpackRows

/-!
The public result path for the bounded four-lane direct-gate source fragment.
Every selected output mask, inverse-basis multiply, and public copy is an
actual physical Gate row at the source-derived preprocessed trace index. The
installed nine arithmetic bytecode roots vanish on that row's twelve main
cells. Exact Gate balance and a unique producer value at each address then
turn those physical rows into one coherent wire map. Fixed zero/basis events
and four public output events are explicit boundary premises.

This removes the separately assumed packed selected-claim event from the
source-to-public-claim join. It does not turn challenge-compressed LogUp into
exact balance or authenticate trace openings, fixed-column commitments,
public events, PCS/FRI, or the Fiat--Shamir transcript.
-/

namespace S31.Functional.SSAInstalledBytecodePublicOutput

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
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGateLookupWireMap
open S31.Functional.SSAInstalledBytecodeGateJoin

/-- The three output-path row kinds all use the same physical nine-root
arithmetic evaluator. The fixed cells are checked separately by equality
with `expectedOutputCells`; this predicate binds each expected cell to a
physical row and its main trace values. -/
def physicalGateBytecodeRows (observedCells : List ColumnCell)
    (rows : List Row) : Prop :=
  ∀ cell ∈ observedCells, ∃ row : Row,
    rows[cell.traceRow]? = some row ∧
    row.flags = cellFlags cell ∧
    row.in0Address = cell.in0 ∧
    row.in1Address = cell.in1 ∧
    row.outAddress = cell.out ∧
    row.multiplicity = cell.mults ∧
    0 < row.multiplicity ∧
    (∀ root ∈ bytecodeArithmetic (physicalBytecodeCells cell row), root = 0)

/-- Exact Gate balance changes each physical output-path row into the local
arithmetic relation evaluated on the unique produced value at each address.
The row's positive multiplicity is needed for its output event. -/
theorem physical_cells_evaluated
    (observedCells : List ColumnCell) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrows : physicalGateBytecodeRows observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields)) :
    ∀ cell ∈ observedCells,
      cellAccepts cell (wireOfProduced (allYields rows externalYields)) := by
  intro cell hcell
  obtain ⟨row, hindex, _, haddr0, haddr1, haddrOut,
    _, hpositive, hzero⟩ := hrows cell hcell
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
  have hwire0 : wireOfProduced produced cell.in0 = row.in0 := by
    rw [← haddr0]
    exact wire_of_produced_event produced hunique _ _ hread0
  have hwire1 : wireOfProduced produced cell.in1 = row.in1 := by
    rw [← haddr1]
    exact wire_of_produced_event produced hunique _ _ hread1
  have hwireOut : wireOfProduced produced cell.out = row.output := by
    rw [← haddrOut]
    exact wire_of_produced_event produced hunique _ _ hyield
  exact physical_bytecode_zero_implies_logical_cell cell row
    (wireOfProduced produced) hwire0 hwire1 hwireOut hzero

/-- The local output-path AIR equations and the public scalar pins. The
source-derived cells fix the exact addresses of all eleven rows. The basis
and zero values are provided by separate native constant producers; their
event membership is established in the exact-Gate join below. -/
structure OutputBoundary (certificate : Certificate) (totalAddRows : Nat)
    (wire : Nat → Quad) (claimed : Lanes) : Prop where
  zero : wire 0 = base 0
  maskBasis : ∀ i : Fin 4, wire (maskBasisAddress i.val) = unit i
  inverseBasis : ∀ i : Fin 3,
    wire ((expectedInverseCell certificate totalAddRows i.val).in1) =
      unitInverse ⟨i.val + 1, by omega⟩
  masks : ∀ i : Fin 4,
    cellAccepts (expectedMaskCell certificate totalAddRows i.val) wire
  inverses : ∀ i : Fin 3,
    cellAccepts (expectedInverseCell certificate totalAddRows i.val) wire
  copies : ∀ i : Fin 4,
    cellAccepts (expectedCopyCell certificate i.val) wire
  pins : ∀ i : Fin 4, wire (7 + i.val) = base (Field.toZMod (claimed i))

/-- The emitted mask/inverse rows implement `unpackIdx` at every output
coordinate. This identifies all four scalar result wires with the four
coordinates of the source-selected packed result. -/
theorem output_unpacks (certificate : Certificate) (totalAddRows : Nat)
    (wire : Nat → Quad) (claimed : Lanes)
    (h : OutputBoundary certificate totalAddRows wire claimed)
    (i : Fin 4) :
    S31.Gadgets.Air.UnpackRows.acceptsUnpack i
      (wire (address certificate.output))
      (wire (resultAddress certificate.instructions.length i.val)) := by
  let masked := wire (maskAddress certificate.instructions.length i.val)
  refine ⟨masked, ?_, ?_⟩
  · have hm := h.masks i
    have hb := h.maskBasis i
    change accepts (encode .pointwiseMul)
      (wire (address certificate.output))
      (wire (maskBasisAddress i.val)) masked at hm
    rw [hb] at hm
    exact hm
  · by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      simp [masked, maskAddress, resultAddress, hi]
    · have hindex : i.val - 1 < 3 := by omega
      let j : Fin 3 := ⟨i.val - 1, hindex⟩
      have hj : j.val + 1 = i.val := by simp [j]; omega
      have hr := h.inverses j
      have hb := h.inverseBasis j
      simp only [hi, ↓reduceIte]
      have hshape :
          (expectedInverseCell certificate totalAddRows j.val).in0 =
            maskAddress certificate.instructions.length i.val ∧
          (expectedInverseCell certificate totalAddRows j.val).out =
            resultAddress certificate.instructions.length i.val := by
        simp [expectedInverseCell, hj]
      change accepts (encode .mul)
        (wire ((expectedInverseCell certificate totalAddRows j.val).in0))
        (wire ((expectedInverseCell certificate totalAddRows j.val).in1))
        (wire ((expectedInverseCell certificate totalAddRows j.val).out)) at hr
      rw [hshape.1, hshape.2, hb] at hr
      have hfin : (⟨j.val + 1, by omega⟩ : Fin 4) = i := Fin.ext hj
      rw [hfin] at hr
      exact hr

/-- Public output copy gates are addition by fixed zero. Combined with
the four scalar pins, the native selected packed wire must equal the
four-lane public claim. -/
theorem output_boundary_claim (certificate : Certificate)
    (totalAddRows : Nat) (wire : Nat → Quad) (claimed : Lanes)
    (h : OutputBoundary certificate totalAddRows wire claimed) :
    wire (address certificate.output) = packM31 claimed := by
  have hlanes : ∀ i : Fin 4,
      coord (wire (address certificate.output)) i =
        Field.toZMod (claimed i) := by
    intro i
    have hu := (S31.Gadgets.Air.UnpackRows.acceptsUnpack_iff i
      (wire (address certificate.output))
      (wire (resultAddress certificate.instructions.length i.val))).mp
        (output_unpacks certificate totalAddRows wire claimed h i)
    have hc := h.copies i
    have hcopy :
        wire (7 + i.val) =
          wire (resultAddress certificate.instructions.length i.val) := by
      have hrow := (accepts_encoded .add _ _ _).mp
        (show accepts (encode .add)
          (wire (resultAddress certificate.instructions.length i.val))
          (wire 0) (wire (7 + i.val)) from by
            simpa [cellAccepts, cellFlags, expectedCopyCell, encode] using hc)
      rw [h.zero] at hrow
      simpa [evaluate, S31.Gadgets.Packed.add, base] using hrow
    have hp := h.pins i
    have hscalar :
        base (Field.toZMod (claimed i)) =
          base (coord (wire (address certificate.output)) i) :=
      hp.symm.trans (hcopy.trans hu)
    exact (congrArg Quad.a hscalar).symm
  apply Quad.ext
  · simpa [coord, packM31] using hlanes ⟨0, by decide⟩
  · simpa [coord, packM31] using hlanes ⟨1, by decide⟩
  · simpa [coord, packM31] using hlanes ⟨2, by decide⟩
  · simpa [coord, packM31] using hlanes ⟨3, by decide⟩

/-- A source-derived list of eleven output cells and physical bytecode rows
supplies the arithmetic part of `OutputBoundary`. Public pins and constant
values are explicit events in the ideal Gate producer set. -/
theorem output_boundary_of_exact_gate
    (certificate : Certificate) (totalAddRows : Nat)
    (observedCells : List ColumnCell) (claimed : Lanes)
    (rows : List Row) (externalUses externalYields : List Event)
    (hcells : observedCells = expectedOutputCells certificate totalAddRows)
    (hrows : physicalGateBytecodeRows observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈ allYields rows externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields rows externalYields)
    (hpublicPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈ externalYields) :
    OutputBoundary certificate totalAddRows
      (wireOfProduced (allYields rows externalYields)) claimed := by
  let produced := allYields rows externalYields
  have heval := physical_cells_evaluated observedCells rows externalUses
    externalYields hrows hbalance hunique
  refine ⟨wire_of_produced_event produced hunique _ _ hzero,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact wire_of_produced_event produced hunique _ _ (hmaskBasis i)
  · intro i
    exact wire_of_produced_event produced hunique _ _ (hinverseBasis i)
  · intro i
    apply heval
    rw [hcells, expectedOutputCells]
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨i.val, by simpa using i.isLt, rfl⟩
  · intro i
    apply heval
    rw [hcells, expectedOutputCells]
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨i.val, by simpa using i.isLt, rfl⟩
  · intro i
    apply heval
    rw [hcells, expectedOutputCells]
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨i.val, by simpa using i.isLt, rfl⟩
  · intro i
    apply wire_of_produced_event produced hunique
    apply List.mem_append_right
    exact hpublicPins i

/-- Installed source-row bytecode roots, installed public output-row roots,
exact Gate balance, fixed producers and four public scalar pin events imply
that the checked source bytes compute the claimed result. No packed selected
claim event is assumed. -/
theorem bytecode_exact_gate_public_claim_sound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (sourceCells outputCells : List ColumnCell)
    (input claimed : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hsourceCells : sourceCells = expectedCells certificate totalAddRows)
    (hsourceRows : sourceGateBytecodeRows certificate sourceCells rows)
    (houtputCells : outputCells = expectedOutputCells certificate totalAddRows)
    (houtputRows : physicalGateBytecodeRows outputCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (address 0, packM31 input) ∈
      allYields rows externalYields)
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈ allYields rows externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields rows externalYields)
    (hpublicPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈ externalYields) :
    denotation sourceBytes input = some claimed := by
  obtain ⟨_, output, hsource, hselected⟩ :=
    checked_source_output_of_bytecode_and_exact_gate sourceBytes
      normalizedBytes certificate totalAddRows sourceCells input rows
      externalUses externalYields hrelation hsourceCells hsourceRows
      hbalance hunique hinputYield
  have hboundary := output_boundary_of_exact_gate certificate totalAddRows
    outputCells claimed rows externalUses externalYields houtputCells
    houtputRows hbalance hunique hzero hmaskBasis hinverseBasis hpublicPins
  have hclaim := output_boundary_claim certificate totalAddRows
    (wireOfProduced (allYields rows externalYields)) claimed hboundary
  have hpacked : packM31 output = packM31 claimed := hselected.symm.trans hclaim
  have hvalue : output = claimed := by
    funext i
    apply Field.toZMod_injective
    simpa only [coord_packM31] using congrArg (fun q => coord q i) hpacked
  simpa [hvalue] using hsource

end S31.Functional.SSAInstalledBytecodePublicOutput
