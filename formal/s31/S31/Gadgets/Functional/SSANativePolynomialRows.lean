import S31.Gadgets.Functional.SSAPublicInputBinding

/-!
Value refinement for all source arithmetic rows of the bounded direct-gate
fragment. `wire` is an address-coherent logical QM31 value map: a native Gate
lookup argument must establish that every physical row read and write uses
these values. `nativePolynomialRows` assumes that the nine production-style
QM31 operation residuals vanish at every source-row address. Exact exported
selector/address cells are supplied separately by `expectedCells`.

The source-byte grammar here is one public four-lane M31 input and output
with one to sixteen distinct static `let` additions or pointwise
multiplications. This module does not prove the native Gate lookup reduction,
commitment opening, PCS/FRI, or native verifier implementation.
-/

namespace S31.Functional.SSANativePolynomialRows

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAPublicInputBinding

/-- One local polynomial relation per checked source instruction, evaluated
at the direct-gate circuit addresses `22 + SSA id`. -/
def nativePolynomialRows (certificate : Certificate) (wire : Nat → Quad) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    accepts (encode (s31Op instruction.multiply))
      (wire (address instruction.lhs))
      (wire (address instruction.rhs))
      (wire (address instruction.id))

/-- Interpret the four exported selector integers as the polynomial
evaluator's field flags. The package checker separately range-checks these
columns and verifies their exact 512-row schedule. -/
def cellFlags (cell : ColumnCell) : Flags :=
  { add := cell.addFlag, sub := cell.subFlag, mul := cell.mulFlag,
    pointwiseMul := cell.pointwiseMulFlag }

def cellAccepts (cell : ColumnCell) (wire : Nat → Quad) : Prop :=
  accepts (cellFlags cell) (wire cell.in0) (wire cell.in1) (wire cell.out)

/-- The compiler-projected cell invokes exactly the modeled operation
polynomial at the row's three circuit addresses. -/
theorem expected_cell_polynomial_iff (certificate : Certificate)
    (instruction : Instruction) (row : NativeSourceRow)
    (wire : Nat → Quad) :
    cellAccepts (expectedCell certificate instruction row) wire ↔
      accepts (encode (s31Op instruction.multiply))
        (wire row.in0) (wire row.in1) (wire row.out) := by
  cases hmul : instruction.multiply <;>
    simp [cellAccepts, cellFlags, expectedCell, s31Op, encode, hmul]

/-- Each source instruction is matched to a projected cell at its exact
direct-gate addresses and opcode, and its nine local residuals vanish.
Membership in `observedCells` is explicit; a separate package check must
bind those cells to committed preprocessed columns and trace openings. -/
def sourceCellsEvaluated (certificate : Certificate)
    (observedCells : List ColumnCell) (wire : Nat → Quad) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ observedCells,
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      cellAccepts cell wire

theorem source_cells_imply_polynomial_rows (certificate : Certificate)
    (observedCells : List ColumnCell) (wire : Nat → Quad)
    (h : sourceCellsEvaluated certificate observedCells wire) :
    nativePolynomialRows certificate wire := by
  intro instruction hmember
  obtain ⟨cell, _, hflags0, hflags1, hflags2, hflags3,
    hin0, hin1, hout, hair⟩ := h instruction hmember
  have hflags : cellFlags cell = encode (s31Op instruction.multiply) := by
    cases hmul : instruction.multiply <;>
      simp [cellFlags, s31Op, encode, hmul,
        hflags0, hflags1, hflags2, hflags3]
  simpa only [cellAccepts, hflags, hin0, hin1, hout] using hair

/-- SIMD add and pointwise multiply commute with four-lane M31 packing. -/
theorem operation_packed (multiply : Bool) (lhs rhs : Lanes) :
    evaluate (s31Op multiply) (packM31 lhs) (packM31 rhs) =
      packM31 (instructionValue multiply lhs rhs) := by
  cases multiply <;> apply Quad.ext <;>
    simp [s31Op, evaluate, instructionValue, packM31,
      S31.Gadgets.Packed.add, S31.Gadgets.Packed.pointwise,
      Field.toZMod_add, Field.toZMod_mul]

/-- A concrete selector mutation: for input `3`, the product wire is `9`,
while changing the same row to addition would require `6`. -/
theorem changed_selector_rejected :
    ¬ accepts (encode .add) (base 3) (base 3) (base 9) := by
  intro h
  have heq := (accepts_encoded .add _ _ _).mp h
  have hfalse : (9 : F) = 6 := by
    simpa [evaluate, S31.Gadgets.Packed.add, base] using congrArg Quad.a heq
  exact (by decide : (9 : F) ≠ 6) hfalse

/-- A concrete operand mutation: changing one multiplier input from `3` to
`4` cannot retain the product output `9`. -/
theorem changed_operand_rejected :
    ¬ accepts (encode .pointwiseMul) (base 3) (base 4) (base 9) := by
  intro h
  have heq := (accepts_encoded .pointwiseMul _ _ _).mp h
  have hfalse : (9 : F) = 12 := by
    simpa [evaluate, S31.Gadgets.Packed.pointwise, base] using congrArg Quad.a heq
  exact (by decide : (9 : F) ≠ 12) hfalse

private def fits (wire : Nat → Quad) (values : List Lanes) : Prop :=
  ∀ id value, values[id]? = some value → wire (address id) = packM31 value

private theorem fits_append (wire : Nat → Quad) (values : List Lanes)
    (output : Lanes) (hfits : fits wire values)
    (houtput : wire (address values.length) = packM31 output) :
    fits wire (values ++ [output]) := by
  intro id value hget
  by_cases hprior : id < values.length
  · have hget' : values[id]? = some value := by
      simpa only [List.getElem?_append_left hprior] using hget
    exact hfits id value hget'
  · have hbound : id < (values ++ [output]).length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have hid : id = values.length := by simp at hbound; omega
    subst id
    have hvalue : value = output := by simpa using hget.symm
    subst value
    exact houtput

private theorem row_output (wire : Nat → Quad) (instruction : Instruction)
    (lhs rhs : Lanes)
    (hleft : wire (address instruction.lhs) = packM31 lhs)
    (hright : wire (address instruction.rhs) = packM31 rhs)
    (hrow : accepts (encode (s31Op instruction.multiply))
      (wire (address instruction.lhs)) (wire (address instruction.rhs))
      (wire (address instruction.id))) :
    wire (address instruction.id) =
      packM31 (instructionValue instruction.multiply lhs rhs) := by
  rw [hleft, hright] at hrow
  exact ((accepts_encoded (s31Op instruction.multiply) _ _ _).mp hrow).trans
    (operation_packed instruction.multiply lhs rhs)

/-- If an executable SSA run succeeds, polynomial acceptance at its native
addresses propagates the packed input through every produced wire. `wire`
being one coherent map is the explicit Gate lookup value premise. -/
theorem source_rows_refine_execution (instructions : List Instruction)
    (initial final : List Lanes) (wire : Nat → Quad)
    (hinitial : fits wire initial)
    (hrows : ∀ instruction ∈ instructions,
      accepts (encode (s31Op instruction.multiply))
        (wire (address instruction.lhs))
        (wire (address instruction.rhs))
        (wire (address instruction.id)))
    (hrun : instructions.foldlM executeStep initial = some final) :
    fits wire final := by
  induction instructions generalizing initial with
  | nil =>
      simp only [List.foldlM_nil] at hrun
      cases hrun
      exact hinitial
  | cons instruction rest ih =>
      have hrow := hrows instruction (by simp)
      have htail : ∀ item ∈ rest,
          accepts (encode (s31Op item.multiply))
            (wire (address item.lhs)) (wire (address item.rhs))
            (wire (address item.id)) := by
        intro item hmem
        exact hrows item (by simp [hmem])
      simp only [List.foldlM_cons] at hrun
      cases hid : instruction.id == initial.length with
      | false =>
          have hneq : instruction.id ≠ initial.length := of_decide_eq_false hid
          simp [executeStep, hneq] at hrun
      | true =>
          have heq : instruction.id = initial.length := of_decide_eq_true hid
          cases hleft : initial[instruction.lhs]? with
          | none => simp [executeStep, heq, hleft] at hrun
          | some lhs =>
              cases hright : initial[instruction.rhs]? with
              | none => simp [executeStep, heq, hleft, hright] at hrun
              | some rhs =>
                  let output := instructionValue instruction.multiply lhs rhs
                  have hstep : executeStep initial instruction =
                      some (initial ++ [output]) := by
                    simp [executeStep, heq, hleft, hright, output]
                  rw [hstep] at hrun
                  have houtput : wire (address initial.length) =
                      packM31 output := by
                    rw [← heq]
                    exact row_output wire instruction lhs rhs
                      (hinitial instruction.lhs lhs hleft)
                      (hinitial instruction.rhs rhs hright) hrow
                  exact ih (initial ++ [output])
                    (fits_append wire initial output hinitial houtput) htail hrun

/-- Local arithmetic equations plus a coherent address map determine the
selected source wire for every accepted normalized SSA execution. -/
theorem selected_wire_matches_execution (certificate : Certificate)
    (wire : Nat → Quad) (input output : Lanes)
    (hinput : wire (address 0) = packM31 input)
    (hrows : nativePolynomialRows certificate wire)
    (hexecute : executeNormalized certificate input = some output) :
    wire (address certificate.output) = packM31 output := by
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselected : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have hstart : fits wire [input] := by
        intro id value hget
        cases id with
        | zero =>
            have hv : value = input := by simpa using hget.symm
            simpa [hv, address] using hinput
        | succ id => simp at hget
      exact source_rows_refine_execution certificate.instructions [input]
        final wire hstart hrows hrun certificate.output output hselected

/-- Actual source bytes, normalized bytes, projected source AIR cells and
the previously proved public-input boundary share the same certificate.
All source arithmetic outputs then have their source meaning under a single
coherent logical wire map and locally accepted polynomial rows. -/
theorem checked_source_polynomial_output
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input : Lanes)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hboundary : InputBoundary certificate totalAddRows wire input)
    (hrows : sourceCellsEvaluated certificate observedCells wire) :
    observedCells = expectedCells certificate totalAddRows ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
          wire (address certificate.output) = packM31 output := by
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
  have hinputWire : wire (address 0) = packM31 input := by
    simpa [address] using packed_input_bound certificate totalAddRows wire input hboundary
  exact ⟨hcells, output, hdenotation,
    selected_wire_matches_execution certificate wire input output
      hinputWire (source_cells_imply_polynomial_rows certificate observedCells
        wire hrows) hexecute⟩

end S31.Functional.SSANativePolynomialRows
