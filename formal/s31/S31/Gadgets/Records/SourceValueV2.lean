import S31.Gadgets.Functional.Correspondence.GeneralLinearSSA

/-!
The value step for the bounded nominal-record source fragment. A record field
is a source expression selecting one already computed M31 wire. The record
constructor supplies an ordered list of selectors; aliases are permitted.
The shared SSA instruction list is checked separately for every selected
field, then the general SSA execution theorem gives every field value for
arbitrary input words. This model does not parse source bytes or JSON and
does not authenticate proof openings.
-/

namespace S31.Gadgets.Records.SourceValueV2

open S31.Functional.Correspondence.GeneralLinearSSA

structure RecordProgram where
  inputs : Nat
  instructions : List Instruction
  fields : List Nat
deriving Repr

def fieldCertificate (program : RecordProgram) (wire : Nat) : Certificate :=
  { inputs := program.inputs
    instructions := program.instructions
    output := wire }

def Checked (program : RecordProgram) (sourceFields : List Term) : Prop :=
  List.Forall₂ (fun wire source => check (fieldCertificate program wire) source = some ())
    program.fields sourceFields

def evaluateFields {n : Nat} (program : RecordProgram)
    (inputs : Nat → Lanes n) : List (Option (Lanes n)) :=
  program.fields.map fun wire => execute (fieldCertificate program wire) inputs

private theorem checked_fields_aux {n : Nat} (program : RecordProgram)
    (wires : List Nat) (sourceFields : List Term) (inputs : Nat → Lanes n)
    (accepted : List.Forall₂
      (fun wire source => check (fieldCertificate program wire) source = some ())
      wires sourceFields) :
    wires.map (fun wire => execute (fieldCertificate program wire) inputs) =
      sourceFields.map (fun term => some (term.eval inputs)) := by
  induction accepted with
  | nil => rfl
  | @cons wire source restWires restSources head tail ih =>
      simp only [List.map_cons]
      rw [checked_execution (fieldCertificate program wire) source inputs head]
      exact congrArg (List.cons (some (source.eval inputs))) ih

/-- Every constructor field selects exactly its source term, including
repeated selectors and fields written in a different constructor order. -/
theorem checked_fields {n : Nat} (program : RecordProgram)
    (sourceFields : List Term) (inputs : Nat → Lanes n)
    (accepted : Checked program sourceFields) :
    evaluateFields program inputs =
      sourceFields.map (fun term => some (term.eval inputs)) := by
  exact checked_fields_aux program program.fields sourceFields inputs accepted

def pairProgram : RecordProgram :=
  { inputs := 4
    instructions :=
      [{ id := 4, lhs := 0, rhs := 3, op := .mul },
       { id := 5, lhs := 4, rhs := 1, op := .add }]
    fields := [5, 1] }

def pairSourceFields : List Term :=
  [.binary .add (.binary .mul (.input 0) (.input 3)) (.input 1),
   .input 1]

theorem pair_checked : Checked pairProgram pairSourceFields := by
  unfold Checked pairProgram pairSourceFields fieldCertificate
  decide

theorem pair_value_correspondence (inputs : Nat → Lanes 1) :
    evaluateFields pairProgram inputs =
      pairSourceFields.map (fun term => some (term.eval inputs)) :=
  checked_fields pairProgram pairSourceFields inputs pair_checked

theorem pair_swapped_field_rejected :
    ¬ Checked { pairProgram with fields := [1, 5] } pairSourceFields := by
  unfold Checked pairProgram pairSourceFields fieldCertificate
  decide

/-- Two named result leaves may name one wire. The checker admits that alias,
while rejecting a certificate that assigns its second leaf another term. -/
theorem pair_alias_checked :
    Checked { pairProgram with fields := [1, 1] } [.input 1, .input 1] := by
  unfold Checked pairProgram fieldCertificate
  decide

theorem pair_alias_split_rejected :
    ¬ Checked { pairProgram with fields := [1, 1] } [.input 1, .input 0] := by
  unfold Checked pairProgram fieldCertificate
  decide

end S31.Gadgets.Records.SourceValueV2
