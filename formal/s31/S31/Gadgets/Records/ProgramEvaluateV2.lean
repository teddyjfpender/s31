import S31.Gadgets.Records.SourceBytesV2
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAProgramEvaluate

/-!
Bridge from the bounded exact-byte record value certificate to the actual
normalized `Program.environment` and public-output checks. The theorem is
parametric in the input values and an arbitrary accepted AIR trace. The
source/relation graph, typed assignment, and public-output roster alignment
are explicit premises; production Python/JSON equivalence and authenticated
native rows are not established here.
-/

namespace S31.Gadgets.Records.ProgramEvaluateV2

open S31.Functional.Correspondence
open GeneralLinearSSA
open GeneralLinearSSAProgramEvaluate
open S31.Gadgets.Records.SourceValueV2
open S31.Gadgets.Records.SourceBytesV2

/-- Every constructor leaf, including duplicate references, is fixed by the
same complete arithmetic trace. The checker enforces the whole shared graph
for every leaf, so an unused bad node cannot be hidden by a projection. -/
theorem accepted_trace_fields {n : Nat} (record : RecordProgram)
    (sources : List Term) (inputs : Nat → GeneralLinearSSA.Lanes n)
    (final : List (GeneralLinearSSA.Lanes n))
    (hchecked : Checked record sources)
    (hrows : AcceptsTrace (initialValues record.inputs inputs)
      record.instructions final) :
    List.Forall₂ (fun wire source =>
      final[wire]? = some (source.eval inputs)) record.fields sources := by
  have aux : ∀ (wires : List Nat) (terms : List Term),
      List.Forall₂ (fun wire source =>
        check (fieldCertificate record wire) source = some ()) wires terms →
      List.Forall₂ (fun wire source =>
        final[wire]? = some (source.eval inputs)) wires terms := by
    intro wires terms h
    induction h with
    | nil => exact .nil
    | @cons wire source wires sources hcheck htail ih =>
        have hsource := checked_execution (fieldCertificate record wire)
          source inputs hcheck
        have hrun := accepted_trace_executes hrows
        have hvalue : final[wire]? = some (source.eval inputs) := by
          simpa [execute, fieldCertificate, hrun] using hsource
        exact .cons hvalue ih
  exact aux record.fields sources hchecked

/-- The actual named normalized evaluator carries every checked source
field value in its final environment once the source-derived graph and input
state are aligned. No output-value equality is assumed. -/
theorem environment_fields_of_trace {n : Nat}
    (parsed : Parsed) (program : S31.Program)
    (assignment : S31.Assignment) (names : List String)
    (inputs : Nat → GeneralLinearSSA.Lanes n) (inputEnv : S31.Env)
    (final : List (GeneralLinearSSA.Lanes n))
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes = parsed.program.instructions.map
      (namedInstructionNode names))
    (hassertions : program.assertions = [])
    (hrows : AcceptsTrace (initialValues parsed.program.inputs inputs)
      parsed.program.instructions final)
    (hcarries : Carries names inputEnv
      (initialValues parsed.program.inputs inputs))
    (habent : Absent names inputEnv
      (initialValues parsed.program.inputs inputs).length
      ((initialValues parsed.program.inputs inputs).length +
        parsed.program.instructions.length))
    (hdistinct : Distinct names
      ((initialValues parsed.program.inputs inputs).length +
        parsed.program.instructions.length)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      List.Forall₂ (fun wire source =>
        S31.lookup finalEnv (nameAt names wire) =
          some (laneValue (source.eval inputs)))
        parsed.program.fields parsed.sourceFields := by
  let certificate : Certificate :=
    { inputs := parsed.program.inputs,
      instructions := parsed.program.instructions, output := 0 }
  obtain ⟨finalEnv, henv, hcarry⟩ :=
    program_environment_follows_air program assignment names certificate
      (initialValues parsed.program.inputs inputs) final inputEnv
      hvalid hprivate hinputs hnodes hassertions hrows
      hcarries habent hdistinct
  have hfields := accepted_trace_fields parsed.program parsed.sourceFields
    inputs final parsed.checked hrows
  have aux : ∀ (wires : List Nat) (terms : List Term),
      List.Forall₂ (fun wire source =>
        final[wire]? = some (source.eval inputs)) wires terms →
      List.Forall₂ (fun wire source =>
        S31.lookup finalEnv (nameAt names wire) =
          some (laneValue (source.eval inputs))) wires terms := by
    intro wires terms h
    induction h with
    | nil => exact .nil
    | @cons wire source wires sources hfield htail ih =>
        exact .cons (hcarry wire (source.eval inputs) hfield) ih
  exact ⟨finalEnv, henv, aux parsed.program.fields parsed.sourceFields hfields⟩

private theorem value_beq_eq (a b : S31.Value)
    (h : (a == b) = true) : a = b := by
  cases a with
  | mk ak aw =>
    cases b with
    | mk bk bw =>
      change S31.instBEqValue.beq ⟨ak, aw⟩ ⟨bk, bw⟩ = true at h
      cases ak <;> cases bk
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, S31.instBEqValue.beq,
            S31.instBEqKind.beq] using h)
        simp [hw]
      · simp only [S31.instBEqValue.beq, BEq.beq,
          S31.instBEqKind.beq, Bool.and_eq_true] at h
        cases h.1
      · simp only [S31.instBEqValue.beq, BEq.beq,
          S31.instBEqKind.beq, Bool.and_eq_true] at h
        cases h.1
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, S31.instBEqValue.beq,
            S31.instBEqKind.beq] using h)
        simp [hw]

/-- Successful checking of a list of public outputs checks each member,
even when record fields alias one named output wire. -/
theorem outputs_agree_member (assignment : S31.Assignment)
    (env : S31.Env) (outputs : List String) (name : String)
    (actual : S31.Value)
    (hagree : S31.outputsAgreeNames assignment env outputs = .ok ())
    (hmember : name ∈ outputs)
    (hlookup : S31.lookup env name = some actual) :
    S31.assigned assignment.publicOutputs name actual.shape = .ok actual := by
  induction outputs with
  | nil => simp at hmember
  | cons head tail ih =>
      simp only [List.mem_cons] at hmember
      unfold S31.outputsAgreeNames at hagree
      cases hhead : S31.lookup env head with
      | none => simp [hhead] at hagree
      | some headValue =>
          cases hassigned : S31.assigned assignment.publicOutputs head
              headValue.shape with
          | error err => simp [hhead, hassigned] at hagree
          | ok expected =>
              by_cases heq : (headValue == expected) = true
              · have htail : S31.outputsAgreeNames assignment env tail =
                    .ok () := by simpa [hhead, hassigned, heq] using hagree
                cases hmember with
                | inl hsame =>
                    subst head
                    have hactual : headValue = actual :=
                      Option.some.inj (hhead.symm.trans hlookup)
                    have hvalue : headValue = expected :=
                      value_beq_eq headValue expected heq
                    subst actual
                    simpa [hvalue] using hassigned
                | inr hin => exact ih htail hin
              · simp [hhead, hassigned, heq] at hagree

/-- If the accepted normalized evaluator has the source-derived input and
node graph, every declared public record field claim equals its parsed source
value. The theorem permits repeated result fields that name one wire. -/
theorem program_evaluate_fields_of_trace {n : Nat}
    (bytes : List Nat) (parsed : Parsed)
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (inputs : Nat → GeneralLinearSSA.Lanes n)
    (inputEnv : S31.Env) (final : List (GeneralLinearSSA.Lanes n))
    (words : List S31.M31)
    (hparse : parseBytes bytes = some parsed)
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes = parsed.program.instructions.map
      (namedInstructionNode names))
    (hassertions : program.assertions = [])
    (houtputs : ∀ wire ∈ parsed.program.fields,
      nameAt names wire ∈ program.outputs)
    (hrows : AcceptsTrace (initialValues parsed.program.inputs inputs)
      parsed.program.instructions final)
    (hcarries : Carries names inputEnv
      (initialValues parsed.program.inputs inputs))
    (habent : Absent names inputEnv
      (initialValues parsed.program.inputs inputs).length
      ((initialValues parsed.program.inputs inputs).length +
        parsed.program.instructions.length))
    (hdistinct : Distinct names
      ((initialValues parsed.program.inputs inputs).length +
        parsed.program.instructions.length))
    (haccept : program.evaluate assignment = .ok words) :
    List.Forall₂ (fun wire source =>
      S31.assigned assignment.publicOutputs (nameAt names wire) ⟨.m31, n⟩ =
        .ok (laneValue (source.eval inputs)))
      parsed.program.fields parsed.sourceFields ∧
    denotation bytes inputs =
      some (parsed.sourceFields.map (fun term => term.eval inputs)) := by
  obtain ⟨finalEnv, henv, hfieldValues⟩ :=
    environment_fields_of_trace parsed program assignment names inputs
      inputEnv final hvalid hprivate hinputs hnodes hassertions hrows
      hcarries habent hdistinct
  have hagree : program.outputsAgree assignment finalEnv = .ok () := by
    unfold S31.Program.evaluate at haccept
    rw [henv] at haccept
    cases hclaimed : program.claimedWords assignment with
    | error err => simp [hclaimed, Bind.bind, Except.bind] at haccept
    | ok claim =>
        cases hout : program.outputsAgree assignment finalEnv with
        | error err => simp [hclaimed, hout, Bind.bind, Except.bind] at haccept
        | ok witness => cases witness; rfl
  constructor
  · unfold S31.Program.outputsAgree at hagree
    have aux : ∀ (wires : List Nat) (terms : List Term),
        List.Forall₂ (fun wire source =>
          S31.lookup finalEnv (nameAt names wire) =
            some (laneValue (source.eval inputs))) wires terms →
        (∀ wire ∈ wires, nameAt names wire ∈ program.outputs) →
        List.Forall₂ (fun wire source =>
          S31.assigned assignment.publicOutputs (nameAt names wire)
            ⟨.m31, n⟩ = .ok (laneValue (source.eval inputs)))
          wires terms := by
      intro wires terms hfields hmember
      induction hfields with
      | nil => exact .nil
      | @cons wire source wires sources hfield htail ih =>
          have hhead : nameAt names wire ∈ program.outputs :=
            hmember wire (by simp)
          have htailMember : ∀ w ∈ wires,
              nameAt names w ∈ program.outputs := by
            intro w hw
            exact hmember w (by simp [hw])
          have hassigned := outputs_agree_member assignment finalEnv
            program.outputs (nameAt names wire)
            (laneValue (source.eval inputs)) hagree hhead hfield
          have hshape : (laneValue (source.eval inputs)).shape = ⟨.m31, n⟩ := by
            simp [laneValue, S31.Value.shape]
          exact .cons (by simpa [hshape] using hassigned) (ih htailMember)
    exact aux parsed.program.fields parsed.sourceFields hfieldValues houtputs
  · simp [denotation, hparse]

def pairNames : List String :=
  ["_s31_abi_input_0", "_s31_abi_input_1",
   "_s31_abi_input_2", "_s31_abi_input_3", "p", "q"]

def pairNormalized : S31.Program :=
  { name := "mix",
    inputs := [
      { name := "_s31_abi_input_0", shape := ⟨.m31, 1⟩, visibility := .public },
      { name := "_s31_abi_input_1", shape := ⟨.m31, 1⟩, visibility := .public },
      { name := "_s31_abi_input_2", shape := ⟨.m31, 1⟩, visibility := .private },
      { name := "_s31_abi_input_3", shape := ⟨.m31, 1⟩, visibility := .private }],
    nodes := [
      { name := "p", op := .mul, lhs := some "_s31_abi_input_0",
        rhs := some "_s31_abi_input_3" },
      { name := "q", op := .add, lhs := some "p",
        rhs := some "_s31_abi_input_1" }],
    assertions := [], outputs := ["q", "_s31_abi_input_1"] }

def pairAssignment : S31.Assignment :=
  { publicInputs := [("_s31_abi_input_0", [2]),
      ("_s31_abi_input_1", [3])],
    privateInputs := [("_s31_abi_input_2", [0]),
      ("_s31_abi_input_3", [7])],
    publicOutputs := [("q", [17]), ("_s31_abi_input_1", [3])] }

/-- The modeled positional record graph has exactly the native normalized
node order and output aliases for the checked byte source. -/
theorem pair_graph_alignment :
    pairNormalized.nodes = pairProgram.instructions.map
      (namedInstructionNode pairNames) ∧
    pairNormalized.outputs = pairProgram.fields.map (nameAt pairNames) := by
  decide

/-- Concrete nonvacuity control for the actual normalized evaluator: it
accepts the four claimed public words and rejects a changed result claim. -/
theorem pair_evaluator_controls :
    pairNormalized.evaluate pairAssignment =
      .ok ([2, 3, 17, 3, 0, 0, 0, 0].map RiscvRefinement.M31.reduce) ∧
    pairNormalized.evaluate
      { pairAssignment with publicOutputs :=
        [("q", [18]), ("_s31_abi_input_1", [3])] } =
      .error .publicMismatch := by
  decide

end S31.Gadgets.Records.ProgramEvaluateV2
