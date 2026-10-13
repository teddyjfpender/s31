import S31.Gadgets.Functional.Correspondence.GeneralRecordV2ProgramAdmission

/-!
The independent record-v2 source evaluator stores canonical natural-number
representatives and evaluates add/mul modulo M31. The normalized `Program`
evaluator stores typed `M31` singleton vectors. This file relates those two
value domains at each arithmetic node; neither evaluator is defined in terms
of the other.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2ValueCorrespondence

open GeneralRecordV2SourceCorrespondence

def singleton (value : Nat) : S31.Value :=
  ⟨.m31, [RiscvRefinement.M31.reduce value]⟩

def typedNode (node : Arithmetic) : S31.Node :=
  { name := node.name, op := if node.op == "+" then .add else .mul,
    lhs := some node.lhs.wire, rhs := some node.rhs.wire }

private theorem lookup_shapes (env : S31.Env) (name : String) :
    S31.lookup (env.map (fun (key, value) => (key, value.shape))) name =
      (S31.lookup env name).map S31.Value.shape := by
  simp [S31.lookup, List.find?_map, Function.comp_def]

/-- One source arithmetic instruction and the real normalized typed evaluator
compute the same M31 word from related operands, for either admitted operator.
The source side uses `% modulus`; the typed side uses `M31.add/mul`. -/
theorem node_value (env : S31.Env) (node : Arithmetic) (lhs rhs : Nat)
    (hleft : S31.lookup env node.lhs.wire = some (singleton lhs))
    (hright : S31.lookup env node.rhs.wire = some (singleton rhs)) :
    S31.evaluateNode env (typedNode node) = .ok (singleton
      (if node.op == "+" then (lhs + rhs) % S31.modulus
       else (lhs * rhs) % S31.modulus)) := by
  have hshapeL :
      S31.lookup (env.map (fun (name, value) => (name, value.shape)))
        node.lhs.wire = some ⟨.m31, 1⟩ := by
    rw [lookup_shapes, hleft]
    rfl
  have hshapeR :
      S31.lookup (env.map (fun (name, value) => (name, value.shape)))
        node.rhs.wire = some ⟨.m31, 1⟩ := by
    rw [lookup_shapes, hright]
    rfl
  have hinfer : S31.inferNode
      (env.map (fun (name, value) => (name, value.shape)))
      (typedNode node) = .ok ⟨.m31, 1⟩ := by
    by_cases h : node.op == "+"
    · simp [typedNode, h, S31.inferNode, S31.Node.metadataValid,
        S31.Node.fields, S31.shapeOperand, S31.expectShape, S31.need,
        S31.require, hshapeL, hshapeR] <;> decide
    · simp [typedNode, h, S31.inferNode, S31.Node.metadataValid,
        S31.Node.fields, S31.shapeOperand, S31.expectShape, S31.need,
        S31.require, hshapeL, hshapeR] <;> decide
  unfold S31.evaluateNode
  rw [hinfer]
  have hshape : ((⟨.m31, 1⟩ : S31.Shape) == ⟨.m31, 1⟩) = true := by decide
  by_cases h : node.op == "+"
  · simp [typedNode, h, S31.valueOperand, hleft, hright,
      singleton, S31.Value.shape, S31.Value.valid, S31.require,
      hshape, Bind.bind, Except.bind, Pure.pure, Except.pure] <;>
      apply RiscvRefinement.M31.ext <;>
      change (RiscvRefinement.M31.add (RiscvRefinement.M31.reduce lhs)
        (RiscvRefinement.M31.reduce rhs)).val =
        (RiscvRefinement.M31.reduce ((lhs + rhs) % S31.modulus)).val
    simp [RiscvRefinement.M31.add, RiscvRefinement.M31.reduce_val, Nat.add_mod]
  · simp [typedNode, h, S31.valueOperand, hleft, hright,
      singleton, S31.Value.shape, S31.Value.valid, S31.require,
      hshape, Bind.bind, Except.bind, Pure.pure, Except.pure] <;>
      apply RiscvRefinement.M31.ext <;>
      change (RiscvRefinement.M31.mul (RiscvRefinement.M31.reduce lhs)
        (RiscvRefinement.M31.reduce rhs)).val =
        (RiscvRefinement.M31.reduce ((lhs * rhs) % S31.modulus)).val
    simp [RiscvRefinement.M31.mul, RiscvRefinement.M31.reduce_val, Nat.mul_mod]

def Related (values : List (String × Nat)) (env : S31.Env) : Prop :=
  ∀ name, S31.lookup env name = (lookupValue values name).map singleton

def typedStep (env : S31.Env) (node : Arithmetic) : S31.Result S31.Env := do
  return env ++ [(node.name, ← S31.evaluateNode env (typedNode node))]

private theorem lookup_append_new (env : S31.Env) (key : String)
    (value : S31.Value) (h : S31.lookup env key = none) :
    S31.lookup (env ++ [(key, value)]) key = some value := by
  unfold S31.lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == key) with
  | none => simp [hfind]
  | some pair => simp [hfind] at h

private theorem lookup_append_other (env : S31.Env) (key name : String)
    (value : S31.Value) (hne : name ≠ key) :
    S31.lookup (env ++ [(key, value)]) name = S31.lookup env name := by
  unfold S31.lookup
  rw [List.find?_append]
  simp [Ne.symm hne]

/-- If a fresh source node reads related scalar and typed environments, its
one-step result is related in both environments. The source evaluator prepends
the value while `Program.environment` appends it; freshness makes those
representations observationally equivalent for every wire lookup. -/
theorem step_related (values : List (String × Nat)) (env : S31.Env)
    (node : Arithmetic) (lhs rhs : Nat)
    (hrelated : Related values env)
    (hleft : lookupValue values node.lhs.wire = some lhs)
    (hright : lookupValue values node.rhs.wire = some rhs)
    (hfresh : S31.lookup env node.name = none) :
    let output := if node.op == "+" then (lhs + rhs) % S31.modulus
      else (lhs * rhs) % S31.modulus
    evalNode values node = some ((node.name, output) :: values) ∧
    typedStep env node = .ok (env ++ [(node.name, singleton output)]) ∧
    Related ((node.name, output) :: values)
      (env ++ [(node.name, singleton output)]) := by
  dsimp
  let output := if node.op == "+" then (lhs + rhs) % S31.modulus
    else (lhs * rhs) % S31.modulus
  have hsource : evalNode values node =
      some ((node.name, output) :: values) := by
    simp [evalNode, hleft, hright, output]
  have htyped := node_value env node lhs rhs
    (by simpa [Related, hleft] using hrelated node.lhs.wire)
    (by simpa [Related, hright] using hrelated node.rhs.wire)
  refine ⟨hsource, ?_, ?_⟩
  · simpa [typedStep, htyped, output, beq_iff_eq]
  · intro name
    by_cases hname : name = node.name
    · subst name
      rw [lookup_append_new env node.name (singleton output) hfresh]
      simp [lookupValue, output, beq_iff_eq]
    · rw [lookup_append_other env node.name name (singleton output) hname]
      rw [hrelated name]
      have hne : (node.name == name) = false := by simp [Ne.symm hname]
      simp [lookupValue, hne]

/-- A whole bounded record arithmetic graph preserves the scalar/typed lookup
relation at every source wire. This is an induction over arbitrary instruction
lists, not a comparison of two completed executions. Fresh names are exactly
the invariant enforced by the normalized program validator. -/
theorem nodes_related (nodes : List Arithmetic)
    (values : List (String × Nat)) (env : S31.Env)
    (hrelated : Related values env)
    (hnodup : (nodes.map Arithmetic.name).Nodup)
    (hfresh : ∀ node ∈ nodes, S31.lookup env node.name = none)
    (finalValues : List (String × Nat))
    (hsource : nodes.foldlM evalNode values = some finalValues) :
    ∃ finalEnv,
      nodes.foldlM typedStep env = .ok finalEnv ∧
      Related finalValues finalEnv := by
  induction nodes generalizing values env with
  | nil =>
      have hval : values = finalValues := by
        simpa [List.foldlM_nil] using hsource
      cases hval
      exact ⟨env, rfl, hrelated⟩
  | cons node rest ih =>
      have hnot : node.name ∉ rest.map Arithmetic.name :=
        (List.nodup_cons.mp hnodup).1
      have hrest : (rest.map Arithmetic.name).Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hnew : S31.lookup env node.name = none :=
        hfresh node (by simp)
      cases hleft : lookupValue values node.lhs.wire with
      | none => simp [List.foldlM_cons, evalNode, hleft] at hsource
      | some lhs =>
          cases hright : lookupValue values node.rhs.wire with
          | none => simp [List.foldlM_cons, evalNode, hleft, hright] at hsource
          | some rhs =>
              obtain ⟨hstepSource, hstepTyped,
                hnextRelated⟩ := step_related values env node lhs rhs
                  hrelated hleft hright hnew
              let output := if node.op == "+" then (lhs + rhs) % S31.modulus
                else (lhs * rhs) % S31.modulus
              let nextValues := (node.name, output) :: values
              let nextEnv := env ++ [(node.name, singleton output)]
              have htailSource : rest.foldlM evalNode nextValues =
                  some finalValues := by
                simpa [List.foldlM_cons, hstepSource,
                  nextValues, output, beq_iff_eq] using hsource
              have htailFresh : ∀ later ∈ rest,
                  S31.lookup nextEnv later.name = none := by
                intro later hlater
                have hne : later.name ≠ node.name := by
                  intro heq
                  apply hnot
                  exact List.mem_map.mpr ⟨later, hlater, heq⟩
                have hold : S31.lookup env later.name = none :=
                  hfresh later (by simp [hlater])
                rw [lookup_append_other env node.name later.name _ hne]
                exact hold
              obtain ⟨finalEnv, htailTyped, hfinalRelated⟩ :=
                ih nextValues nextEnv hnextRelated hrest htailFresh
                  htailSource
              exact ⟨finalEnv, by simpa [List.foldlM_cons, hstepTyped,
                nextEnv, output, beq_iff_eq] using
                htailTyped, hfinalRelated⟩

/-- The actual normalized `Program.environment` executes the same typed fold
as `typedStep`. The premises expose the validation and public/private input
loading that the fragment checker must supply for a fully automatic join. -/
theorem source_nodes_program_environment (source : Source)
    (assignment : S31.Assignment)
    (inputWords : List Nat) (inputEnv : S31.Env)
    (finalValues : List (String × Nat))
    (hvalidate : ∃ shapes, (GeneralRecordV2ProgramAdmission.sourceProgram source).validate =
      .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      (((GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.filter
        (fun i => i.visibility == .private)).map (·.name)) = true)
    (hinputs : ((GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.mapM
      (fun i => (i.name, ·) <$> S31.assigned
        (if i.visibility == S31.Visibility.public then assignment.publicInputs
          else assignment.privateInputs) i.name i.shape)) = .ok inputEnv)
    (hrelated : Related (List.zip (inputWires source) inputWords) inputEnv)
    (hnodup : (source.nodes.map Arithmetic.name).Nodup)
    (hfresh : ∀ node ∈ source.nodes, S31.lookup inputEnv node.name = none)
    (hsource : source.nodes.foldlM evalNode
      (List.zip (inputWires source) inputWords) = some finalValues) :
    ∃ finalEnv,
      (GeneralRecordV2ProgramAdmission.sourceProgram source).environment
        assignment = .ok finalEnv ∧
      Related finalValues finalEnv := by
  obtain ⟨finalEnv, hfold, hfinal⟩ := nodes_related source.nodes
    (List.zip (inputWires source) inputWords) inputEnv
    hrelated hnodup hfresh finalValues hsource
  have hprogramFold :
      ((GeneralRecordV2ProgramAdmission.sourceProgram source).nodes.foldlM
        (fun env n => do
          return env ++ [(n.name, ← S31.evaluateNode env n)]) inputEnv) =
        .ok finalEnv := by
    change ((source.nodes.map typedNode).foldlM
      (fun env n => do
        return env ++ [(n.name, ← S31.evaluateNode env n)]) inputEnv) =
        .ok finalEnv
    rw [List.foldlM_map]
    simpa [typedStep] using hfold
  rcases hvalidate with ⟨shapes, hvalidate⟩
  refine ⟨finalEnv, ?_, hfinal⟩
  have hassert :
      (GeneralRecordV2ProgramAdmission.sourceProgram source).assertions = [] := rfl
  simpa [S31.Program.environment, hvalidate, hprivate,
    hinputs, S31.require, hassert] using hprogramFold

/-- Every source result selector, including repeated aliases and reordered
record fields, resolves to the same value in the normalized typed environment.
This is a list theorem over all result fields, not a one-field fixture. -/
theorem result_fields_related (wires : List String)
    (values : List (String × Nat)) (env : S31.Env)
    (hrelated : Related values env) (results : List Nat)
    (hresults : wires.mapM (lookupValue values) = some results) :
    wires.mapM (S31.lookup env) = some (results.map singleton) := by
  induction wires generalizing results with
  | nil =>
      have hnil : results = [] := by simpa using hresults.symm
      subst results
      rfl
  | cons wire rest ih =>
      cases hwire : lookupValue values wire with
      | none => simp [List.mapM_cons, hwire] at hresults
      | some value =>
          cases htail : rest.mapM (lookupValue values) with
          | none => simp [List.mapM_cons, hwire, htail] at hresults
          | some tail =>
              have heq : value :: tail = results := by
                simpa [List.mapM_cons, hwire, htail] using hresults
              subst results
              have htailTyped := ih tail htail
              have hlookup := hrelated wire
              rw [hwire] at hlookup
              simpa [List.mapM_cons, hlookup, htailTyped]

/-- These are the remaining input-layout facts needed to join a source record
run to the normalized typed evaluator. In particular, `loaded` expresses the
public/private partition in `Program.environment`; it is not inferred from a
successful source run alone. -/
structure InputAlignment (source : Source) (assignment : S31.Assignment)
    (inputWords : List Nat) (inputEnv : S31.Env) : Prop where
  privateExact : S31.exactFields assignment.privateInputs
    (((GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.filter
      (fun i => i.visibility == .private)).map (·.name)) = true
  loaded : ((GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.mapM
    (fun i => (i.name, ·) <$> S31.assigned
      (if i.visibility == S31.Visibility.public then assignment.publicInputs
       else assignment.privateInputs) i.name i.shape)) = .ok inputEnv
  initialRelated : Related (List.zip (inputWires source) inputWords) inputEnv
  namesUnique : (source.nodes.map Arithmetic.name).Nodup
  fresh : ∀ node ∈ source.nodes, S31.lookup inputEnv node.name = none

/-- An accepted exact-source static record package, a source run, and aligned
public/private input loading determine all typed result fields. The result
field list retains constructor order and aliases; the normalized `Program`
stores its distinct output wires separately. -/
theorem checked_source_result_fields
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (inputWords : List Nat)
    (inputEnv : S31.Env) (results : List Nat)
    (haligned : InputAlignment accepted.checked.source assignment
      inputWords inputEnv)
    (hsource : evaluate accepted.checked.source inputWords = some results) :
    ∃ finalEnv,
      accepted.program.environment assignment = .ok finalEnv ∧
      (resultWires accepted.checked.source).mapM (S31.lookup finalEnv) =
        some (results.map singleton) := by
  let source := accepted.checked.source
  have hvalidated : ∃ shapes,
      (GeneralRecordV2ProgramAdmission.sourceProgram source).validate =
        .ok shapes := by
    rcases accepted.validated with ⟨shapes, hv⟩
    rw [accepted.aligned] at hv
    exact ⟨shapes, hv⟩
  have hrun :
      (source.nodes.foldlM evalNode
        (List.zip (inputWires source) inputWords)).bind
          (fun values => (resultWires source).mapM (lookupValue values)) =
        some results := by
    simp [evaluate] at hsource
    exact hsource.2
  cases hfold : source.nodes.foldlM evalNode
      (List.zip (inputWires source) inputWords) with
  | none => simp [hfold] at hrun
  | some finalValues =>
      have hresults : (resultWires source).mapM
          (lookupValue finalValues) = some results := by
        simpa [hfold] using hrun
      obtain ⟨finalEnv, henv, hrel⟩ :=
        source_nodes_program_environment source assignment inputWords
          inputEnv finalValues hvalidated haligned.privateExact
          haligned.loaded haligned.initialRelated haligned.namesUnique
          haligned.fresh hfold
      refine ⟨finalEnv, ?_, ?_⟩
      · simpa [accepted.aligned] using henv
      · exact result_fields_related (resultWires source) finalValues
          finalEnv hrel results hresults

/-! A two-field public/private example. The source result order differs from
the node order; the private `secret` words are loaded into the typed evaluator
but do not appear in its public claim vector. -/

def workedSource : Source :=
  { record := "Pair", fields := ["left", "right"], circuit := "combine",
    roots := [⟨"visible", "public"⟩, ⟨"secret", "private"⟩],
    nodes := [
      ⟨"sum", ⟨"_s31_abi_input_0", Lean.Json.null⟩,
        ⟨"_s31_abi_input_2", Lean.Json.null⟩, "+"⟩,
      ⟨"product", ⟨"sum", Lean.Json.null⟩,
        ⟨"_s31_abi_input_1", Lean.Json.null⟩, ".*"⟩],
    result := [
      ⟨"left", ⟨"product", Lean.Json.null⟩⟩,
      ⟨"right", ⟨"sum", Lean.Json.null⟩⟩] }

def workedAssignment : S31.Assignment :=
  { publicInputs := [("_s31_abi_input_0", [2]),
      ("_s31_abi_input_1", [3])],
    privateInputs := [("_s31_abi_input_2", [4]),
      ("_s31_abi_input_3", [5])],
    publicOutputs := [("product", [18]), ("sum", [6])] }

def workedInputEnv : S31.Env :=
  [("_s31_abi_input_0", singleton 2),
   ("_s31_abi_input_1", singleton 3),
   ("_s31_abi_input_2", singleton 4),
   ("_s31_abi_input_3", singleton 5)]

private theorem worked_input_related :
    Related (List.zip (inputWires workedSource) [2, 3, 4, 5])
      workedInputEnv := by
  have hwires : inputWires workedSource =
      ["_s31_abi_input_0", "_s31_abi_input_1",
       "_s31_abi_input_2", "_s31_abi_input_3"] := by decide
  rw [hwires]
  intro name
  simp only [workedInputEnv, S31.lookup, lookupValue, List.find?]
  cases h0 : ("_s31_abi_input_0" == name) <;>
    cases h1 : ("_s31_abi_input_1" == name) <;>
    cases h2 : ("_s31_abi_input_2" == name) <;>
    cases h3 : ("_s31_abi_input_3" == name) <;>
    simp [h0, h1, h2, h3]

theorem worked_source_values : evaluate workedSource [2, 3, 4, 5] =
    some [18, 6] := by decide

theorem worked_typed_public_claim :
    (GeneralRecordV2ProgramAdmission.sourceProgram workedSource).evaluate
      workedAssignment = .ok
        ([2, 3, 18, 6, 0, 0, 0, 0].map RiscvRefinement.M31.reduce) := by
  decide

theorem worked_environment_bridge :
    ∃ finalEnv,
      (GeneralRecordV2ProgramAdmission.sourceProgram workedSource).environment
        workedAssignment = .ok finalEnv ∧
      Related
        (("product", 18) :: ("sum", 6) ::
          List.zip (inputWires workedSource) [2, 3, 4, 5]) finalEnv := by
  apply source_nodes_program_environment workedSource workedAssignment
    [2, 3, 4, 5] workedInputEnv
    (("product", 18) :: ("sum", 6) ::
      List.zip (inputWires workedSource) [2, 3, 4, 5])
  · exact ⟨(GeneralRecordV2ProgramAdmission.sourceProgram
      workedSource).validate.toOption.getD [], by decide⟩
  · decide
  · decide
  · exact worked_input_related
  · decide
  · intro node hmem
    simp [workedSource] at hmem
    rcases hmem with h | h
    · subst node
      decide
    · subst node
      decide
  · decide

theorem worked_result_bridge :
    ∃ finalEnv,
      (GeneralRecordV2ProgramAdmission.sourceProgram workedSource).environment
        workedAssignment = .ok finalEnv ∧
      (resultWires workedSource).mapM (S31.lookup finalEnv) =
        some [singleton 18, singleton 6] := by
  obtain ⟨finalEnv, henv, hrel⟩ := worked_environment_bridge
  refine ⟨finalEnv, henv, ?_⟩
  have hresults :
      (resultWires workedSource).mapM
        (lookupValue
          (("product", 18) :: ("sum", 6) ::
            List.zip (inputWires workedSource) [2, 3, 4, 5])) =
        some [18, 6] := by decide
  exact result_fields_related (resultWires workedSource)
    (("product", 18) :: ("sum", 6) ::
      List.zip (inputWires workedSource) [2, 3, 4, 5])
    finalEnv hrel [18, 6] hresults

theorem worked_private_input_affects_output :
    (GeneralRecordV2ProgramAdmission.sourceProgram workedSource).evaluate
      { workedAssignment with
        privateInputs := [("_s31_abi_input_2", [5]),
          ("_s31_abi_input_3", [5])] } =
      .error .publicMismatch := by decide

theorem worked_wrong_public_output_rejected :
    (GeneralRecordV2ProgramAdmission.sourceProgram workedSource).evaluate
      { workedAssignment with
        publicOutputs := [("product", [19]), ("sum", [6])] } =
      .error .publicMismatch := by decide

end S31.Functional.Correspondence.GeneralRecordV2ValueCorrespondence
