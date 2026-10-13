import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAPublicABI
import Mathlib.Data.List.GetD

/-!
Structural bridge from bounded pure source bytes and decoded SSA to the
actual normalized `Program.evaluate` semantics. The named-environment proof
works for every field input, with its input-state relation explicit. Modeled
packed AIR completeness supplies the intermediate values; no final-value
comparison is assumed. Native row ownership and compiler-wide
correspondence remain separate.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAProgramEvaluate

open S31.Functional.Correspondence
open GeneralLinearSSAPublicABI
abbrev Lanes (n : Nat) := GeneralLinearSSA.Lanes n

def laneValue {n : Nat} (value : Lanes n) : S31.Value :=
  ⟨.m31, List.ofFn value⟩

private theorem lookup_shapes (env : S31.Env) (name : String) :
    S31.lookup (env.map (fun (key, value) => (key, value.shape))) name =
      (S31.lookup env name).map S31.Value.shape := by
  simp [S31.lookup, List.find?_map, Function.comp_def]

def namedBinaryNode (name lhs rhs : String)
    (op : GeneralLinearSSA.ArithmeticOp) : S31.Node :=
  { name, op := match op with
      | .add => .add | .sub => .sub | .mul => .mul,
    lhs := some lhs, rhs := some rhs }

private theorem zipMap_ofFn {n : Nat} (a b : Lanes n)
    (combine : S31.M31 → S31.M31 → S31.M31) :
    ((List.ofFn a).zip (List.ofFn b)).map
      (fun (x, y) => combine x y) =
    List.ofFn (fun i => combine (a i) (b i)) := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp

/-- The actual normalized evaluator is insensitive to unrelated named
environment entries for a binary M31 node. This is the local step theorem
used by a general named-environment fold. -/
theorem named_binary_node_eval {n : Nat} (env : S31.Env)
    (name lhs rhs : String) (op : GeneralLinearSSA.ArithmeticOp)
    (left right : Lanes n)
    (hlhs : S31.lookup env lhs = some ⟨.m31, List.ofFn left⟩)
    (hrhs : S31.lookup env rhs = some ⟨.m31, List.ofFn right⟩) :
    S31.evaluateNode env (namedBinaryNode name lhs rhs op) =
      .ok ⟨.m31, List.ofFn
        (fun i => op.eval (left i) (right i))⟩ := by
  have hshapeL :
      S31.lookup (env.map (fun (name, value) => (name, value.shape))) lhs =
        some ⟨.m31, n⟩ := by
    rw [lookup_shapes, hlhs]
    simp [S31.Value.shape]
  have hshapeR :
      S31.lookup (env.map (fun (name, value) => (name, value.shape))) rhs =
        some ⟨.m31, n⟩ := by
    rw [lookup_shapes, hrhs]
    simp [S31.Value.shape]
  have hinfer :
      S31.inferNode
        (env.map (fun (name, value) => (name, value.shape)))
        (namedBinaryNode name lhs rhs op) = .ok ⟨.m31, n⟩ := by
    have hkind : (S31.Kind.m31 == S31.Kind.m31) = true := rfl
    cases op <;>
      simp [namedBinaryNode, S31.inferNode, S31.Node.metadataValid,
        S31.Node.fields, S31.shapeOperand, S31.expectShape,
        S31.need, S31.require, hshapeL, hshapeR, hkind,
        Bind.bind, Except.bind, Except.map, Pure.pure, Except.pure]
  unfold S31.evaluateNode
  rw [hinfer]
  have hshape :
      ((⟨.m31, n⟩ : S31.Shape) == ⟨.m31, n⟩) = true := by
    change ((S31.Kind.m31 == S31.Kind.m31) && (n == n)) = true
    simp [show (S31.Kind.m31 == S31.Kind.m31) = true by rfl]
  cases op <;>
    simp [namedBinaryNode, S31.valueOperand, hlhs, hrhs,
      S31.require, S31.Value.shape, S31.Value.valid, zipMap_ofFn,
      Bind.bind, Except.bind, Pure.pure, Except.pure,
      SourceFunctionBytes.Op.eval, hshape]

def nameAt (names : List String) (id : Nat) : String :=
  names.getD id ""

def namedInstructionNode (names : List String)
    (instruction : GeneralLinearSSA.Instruction) : S31.Node :=
  namedBinaryNode (nameAt names instruction.id)
    (nameAt names instruction.lhs) (nameAt names instruction.rhs)
    instruction.op

def Carries {n : Nat} (names : List String) (env : S31.Env)
    (values : List (Lanes n)) : Prop :=
  ∀ id value, values[id]? = some value →
    S31.lookup env (nameAt names id) =
      some ⟨.m31, List.ofFn value⟩

def Absent (names : List String) (env : S31.Env)
    (next maximum : Nat) : Prop :=
  ∀ id, next ≤ id → id < maximum →
    S31.lookup env (nameAt names id) = none

def Distinct (names : List String) (maximum : Nat) : Prop :=
  ∀ i j, i < maximum → j < maximum →
    nameAt names i = nameAt names j → i = j

theorem lookup_append_some (env suffix : S31.Env)
    (name : String) (value : S31.Value)
    (h : S31.lookup env name = some value) :
    S31.lookup (env ++ suffix) name = some value := by
  unfold S31.lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp [hfind] at h
  | some pair => simpa [hfind] using h

theorem lookup_append_fresh (env : S31.Env)
    (name : String) (value : S31.Value)
    (h : S31.lookup env name = none) :
    S31.lookup (env ++ [(name, value)]) name = some value := by
  unfold S31.lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp
  | some pair => simp [hfind] at h

theorem lookup_append_other (env : S31.Env)
    (name newName : String) (value : S31.Value)
    (h : S31.lookup env name = none) (hne : name ≠ newName) :
    S31.lookup (env ++ [(newName, value)]) name = none := by
  unfold S31.lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp [Ne.symm hne]
  | some pair => simp [hfind] at h

def namedStep (names : List String) (env : S31.Env)
    (instruction : GeneralLinearSSA.Instruction) : S31.Result S31.Env := do
  let node := namedInstructionNode names instruction
  return env ++ [(node.name, ← S31.evaluateNode env node)]

/-- A single modeled AIR row extends the actual named normalized evaluator
with precisely the constrained M31 output. This uses an arbitrary current
environment and does not rely on a fixture's numeric inputs. -/
theorem named_step_of_air {n maximum : Nat} (names : List String)
    (env : S31.Env) (values : List (Lanes n))
    (instruction : GeneralLinearSSA.Instruction) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → S31.M31)
    (hrow : GeneralLinearSSA.acceptsRow values instruction output tailA tailB)
    (hcarries : Carries names env values)
    (habent : Absent names env values.length maximum)
    (hdistinct : Distinct names maximum)
    (hbudget : values.length < maximum) :
    ∃ nextEnv,
      namedStep names env instruction = .ok nextEnv ∧
      Carries names nextEnv (values ++ [output]) ∧
      Absent names nextEnv (values.length + 1) maximum := by
  obtain ⟨left, right, hid, hlhs, hrhs, hpoly⟩ := hrow
  have hvalue : output =
      (fun i => instruction.op.eval (left i) (right i)) := by
    funext i
    exact (SourceFunctionBytes.packed_iff_eval instruction.op left right
      output tailA tailB).mp hpoly i
  have hleft := hcarries instruction.lhs left hlhs
  have hright := hcarries instruction.rhs right hrhs
  have heval : S31.evaluateNode env
      (namedInstructionNode names instruction) =
        .ok ⟨.m31, List.ofFn output⟩ := by
    rw [hvalue]
    exact named_binary_node_eval env _ _ _ instruction.op left right
      hleft hright
  let nextEnv := env ++ [(nameAt names instruction.id,
    (⟨.m31, List.ofFn output⟩ : S31.Value))]
  have hstep : namedStep names env instruction = .ok nextEnv := by
    change (do
      let value ← S31.evaluateNode env
        (namedInstructionNode names instruction)
      pure (env ++ [(nameAt names instruction.id, value)])) = _
    rw [heval]
    rfl
  refine ⟨nextEnv, hstep, ?_, ?_⟩
  · intro id value hfound
    by_cases hold : id < values.length
    · have hprior : values[id]? = some value := by
        rw [List.getElem?_append_left hold] at hfound
        exact hfound
      exact lookup_append_some env _ (nameAt names id)
        ⟨.m31, List.ofFn value⟩ (hcarries id value hprior)
    · have hindex : id = values.length := by
        have hlt : id < (values ++ [output]).length :=
          (List.getElem?_eq_some_iff.mp hfound).1
        simp at hlt
        omega
      subst id
      have hsame : value = output := by
        simpa using hfound.symm
      subst value
      have hfresh : S31.lookup env (nameAt names instruction.id) = none := by
        rw [hid]
        exact habent values.length (by omega) hbudget
      simpa [nextEnv, hid] using lookup_append_fresh env
        (nameAt names instruction.id) ⟨.m31, List.ofFn output⟩ hfresh
  · intro id hnext hmax
    have hnone : S31.lookup env (nameAt names id) = none :=
      habent id (by omega) hmax
    have hne : nameAt names id ≠ nameAt names instruction.id := by
      intro heq
      have hsame := hdistinct id instruction.id hmax
        (by rw [hid]; exact hbudget) heq
      omega
    exact lookup_append_other env (nameAt names id)
      (nameAt names instruction.id) ⟨.m31, List.ofFn output⟩
      hnone hne

/-- General named normalized execution of an arbitrary complete packed AIR
trace. Every node is evaluated through the real `S31.evaluateNode` function;
the source graph may contain dead nodes, which are still executed. -/
theorem named_fold_of_air {n maximum : Nat} (names : List String)
    {values final : List (Lanes n)}
    {instructions : List GeneralLinearSSA.Instruction}
    (env : S31.Env)
    (hrows : GeneralLinearSSA.AcceptsTrace values instructions final)
    (hbudget : values.length + instructions.length = maximum)
    (hdistinct : Distinct names maximum)
    (hcarries : Carries names env values)
    (habent : Absent names env values.length maximum) :
    ∃ finalEnv,
      instructions.foldlM (namedStep names) env = .ok finalEnv ∧
      Carries names finalEnv final ∧
      Absent names finalEnv final.length maximum := by
  induction hrows generalizing env with
  | done values =>
      exact ⟨env, rfl, hcarries, habent⟩
  | @next values final instruction rest output tailA tailB hrow hrest ih =>
      have hlt : values.length < maximum := by
        simp at hbudget
        omega
      obtain ⟨nextEnv, hstep, hcarryNext, habsentNext⟩ :=
        named_step_of_air names env values instruction output tailA tailB
          hrow hcarries habent hdistinct hlt
      have hbudgetNext :
          (values ++ [output]).length + rest.length = maximum := by
        simp at hbudget ⊢
        omega
      obtain ⟨finalEnv, hfold, hcarryFinal, habsentFinal⟩ :=
        ih nextEnv hbudgetNext hcarryNext (by simpa using habsentNext)
      refine ⟨finalEnv, ?_, hcarryFinal, habsentFinal⟩
      simpa [List.foldlM_cons, hstep] using hfold

private theorem named_fold_eq_nodes (names : List String)
    (instructions : List GeneralLinearSSA.Instruction) (env : S31.Env) :
    (instructions.map (namedInstructionNode names)).foldlM
      (fun env node => do
        return env ++ [(node.name, ← S31.evaluateNode env node)]) env =
      instructions.foldlM (namedStep names) env := by
  rw [List.foldlM_map]
  rfl

/-- Structural bridge from a complete modeled arithmetic AIR trace to the
actual normalized `Program.environment` fold. The named input initializer,
fresh-name invariant and exact node graph are explicit premises; no equality
of final interpreter and source outputs is assumed. -/
theorem program_environment_follows_air {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSA.Certificate)
    (initial final : List (Lanes n)) (inputEnv : S31.Env)
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then assignment.publicInputs
        else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.instructions.map (namedInstructionNode names))
    (hassertions : program.assertions = [])
    (hrows : GeneralLinearSSA.AcceptsTrace initial
      certificate.instructions final)
    (hcarries : Carries names inputEnv initial)
    (habent : Absent names inputEnv initial.length
      (initial.length + certificate.instructions.length))
    (hdistinct : Distinct names
      (initial.length + certificate.instructions.length)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      Carries names finalEnv final := by
  obtain ⟨shapes, hvalidate⟩ := hvalid
  obtain ⟨finalEnv, hfold, hcarryFinal, _⟩ :=
    named_fold_of_air names inputEnv hrows rfl hdistinct hcarries habent
  have hnodesFold :
      program.nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← S31.evaluateNode env node)]) inputEnv =
        .ok finalEnv := by
    rw [hnodes]
    rw [named_fold_eq_nodes]
    exact hfold
  refine ⟨finalEnv, ?_, hcarryFinal⟩
  unfold S31.Program.environment
  rw [hvalidate]
  simp only [hprivate, hinputs, hassertions]
  simp only [S31.require, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at hnodesFold ⊢
  simp [hnodesFold, Pure.pure, Except.pure]

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

/-- An accepted real `Program.evaluate` binds its public output assignment to
the value selected from its actual final environment. This is independent of
how that environment was proved to agree with a source or an AIR trace. -/
theorem public_output_claim_of_environment {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (finalEnv : S31.Env) (name : String) (claimed : Lanes n)
    (words : List S31.M31)
    (henv : program.environment assignment = .ok finalEnv)
    (houtputs : program.outputs = [name])
    (hlookup : S31.lookup finalEnv name = some (laneValue claimed))
    (haccept : program.evaluate assignment = .ok words) :
    S31.assigned assignment.publicOutputs name ⟨.m31, n⟩ =
      .ok (laneValue claimed) := by
  have hagree : program.outputsAgree assignment finalEnv = .ok () := by
    unfold S31.Program.evaluate at haccept
    rw [henv] at haccept
    cases hclaimed : program.claimedWords assignment with
    | error error => simp [hclaimed, Bind.bind, Except.bind] at haccept
    | ok claim =>
        cases hout : program.outputsAgree assignment finalEnv with
        | error error =>
            simp [hclaimed, hout, Bind.bind, Except.bind] at haccept
        | ok witness =>
            cases witness
            rfl
  unfold S31.Program.outputsAgree at hagree
  rw [houtputs] at hagree
  simp only [S31.outputsAgreeNames, hlookup] at hagree
  have hshape : (laneValue claimed).shape = ⟨.m31, n⟩ := by
    simp [laneValue, S31.Value.shape]
  cases hassigned : S31.assigned assignment.publicOutputs
      name (laneValue claimed).shape with
  | error error =>
      change (match S31.assigned assignment.publicOutputs
        name (laneValue claimed).shape with
        | Except.error err => Except.error err
        | Except.ok expected => if laneValue claimed == expected then Except.ok ()
          else Except.error .publicMismatch) = Except.ok () at hagree
      simp [hassigned] at hagree
  | ok expected =>
      have heq : laneValue claimed = expected := by
        have hbeq : (laneValue claimed == expected) = true := by
          change (match S31.assigned assignment.publicOutputs
            name (laneValue claimed).shape with
            | Except.error err => Except.error err
            | Except.ok expected => if laneValue claimed == expected then Except.ok ()
              else Except.error .publicMismatch) = Except.ok () at hagree
          simpa [hassigned] using hagree
        exact value_beq_eq _ _ hbeq
      rw [← heq] at hassigned
      simpa [hshape] using hassigned

/-- An accepted real `Program.evaluate` must agree with the selected
constrained AIR value once its exact named environment has been derived.
There is no direct interpreter-vs-source output comparison premise. -/
theorem program_evaluate_claim_of_air {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSA.Certificate)
    (initial final : List (Lanes n)) (inputEnv : S31.Env)
    (claimed : Lanes n) (words : List S31.M31)
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then assignment.publicInputs
        else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.instructions.map (namedInstructionNode names))
    (hassertions : program.assertions = [])
    (houtputs : program.outputs = [nameAt names certificate.output])
    (hrows : GeneralLinearSSA.AcceptsTrace initial
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed)
    (hcarries : Carries names inputEnv initial)
    (habent : Absent names inputEnv initial.length
      (initial.length + certificate.instructions.length))
    (hdistinct : Distinct names
      (initial.length + certificate.instructions.length))
    (haccept : program.evaluate assignment = .ok words) :
    S31.assigned assignment.publicOutputs
      (nameAt names certificate.output) ⟨.m31, n⟩ =
        .ok (laneValue claimed) := by
  obtain ⟨finalEnv, henv, hcarryFinal⟩ :=
    program_environment_follows_air program assignment names certificate
      initial final inputEnv hvalid hprivate hinputs hnodes hassertions
      hrows hcarries habent hdistinct
  have hlookup := hcarryFinal certificate.output claimed houtput
  exact public_output_claim_of_environment program assignment finalEnv
    (nameAt names certificate.output) claimed words henv houtputs hlookup
    haccept

private theorem decoded_pure_output (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (hdecode : ssa.decode = some certificate) :
    certificate.output = ssa.output := by
  unfold GeneralLinearSSA.EmittedSSA.decode at hdecode
  simp_all
  have hbind := hdecode.2.2.2.2.2
  cases hinstructions : ssa.nodes.mapM
      GeneralLinearSSA.EmittedNode.decode with
  | none => simp [hinstructions, Option.bind] at hbind
  | some instructions =>
      have hcertificate :
          ({ inputs := ssa.inputs.length, instructions,
             output := ssa.output } : GeneralLinearSSA.Certificate) =
            certificate := Option.some.inj (by
              simpa [hinstructions, Option.bind] using hbind)
      rw [← hcertificate]

private theorem length_of_option_mapM {α β : Type} (xs : List α)
    (f : α → Option β) (ys : List β)
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      simp at h
      cases h
      rfl
  | cons x xs ih =>
      simp only [List.mapM_cons] at h
      cases hf : f x with
      | none => simp [hf] at h
      | some y =>
          cases htail : xs.mapM f with
          | none => simp [hf, htail] at h
          | some rest =>
              simp [hf, htail] at h
              cases h
              simpa using ih rest htail

private theorem decoded_pure_roster (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (hdecode : ssa.decode = some certificate) :
    ssa.names.Nodup ∧ certificate.inputs = ssa.inputs.length ∧
      certificate.instructions.length = ssa.nodes.length := by
  unfold GeneralLinearSSA.EmittedSSA.decode at hdecode
  simp at hdecode
  have hnames : ssa.names.Nodup := hdecode.2.2.2.1.1
  have hbind := hdecode.2.2.2.2.2
  cases hinstructions : ssa.nodes.mapM
      GeneralLinearSSA.EmittedNode.decode with
  | none => simp [hinstructions, Option.bind] at hbind
  | some instructions =>
      have hcertificate :
          ({ inputs := ssa.inputs.length, instructions,
             output := ssa.output } : GeneralLinearSSA.Certificate) =
            certificate := Option.some.inj (by
              simpa [hinstructions, Option.bind] using hbind)
      have hlength : instructions.length = ssa.nodes.length := by
        exact length_of_option_mapM ssa.nodes
          GeneralLinearSSA.EmittedNode.decode instructions hinstructions
      rw [← hcertificate]
      exact ⟨hnames, rfl, hlength⟩

private theorem distinct_of_nodup (names : List String) (maximum : Nat)
    (hmax : maximum ≤ names.length) (hnames : names.Nodup) :
    Distinct names maximum := by
  intro i j hi hj heq
  have hi' : i < names.length := by omega
  have hj' : j < names.length := by omega
  have hnamesEq : names[i] = names[j] := by
    simpa only [nameAt, List.getD_eq_getElem names "" hi',
      List.getD_eq_getElem names "" hj'] using heq
  exact (List.Nodup.getElem_inj_iff hnames).mp hnamesEq

/-- Executable structural alignment between the source-derived roster and
the positional certificate. This compares every ordered node, resolved
operand and operation; it does not compare evaluated output values. -/
def checkPureAlignment (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate) : Bool :=
  decide (expectedPureNodes ssa = some
    (certificate.instructions.map (namedInstructionNode ssa.names)))

theorem checked_pure_alignment (ssa : GeneralLinearSSA.EmittedSSA)
    (certificate : GeneralLinearSSA.Certificate)
    (hcheck : checkPureAlignment ssa certificate = true) :
    expectedPureNodes ssa = some
      (certificate.instructions.map (namedInstructionNode ssa.names)) := by
  exact of_decide_eq_true (by simpa [checkPureAlignment] using hcheck)

theorem pure_alignment_fixture :
    checkPureAlignment GeneralLinearSSA.subtractionThenDoubleEmitted
      GeneralLinearSSA.subtractionThenDouble = true := by decide

theorem pure_alignment_mutations_rejected :
    checkPureAlignment
      { GeneralLinearSSA.subtractionThenDoubleEmitted with
        nodes := [
          { id := 2, name := "delta", op := "add", lhs := 0, rhs := 1 },
          { id := 3, name := "doubled", op := "add", lhs := 2, rhs := 2 }] }
      GeneralLinearSSA.subtractionThenDouble = false ∧
    checkPureAlignment
      { GeneralLinearSSA.subtractionThenDoubleEmitted with
        nodes := [
          { id := 2, name := "delta", op := "sub", lhs := 1, rhs := 0 },
          { id := 3, name := "doubled", op := "add", lhs := 2, rhs := 2 }] }
      GeneralLinearSSA.subtractionThenDouble = false := by decide

private def subtractionProgram : S31.Program :=
  { name := "subtraction_twice",
    inputs := [
      { name := "a", shape := ⟨.m31, 1⟩, visibility := .private },
      { name := "b", shape := ⟨.m31, 1⟩, visibility := .private }],
    nodes := [
      { name := "delta", op := .sub, lhs := some "a", rhs := some "b" },
      { name := "doubled", op := .add,
        lhs := some "delta", rhs := some "delta" }],
    assertions := [], outputs := ["doubled"] }

private def subtractionAssignment : S31.Assignment :=
  { publicInputs := [], privateInputs := [("a", [3]), ("b", [2])],
    publicOutputs := [("doubled", [2])] }

/-- Concrete normalization control: the real interpreter computes ordered
subtraction before doubling. A wrong public claim and reversed subtraction
are rejected by the same evaluator. -/
theorem subtraction_interpreter_controls :
    subtractionProgram.evaluate subtractionAssignment =
      .ok ([2, 0, 0, 0, 0, 0, 0, 0].map
        RiscvRefinement.M31.reduce) ∧
    subtractionProgram.evaluate
      { subtractionAssignment with publicOutputs := [("doubled", [S31.modulus - 2])] } =
        .error .publicMismatch ∧
    ({ subtractionProgram with nodes :=
      [{ name := "delta", op := .sub, lhs := some "b", rhs := some "a" },
       { name := "doubled", op := .add,
         lhs := some "delta", rhs := some "delta" }] }).evaluate
      subtractionAssignment = .error .publicMismatch := by decide

/-- For every field input and every normalized assignment accepted by the
real interpreter, exact source/certificate and relation graph checks force
its public output to equal the independently parsed source term. The input
initializer and indexed-name alignment are explicit correspondence premises;
the theorem does not compare the two final outputs in a checker. -/
theorem checked_pure_source_program_evaluate {n : Nat}
    (sourceBytes : List Nat) (certificateBytes relationBytes : String)
    (ssa : GeneralLinearSSA.EmittedSSA)
    (meaning : GeneralLinearSSA.Term)
    (certificate : GeneralLinearSSA.Certificate)
    (program : S31.Program) (assignment : S31.Assignment)
    (inputEnv : S31.Env) (values : Nat → Lanes n)
    (words : List S31.M31)
    (hsource : GeneralLinearSSASourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hrelation : checkPureSourceRelationSSA sourceBytes relationBytes ssa =
      .ok program)
    (halign : checkPureAlignment ssa certificate = true)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then assignment.publicInputs
        else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hcarries : Carries ssa.names inputEnv
      (GeneralLinearSSA.initialValues certificate.inputs values))
    (habent : Absent ssa.names inputEnv
      (GeneralLinearSSA.initialValues certificate.inputs values).length
      ((GeneralLinearSSA.initialValues certificate.inputs values).length +
        certificate.instructions.length))
    (haccept : program.evaluate assignment = .ok words) :
    GeneralLinearSSASourceBytes.denotation sourceBytes values =
      some (meaning.eval values) ∧
    ∃ outputName,
      ssa.names[ssa.output]? = some outputName ∧
      expectedPureNodes ssa = some program.nodes ∧
      S31.assigned assignment.publicOutputs outputName ⟨.m31, n⟩ =
        .ok (laneValue (meaning.eval values)) := by
  obtain ⟨hparse, _, hterm, hssa⟩ :=
    GeneralLinearSSASourceBytes.checked_source_parts sourceBytes
      certificateBytes ssa meaning certificate hsource
  have houtputId : certificate.output = ssa.output :=
    decoded_pure_output ssa certificate
      (GeneralLinearSSA.checked_emitted_certificate ssa meaning
        certificate hssa).1
  have hroster := decoded_pure_roster ssa certificate
    (GeneralLinearSSA.checked_emitted_certificate ssa meaning
      certificate hssa).1
  have hmaximum :
      (GeneralLinearSSA.initialValues certificate.inputs values).length +
          certificate.instructions.length = ssa.names.length := by
    simp [GeneralLinearSSA.initialValues,
      GeneralLinearSSA.EmittedSSA.names, hroster.2.1, hroster.2.2]
  have hdistinct : Distinct ssa.names
      ((GeneralLinearSSA.initialValues certificate.inputs values).length +
        certificate.instructions.length) :=
    distinct_of_nodup ssa.names _ (by omega) hroster.1
  have hcertificate : GeneralLinearSSA.check certificate meaning = some () :=
    (GeneralLinearSSA.checked_emitted_certificate ssa meaning certificate
      hssa).2
  obtain ⟨final, hrows, houtput⟩ :=
    GeneralLinearSSA.checked_air_complete certificate meaning values
      hcertificate
  have hrelationBase : checkPureRelationSSA relationBytes ssa = .ok program :=
    (checked_relation_name
      (GeneralLinearSSASourceBytes.parseSourceName sourceBytes)
      (checkPureRelationSSA relationBytes ssa) program hrelation).2
  obtain ⟨hbase, hnodes, hassertions, _⟩ :=
    checked_pure_relation_graph relationBytes ssa program hrelationBase
  have hnodesAligned := checked_pure_alignment ssa certificate halign
  obtain ⟨outputName, hname, _, hmatch⟩ :=
    checked_relation_ssa relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output program hbase
  have hlayout : checkRelationLayout relationBytes ssa.lane_count
      ssa.inputs outputName = .ok program := by
    simpa [checkRelationSSA, hname] using hbase
  obtain ⟨_, _, hvalid⟩ :=
    checked_relation_layout relationBytes ssa.lane_count ssa.inputs
      outputName program hlayout
  have hgraph : program.nodes =
      certificate.instructions.map (namedInstructionNode ssa.names) :=
    Option.some.inj (hnodes.symm.trans hnodesAligned)
  have hselected : program.outputs =
      [nameAt ssa.names certificate.output] := by
    rw [houtputId]
    simpa [nameAt, hname] using hmatch.2.2.2
  have hclaim := program_evaluate_claim_of_air program assignment
    ssa.names certificate
    (GeneralLinearSSA.initialValues certificate.inputs values)
    final inputEnv (meaning.eval values) words hvalid hprivate hinputs
    hgraph hassertions hselected hrows houtput hcarries habent
    hdistinct haccept
  refine ⟨?_, outputName, hname, hnodes, ?_⟩
  · simp [GeneralLinearSSASourceBytes.denotation, hparse, hterm]
  · rw [houtputId] at hclaim
    simpa [nameAt, hname] using hclaim


end S31.Functional.Correspondence.GeneralLinearSSAProgramEvaluate
