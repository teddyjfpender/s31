import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator

/-! Finite typed-assignment admission for the initial effectful SSA environment. -/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsInputState

open S31.Functional.Correspondence
open GeneralLinearSSAProgramEvaluate

private def assignedInput (assignment : S31.Assignment)
    (input : S31.Input) : S31.Result (String × S31.Value) := do
  let raw := if input.visibility == S31.Visibility.«public» then
    assignment.publicInputs else assignment.privateInputs
  return (input.name, ← S31.assigned raw input.name input.shape)

def checkInputState {n : Nat} (program : S31.Program)
    (assignment : S31.Assignment) (names : List String)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (values : Nat → Lanes n) : Option S31.Env :=
  match program.inputs.mapM (assignedInput assignment) with
  | .error _ => none
  | .ok inputEnv =>
      let initial := GeneralLinearSSAEffects.initialValues certificate.inputs values
      let privateOK := S31.exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name))
      let carriesOK := (List.range initial.length).all fun id =>
        match initial[id]? with
        | none => false
        | some value => decide (S31.lookup inputEnv (nameAt names id) =
            some (laneValue value))
      let absentOK := (List.range certificate.steps.length).all
        fun offset => decide (S31.lookup inputEnv
          (nameAt names (initial.length + offset)) = none)
      if privateOK && carriesOK && absentOK then some inputEnv else none

/-- The finite check provides the input/private/freshness premises needed by
the effectful normalized interpreter theorem, without comparing outputs. -/
theorem checked_input_state {n : Nat} (program : S31.Program)
    (assignment : S31.Assignment) (names : List String)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (values : Nat → Lanes n) (inputEnv : S31.Env)
    (hcheck : checkInputState program assignment names certificate values =
      some inputEnv) :
    S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true ∧
    program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv ∧
    Carries names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs values) ∧
    Absent names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs values).length
      ((GeneralLinearSSAEffects.initialValues certificate.inputs values).length +
        certificate.steps.length) := by
  unfold checkInputState at hcheck
  cases hmap : program.inputs.mapM (assignedInput assignment) with
  | error err => simp [hmap] at hcheck
  | ok env =>
      let initial := GeneralLinearSSAEffects.initialValues certificate.inputs values
      let privateOK := S31.exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name))
      let carriesOK := (List.range initial.length).all fun id =>
        match initial[id]? with
        | none => false
        | some value => decide (S31.lookup env (nameAt names id) =
            some (laneValue value))
      let absentOK := (List.range certificate.steps.length).all
        fun offset => decide (S31.lookup env
          (nameAt names (initial.length + offset)) = none)
      simp [hmap] at hcheck
      have henv : env = inputEnv := hcheck.2
      subst env
      refine ⟨hcheck.1.1.1, ?_, ?_, ?_⟩
      · simpa [assignedInput] using hmap
      · intro id value hfound
        change initial[id]? = some value at hfound
        have hid : id < initial.length :=
          (List.getElem?_eq_some_iff.mp hfound).1
        have hpoint : (match initial[id]? with
            | none => false
            | some actual => decide (S31.lookup inputEnv
                (nameAt names id) = some (laneValue actual))) = true :=
          hcheck.1.1.2 id hid
        rw [hfound] at hpoint
        exact of_decide_eq_true hpoint
      · intro id hnext hmax
        change initial.length ≤ id at hnext
        change id < initial.length + certificate.steps.length at hmax
        have hoffset : id - initial.length < certificate.steps.length := by
          omega
        have hpoint : decide (S31.lookup inputEnv
            (nameAt names (initial.length + (id - initial.length))) = none) =
              true := by
          simpa using hcheck.1.2 (id - initial.length) hoffset
        have hid : initial.length + (id - initial.length) = id := by omega
        rw [hid] at hpoint
        exact of_decide_eq_true hpoint

end S31.Functional.Correspondence.GeneralLinearSSAEffectsInputState
