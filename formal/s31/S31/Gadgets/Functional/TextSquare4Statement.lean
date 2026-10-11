import S31.Gadgets.Functional.TextSquare4Air
import S31.Gadgets.Bindings

/-!
Public-output binding for the generated `functional_square4.s31` program.
The theorem is conditional on a canonical four-word public input being
accepted by the assignment parser and on successful program evaluation.
-/

namespace S31.Functional.TextSquare4Statement

open S31

def computedEnv (a b c d : M31) : S31.Env :=
  TextSquare4Proof.inputEnv a b c d ++ [
    ("_s31_i1_0", ⟨.m31, [a * a, b * b, c * c, d * d]⟩),
    ("result", ⟨.m31,
      [(a * a) * (a * a), (b * b) * (b * b),
       (c * c) * (c * c), (d * d) * (d * d)]⟩)]

theorem environment_of_input (assignment : Assignment) (a b c d : M31)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok ⟨.m31, [a, b, c, d]⟩) :
    TextSquare4.compiled.environment assignment =
      .ok (computedEnv a b c d) := by
  have hprivateNames :
      (TextSquare4.compiled.inputs.filter
        (fun i => i.visibility == .private)).map (·.name) = [] := by decide
  have hfields : exactFields ([] : RawValues) [] = true := by decide
  have hprivateFields : exactFields assignment.privateInputs
      ((TextSquare4.compiled.inputs.filter
        (fun i => i.visibility == .private)).map (·.name)) = true := by
    rw [hprivate, hprivateNames]
    exact hfields
  have hinputs : TextSquare4.compiled.inputs =
      [{ name := "x", shape := ⟨.m31, 4⟩, visibility := .«public» }] := rfl
  have hassertions : TextSquare4.compiled.assertions = [] := rfl
  have hpublic : (Visibility.«public» == Visibility.«public») = true := by decide
  have hmap :
      TextSquare4.compiled.inputs.mapM (fun i => do
        let raw := if i.visibility == Visibility.«public» then
          assignment.publicInputs else assignment.privateInputs
        return (i.name, ← assigned raw i.name i.shape)) =
        .ok (TextSquare4Proof.inputEnv a b c d) := by
    rw [hinputs, hprivate]
    simp [List.mapM, List.mapM.loop, hpublic, hinput,
      TextSquare4Proof.inputEnv]
  simp only [Program.environment, TextSquare4Proof.text_compiler_validates,
    hprivateFields, hmap, hassertions]
  simpa only [require, pure_bind, bind_pure, computedEnv] using
    (TextSquare4Proof.text_compiler_nodes_correct a b c d)

theorem successful_output_is_fourth (assignment : Assignment)
    (a b c d : M31) (statement : List M31)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok ⟨.m31, [a, b, c, d]⟩)
    (haccepted : TextSquare4.compiled.evaluate assignment = .ok statement) :
    assigned assignment.publicOutputs "result" ⟨.m31, 4⟩ =
      .ok ⟨.m31,
        [(a * a) * (a * a), (b * b) * (b * b),
         (c * c) * (c * c), (d * d) * (d * d)]⟩ := by
  obtain ⟨values, henv, hbound⟩ :=
    Gadgets.Bindings.evaluate_ok_output_binding
      TextSquare4.compiled assignment statement haccepted
  rw [environment_of_input assignment a b c d hprivate hinput] at henv
  have hvalues : values = computedEnv a b c d := Except.ok.inj henv.symm
  subst values
  obtain ⟨actual, hlookup, hassigned⟩ :=
    hbound "result" (by simp [TextSquare4.compiled])
  have hlookup' : lookup (computedEnv a b c d) "result" =
      some ⟨.m31,
        [(a * a) * (a * a), (b * b) * (b * b),
         (c * c) * (c * c), (d * d) * (d * d)]⟩ := by
    simp [computedEnv, TextSquare4Proof.inputEnv, lookup]
  rw [hlookup'] at hlookup
  cases Option.some.inj hlookup
  exact hassigned

/-- A canonical but incorrect public result cannot be accepted, regardless of
the otherwise valid assignment and proof witness. -/
theorem forged_output_rejected (assignment : Assignment)
    (a b c d : M31) (forged : List M31)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok ⟨.m31, [a, b, c, d]⟩)
    (hforged : assigned assignment.publicOutputs "result" ⟨.m31, 4⟩ =
      .ok ⟨.m31, forged⟩)
    (hne : forged ≠
      [(a * a) * (a * a), (b * b) * (b * b),
       (c * c) * (c * c), (d * d) * (d * d)]) :
    ¬ ∃ statement, TextSquare4.compiled.evaluate assignment = .ok statement := by
  rintro ⟨statement, haccepted⟩
  have hreal := successful_output_is_fourth assignment a b c d statement
    hprivate hinput haccepted
  rw [hforged] at hreal
  exact hne (congrArg Value.words (Except.ok.inj hreal))

end S31.Functional.TextSquare4Statement
