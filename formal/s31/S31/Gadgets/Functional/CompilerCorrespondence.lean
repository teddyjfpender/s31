import S31.Gadgets.Functional.Arrays
import S31.Gadgets.Functional.ArithmeticNodes
import S31.Gadgets.Air.Qm31Ops

/-!
Compositional correspondence for the total, four-lane arithmetic fragment.
The source is typed and may contain arbitrarily nested additions and
multiplications. Each normalized arithmetic step uses the executable S31
`evaluateNode`; each AIR step uses the packed QM31 operation constraints.
Intermediate values in both relations are existential proof witnesses, not
assumed to be the honest evaluation. This module does not model Python parser
or emitter correctness, Zig column emission, lookup closure, or the STARK.
-/

namespace S31.Functional.CompilerCorrespondence

open S31
open S31.Functional
open S31.Gadgets.Air.Qm31Ops

inductive Arithmetic4 where
  | input
  | add (left right : Arithmetic4)
  | mul (left right : Arithmetic4)
deriving Repr

def Arithmetic4.source {Γ : List Ty} (input : Expr Γ (.array 4)) :
    Arithmetic4 → Expr Γ (.array 4)
  | .input => input
  | .add left right => .arrayAdd (left.source input) (right.source input)
  | .mul left right => .arrayMul (left.source input) (right.source input)

def Arithmetic4.value (input : Fin 4 → M31) : Arithmetic4 → Fin 4 → M31
  | .input => input
  | .add left right => fun i => left.value input i + right.value input i
  | .mul left right => fun i => left.value input i * right.value input i

def Arithmetic4.poly {n : Nat} (input : Fin 4 → Poly n) :
    Arithmetic4 → Fin 4 → Poly n
  | .input => input
  | .add left right => fun i => .add (left.poly input i) (right.poly input i)
  | .mul left right => fun i => .mul (left.poly input i) (right.poly input i)

theorem Arithmetic4.source_specialize {Γ : List Ty} {n : Nat}
    (expression : Arithmetic4) (input : Expr Γ (.array 4))
    (env : Env (Residual n) Γ) :
    specialize (expression.source input) env =
      expression.poly (specialize input env) := by
  induction expression with
  | input => rfl
  | add left right ihLeft ihRight =>
      funext i
      exact congrArg₂ Poly.add (congrFun ihLeft i) (congrFun ihRight i)
  | mul left right ihLeft ihRight =>
      funext i
      exact congrArg₂ Poly.mul (congrFun ihLeft i) (congrFun ihRight i)

def directSource (expression : Arithmetic4) : Expr [.array 4] (.array 4) :=
  expression.source (.var .here)

/-- Static lambda application vanishes before the relation. -/
def boundSource (expression : Arithmetic4) : Expr [.array 4] (.array 4) :=
  .apply (.lambda (expression.source (.var .here))) (.var .here)

theorem source_value (expression : Arithmetic4) (input : Fin 4 → M31) :
    denote (directSource expression) (arrayInputSource input) =
      expression.value input := by
  induction expression with
  | input => rfl
  | add left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· + ·) (congrFun ihLeft i) (congrFun ihRight i)
  | mul left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· * ·) (congrFun ihLeft i) (congrFun ihRight i)

theorem bound_source_value (expression : Arithmetic4) (input : Fin 4 → M31) :
    denote (boundSource expression) (arrayInputSource input) =
      expression.value input := by
  change denote (expression.source (.var .here))
      (.cons input (arrayInputSource input)) = _
  induction expression with
  | input => rfl
  | add left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· + ·) (congrFun ihLeft i) (congrFun ihRight i)
  | mul left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· * ·) (congrFun ihLeft i) (congrFun ihRight i)

theorem bound_source_specializes (expression : Arithmetic4) :
    specialize (boundSource expression) (arrayInputResidual (n := 4)) =
      specialize (directSource expression) (arrayInputResidual (n := 4)) := by
  rw [show specialize (boundSource expression) (arrayInputResidual (n := 4)) =
    specialize (expression.source (.var .here))
      (.cons (fun i => Poly.input i) (arrayInputResidual (n := 4))) by rfl]
  rw [expression.source_specialize]
  unfold directSource
  rw [expression.source_specialize]
  rfl

theorem bound_source_same_graph (expression : Arithmetic4) :
    arrayCode (boundSource expression) = arrayCode (directSource expression) := by
  simp only [arrayCode, bound_source_specializes]

/-- An arbitrary normalized output can be reached only through actual
`evaluateNode` results at every arithmetic step. -/
inductive NormalizedAccepts (input : Fin 4 → M31) :
    Arithmetic4 → (Fin 4 → M31) → Prop where
  | input : NormalizedAccepts input .input input
  | add {left right : Arithmetic4} {leftValue rightValue output : Fin 4 → M31} :
      NormalizedAccepts input left leftValue →
      NormalizedAccepts input right rightValue →
      evaluateNode (arithmeticEnv leftValue rightValue)
        (arithmeticNode false) = .ok ⟨.m31, List.ofFn output⟩ →
      NormalizedAccepts input (.add left right) output
  | mul {left right : Arithmetic4} {leftValue rightValue output : Fin 4 → M31} :
      NormalizedAccepts input left leftValue →
      NormalizedAccepts input right rightValue →
      evaluateNode (arithmeticEnv leftValue rightValue)
        (arithmeticNode true) = .ok ⟨.m31, List.ofFn output⟩ →
      NormalizedAccepts input (.mul left right) output

/-- Packed AIR rows for every arithmetic operation in the expression tree.
Operands and outputs are arbitrary witnesses, and each row's preprocessed
opcode is fixed by the expression. -/
inductive AirAccepts (input : Fin 4 → M31) :
    Arithmetic4 → (Fin 4 → M31) → Prop where
  | input : AirAccepts input .input input
  | add {left right : Arithmetic4} {leftValue rightValue output : Fin 4 → M31} :
      AirAccepts input left leftValue →
      AirAccepts input right rightValue →
      accepts (encode (s31Op false)) (packM31 leftValue)
        (packM31 rightValue) (packM31 output) →
      AirAccepts input (.add left right) output
  | mul {left right : Arithmetic4} {leftValue rightValue output : Fin 4 → M31} :
      AirAccepts input left leftValue →
      AirAccepts input right rightValue →
      accepts (encode (s31Op true)) (packM31 leftValue)
        (packM31 rightValue) (packM31 output) →
      AirAccepts input (.mul left right) output

theorem normalized_iff_air (expression : Arithmetic4)
    (input output : Fin 4 → M31) :
    NormalizedAccepts input expression output ↔
      AirAccepts input expression output := by
  induction expression generalizing output with
  | input =>
      constructor
      · intro h; cases h; exact .input
      · intro h; cases h; exact .input
  | add left right ihLeft ihRight =>
      constructor
      · intro h
        cases h with
        | add hleft hright hnode =>
            exact .add ((ihLeft _).mp hleft) ((ihRight _).mp hright)
              ((row_iff_normalized_node false _ _ _).mpr hnode)
      · intro h
        cases h with
        | add hleft hright hrow =>
            exact .add ((ihLeft _).mpr hleft) ((ihRight _).mpr hright)
              ((row_iff_normalized_node false _ _ _).mp hrow)
  | mul left right ihLeft ihRight =>
      constructor
      · intro h
        cases h with
        | mul hleft hright hnode =>
            exact .mul ((ihLeft _).mp hleft) ((ihRight _).mp hright)
              ((row_iff_normalized_node true _ _ _).mpr hnode)
      · intro h
        cases h with
        | mul hleft hright hrow =>
            exact .mul ((ihLeft _).mpr hleft) ((ihRight _).mpr hright)
              ((row_iff_normalized_node true _ _ _).mp hrow)

theorem normalized_iff_source (expression : Arithmetic4)
    (input output : Fin 4 → M31) :
    NormalizedAccepts input expression output ↔
      output = denote (boundSource expression) (arrayInputSource input) := by
  rw [bound_source_value]
  induction expression generalizing output with
  | input =>
      constructor
      · intro h; cases h; rfl
      · intro h; subst output; exact .input
  | add left right ihLeft ihRight =>
      constructor
      · intro h
        cases h with
        | add hleft hright hnode =>
            have hl := (ihLeft _).mp hleft
            have hr := (ihRight _).mp hright
            rw [arithmeticNode_eval] at hnode
            have hout := List.ofFn_injective
              (congrArg Value.words (Except.ok.inj hnode))
            simpa [Arithmetic4.value, hl, hr] using hout.symm
      · intro h
        subst output
        apply NormalizedAccepts.add
          ((ihLeft _).mpr rfl) ((ihRight _).mpr rfl)
        simpa [Arithmetic4.value] using
          (arithmeticNode_eval false (left.value input) (right.value input))
  | mul left right ihLeft ihRight =>
      constructor
      · intro h
        cases h with
        | mul hleft hright hnode =>
            have hl := (ihLeft _).mp hleft
            have hr := (ihRight _).mp hright
            rw [arithmeticNode_eval] at hnode
            have hout := List.ofFn_injective
              (congrArg Value.words (Except.ok.inj hnode))
            simpa [Arithmetic4.value, hl, hr] using hout.symm
      · intro h
        subst output
        apply NormalizedAccepts.mul
          ((ihLeft _).mpr rfl) ((ihRight _).mpr rfl)
        simpa [Arithmetic4.value] using
          (arithmeticNode_eval true (left.value input) (right.value input))

/-- A complete local correspondence for every expression in this fragment:
source meaning, normalized evaluator and packed AIR rows accept the same
claimed four-lane output, with no honest-witness assumption. -/
theorem source_iff_normalized_iff_air (expression : Arithmetic4)
    (input output : Fin 4 → M31) :
    (output = denote (boundSource expression) (arrayInputSource input) ↔
      NormalizedAccepts input expression output) ∧
    (NormalizedAccepts input expression output ↔
      AirAccepts input expression output) := by
  exact ⟨(normalized_iff_source expression input output).symm,
    normalized_iff_air expression input output⟩

/-- The existing arbitrary-witness strict graph of the typed source has the
same accepted outputs as the complete tree of normalized arithmetic nodes and
packed AIR rows. Inputs can be any canonical four-element M31 list. -/
theorem strict_graph_iff_air (expression : Arithmetic4)
    (inputs : List M31) (claimed : Fin 4 → M31)
    (hinputs : inputs.length = 4) :
    (arrayCode (boundSource expression)).strictAccepts
      Graph.fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn claimed) ↔
    AirAccepts (fun i => inputs.getD i.val 0) expression claimed := by
  rw [arrayCode_accepts (boundSource expression) inputs
    (List.ofFn claimed) hinputs]
  constructor
  · intro h
    apply (normalized_iff_air expression _ claimed).mp
    apply (normalized_iff_source expression _ claimed).mpr
    exact List.ofFn_injective h
  · intro h
    apply congrArg List.ofFn
    apply (normalized_iff_source expression _ claimed).mp
    exact (normalized_iff_air expression _ claimed).mpr h

theorem forged_air_result_rejected (expression : Arithmetic4)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ expression.value input) :
    ¬ AirAccepts input expression claimed := by
  intro h
  apply hforged
  exact (normalized_iff_source expression input claimed).mp
    ((normalized_iff_air expression input claimed).mpr h) |>.trans
      (bound_source_value expression input)

/-- A concrete nested circuit with two branches and four arithmetic rows. -/
def squarePlusCube : Arithmetic4 :=
  .add (.mul .input .input) (.mul (.mul .input .input) .input)

theorem square_plus_cube_air (input claimed : Fin 4 → M31) :
    AirAccepts input squarePlusCube claimed ↔
      claimed = fun i => input i * input i +
        (input i * input i) * input i := by
  rw [← normalized_iff_air, normalized_iff_source,
    bound_source_value]
  rfl

end S31.Functional.CompilerCorrespondence
