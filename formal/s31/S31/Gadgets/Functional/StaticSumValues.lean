import S31.Gadgets.Functional.CompilerCorrespondence

/-!
Typed, source-stage sum values and exhaustive two-arm matching. `Ty.sum` is a
static value in the modeled language: `Meaning` and `Residual` each carry a
tag, but `Poly` and the emitted graph have no tag, constructor, or match node.
The tag is known during specialization, so only the selected arm is lowered.

This model proves semantic preservation of the typed total core and a concrete
local AIR correspondence. It does not verify the Python parser, effect pass,
nominal enum checks, Zig lowering, or native verifier. In particular, sums
cannot be inferred to be free when their tag depends on a witness value.
-/

namespace S31.Functional.StaticSumValues

open S31.Functional
open S31.Functional.CompilerCorrespondence

/-- Constructor and match disappear before residual polynomial lowering. -/
theorem left_erases {n : Nat} (payload : Expr Γ a)
    (onLeft : Expr (a :: Γ) t) (onRight : Expr (b :: Γ) t)
    (env : Env (Residual n) Γ) :
    specialize (Expr.matchSum (Expr.inl (b := b) payload) onLeft onRight) env =
      specialize (Expr.letValue payload onLeft) env := rfl

theorem right_erases {n : Nat} (payload : Expr Γ b)
    (onLeft : Expr (a :: Γ) t) (onRight : Expr (b :: Γ) t)
    (env : Env (Residual n) Γ) :
    specialize (Expr.matchSum (Expr.inr (a := a) payload) onLeft onRight) env =
      specialize (Expr.letValue payload onRight) env := rfl

/-- Changing an inactive arm cannot change the emitted relation. -/
theorem inactive_right_irrelevant {n : Nat} (payload : Expr Γ a)
    (onLeft : Expr (a :: Γ) .field)
    (right1 right2 : Expr (b :: Γ) .field)
    (env : Env (Residual n) Γ) :
    specialize (Expr.matchSum (Expr.inl (b := b) payload) onLeft right1) env =
      specialize (Expr.matchSum (Expr.inl (b := b) payload) onLeft right2) env := rfl

/-- A separate partial-effect model records the source evaluation order that
the total polynomial core cannot express. Constructor payload failure is
observable even though the constructor itself has no residual gate. -/
def checkedLeft {ε α β : Type} (payload : Except ε α) :
    Except ε (Sum α β) :=
  match payload with
  | .error reason => .error reason
  | .ok value => .ok (.inl value)

def checkedMatch {ε α β γ : Type} (scrutinee : Except ε (Sum α β))
    (onLeft : α → Except ε γ) (onRight : β → Except ε γ) :
    Except ε γ :=
  match scrutinee with
  | .error reason => .error reason
  | .ok (.inl value) => onLeft value
  | .ok (.inr value) => onRight value

theorem left_payload_failure_propagates {ε α β γ : Type}
    (reason : ε) (onLeft : α → Except ε γ)
    (onRight : β → Except ε γ) :
    checkedMatch (checkedLeft (.error reason)) onLeft onRight =
      .error reason := rfl

/-- A failing inactive arm does not invalidate a successful selected arm.
This is why match is erased according to its static tag, while a dynamic
circuit conditional has different totality requirements. -/
theorem inactive_right_failure_is_ignored {ε α β γ : Type}
    (payload : α) (onLeft : α → Except ε γ) (reason : ε) :
    checkedMatch (checkedLeft (β := β) (.ok payload)) onLeft
      (fun _ => .error reason) = onLeft payload := rfl

/-- A static left tag carries a dynamic four-lane payload. Matching selects
the square arm; the other arm's arithmetic is absent from the residual. -/
def matchedSquare4 : Expr [.array 4] (.array 4) :=
  .matchSum (.inl (.var .here))
    (.arrayMul (.var .here) (.var .here))
    (.arrayAdd (.var .here) (.var .here))

def directSquare4 : Expr [.array 4] (.array 4) :=
  .arrayMul (.var .here) (.var .here)

theorem matched_square4_source (input : Fin 4 → M31) :
    denote matchedSquare4 (arrayInputSource input) =
      denote directSquare4 (arrayInputSource input) := rfl

/-- Exact residual polynomial equality for every input polynomial. -/
theorem matched_square4_residual {n : Nat} (input : Fin 4 → Poly n) :
    specialize matchedSquare4 (.cons input .nil) =
      specialize directSquare4 (.cons input .nil) := rfl

/-- Consequently the complete straight-line graph, including its gate and
wire layout, is identical to direct arithmetic. -/
theorem matched_square4_same_graph :
    arrayCode matchedSquare4 = arrayCode directSquare4 := rfl

theorem matched_square4_graph_shape :
    arrayCode matchedSquare4 =
      ⟨[.apply .mul [0, 0], .apply .mul [1, 1],
        .apply .mul [2, 2], .apply .mul [3, 3]], [4, 5, 6, 7]⟩ := rfl

/-- Every arbitrary witness satisfying the selected square's modeled packed
AIR rows has exactly the source result; honest witnesses exist. The enum tag
does not add a row. This invokes the already proved local arithmetic bridge,
not the native proof verifier. -/
theorem matched_square4_graph_iff_air (inputs : List M31)
    (claimed : Fin 4 → M31) (hinputs : inputs.length = 4) :
    (arrayCode matchedSquare4).strictAccepts
      Graph.fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn claimed) ↔
      AirAccepts (fun i => inputs.getD i.val 0)
        (.mul .input .input) claimed := by
  rw [matched_square4_same_graph]
  change (arrayCode (directSource (.mul .input .input))).strictAccepts
    Graph.fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
    (List.ofFn claimed) ↔ _
  rw [← bound_source_same_graph (.mul .input .input)]
  exact strict_graph_iff_air (.mul .input .input) inputs claimed hinputs

theorem matched_square4_rejects_forged (inputs : List M31)
    (claimed : Fin 4 → M31) (hinputs : inputs.length = 4)
    (hforged : claimed ≠ fun i =>
      (inputs.getD i.val 0) * (inputs.getD i.val 0)) :
    ¬ (arrayCode matchedSquare4).strictAccepts
      Graph.fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn claimed) := by
  intro accepted
  exact forged_air_result_rejected (.mul .input .input)
    (fun i => inputs.getD i.val 0) claimed hforged
    ((matched_square4_graph_iff_air inputs claimed hinputs).mp accepted)

end S31.Functional.StaticSumValues
