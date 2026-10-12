import S31.Gadgets.Functional.Graph

/-!
Source-level field math combinators with no primitive beyond add and multiply.
The proofs cover every typed argument expression and every strict graph witness.
They model the mathematical meaning of the Python math library; they do not
claim that Python's balanced reduction emits this particular graph schedule.
-/

namespace S31.Functional

open Graph

/-- A nonempty sum avoids an artificial zero gate. -/
def sumExpr (first : Expr Γ .field) (rest : List (Expr Γ .field)) :
    Expr Γ .field := rest.foldl Expr.add first

/-- Nonempty static dot product. Paired terms encode equal list lengths. -/
def dotExpr (firstLeft firstRight : Expr Γ .field)
    (rest : List (Expr Γ .field × Expr Γ .field)) : Expr Γ .field :=
  sumExpr (.mul firstLeft firstRight)
    (rest.map (fun (a, b) => .mul a b))

/-- Horner evaluation with low-degree terms in `lower` and the leading
coefficient in `leading`. The final expression uses no multiply by zero. -/
def hornerExpr (x leading : Expr Γ .field)
    (lower : List (Expr Γ .field)) : Expr Γ .field :=
  lower.foldr (fun coefficient acc => .add (.mul acc x) coefficient) leading

private theorem sumExpr_denote_acc (rest : List (Expr Γ .field))
    (first : Expr Γ .field) (env : Env Meaning Γ) :
    denote (sumExpr first rest) env =
      rest.foldl (fun value term => value + denote term env) (denote first env) := by
  induction rest generalizing first with
  | nil => rfl
  | cons term tail ih =>
      simpa [sumExpr, List.foldl_cons, denote] using
        ih (.add first term)

/-- A source sum equals its modular field reduction for every typed term. -/
theorem sumExpr_denote (first : Expr Γ .field)
    (rest : List (Expr Γ .field)) (env : Env Meaning Γ) :
    denote (sumExpr first rest) env =
      rest.foldl (fun value term => value + denote term env) (denote first env) :=
  sumExpr_denote_acc rest first env

/-- Static dot is the modular sum of paired products; no witness value can
change the final result once the strict field graph accepts. -/
private theorem dot_fold (rest : List (Expr Γ .field × Expr Γ .field))
    (value : M31) (env : Env Meaning Γ) :
    (rest.map (fun (a, b) => Expr.mul a b)).foldl
      (fun result term => result + denote term env) value =
    rest.foldl (fun result pair => result +
      denote pair.1 env * denote pair.2 env) value := by
  induction rest generalizing value with
  | nil => rfl
  | cons pair tail ih =>
      cases pair with
      | mk a b =>
          simpa [List.foldl_cons, denote] using
            ih (value + denote a env * denote b env)

theorem dotExpr_denote (firstLeft firstRight : Expr Γ .field)
    (rest : List (Expr Γ .field × Expr Γ .field)) (env : Env Meaning Γ) :
    denote (dotExpr firstLeft firstRight rest) env =
      rest.foldl (fun value pair => value +
        denote pair.1 env * denote pair.2 env)
        (denote firstLeft env * denote firstRight env) := by
  rw [dotExpr, sumExpr_denote]
  exact dot_fold rest (denote firstLeft env * denote firstRight env) env

/-- `poly_eval` uses low-to-high coefficients and Horner's recurrence. -/
theorem hornerExpr_denote (x leading : Expr Γ .field)
    (lower : List (Expr Γ .field)) (env : Env Meaning Γ) :
    denote (hornerExpr x leading lower) env =
      lower.foldr (fun coefficient acc => acc * denote x env +
        denote coefficient env) (denote leading env) := by
  induction lower with
  | nil => rfl
  | cons coefficient tail ih =>
      simp only [hornerExpr, List.foldr_cons, denote]
      exact congrArg (fun value : M31 => value * denote x env +
        denote coefficient env) ih

/-- The source math combinators inherit the general strict-graph theorem:
accepted outputs are fixed for arbitrary intermediate witnesses, and honest
witnesses exist for every input. -/
theorem mathExpr_graph_accepts {n : Nat} (indices : List (Fin n))
    (e : Expr (indices.map fun _ => .field) .field)
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (specialize e (inputResidual indices)).code.strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [denote e (inputSource (fun i => inputs.getD i.val 0) indices)] :=
  program_graph_accepts indices e inputs output hinputs

theorem sumExpr_graph_accepts {n : Nat} (indices : List (Fin n))
    (first : Expr (indices.map fun _ => .field) .field)
    (rest : List (Expr (indices.map fun _ => .field) .field))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (specialize (sumExpr first rest) (inputResidual indices)).code.strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [rest.foldl (fun value term => value +
        denote term (inputSource (fun i => inputs.getD i.val 0) indices))
        (denote first (inputSource (fun i => inputs.getD i.val 0) indices))] := by
  rw [mathExpr_graph_accepts indices (sumExpr first rest) inputs output hinputs,
    sumExpr_denote]

theorem dotExpr_graph_accepts {n : Nat} (indices : List (Fin n))
    (firstLeft firstRight : Expr (indices.map fun _ => .field) .field)
    (rest : List (Expr (indices.map fun _ => .field) .field ×
      Expr (indices.map fun _ => .field) .field))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (specialize (dotExpr firstLeft firstRight rest)
      (inputResidual indices)).code.strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [rest.foldl (fun value pair => value +
        denote pair.1 (inputSource (fun i => inputs.getD i.val 0) indices) *
        denote pair.2 (inputSource (fun i => inputs.getD i.val 0) indices))
        (denote firstLeft (inputSource (fun i => inputs.getD i.val 0) indices) *
         denote firstRight (inputSource (fun i => inputs.getD i.val 0) indices))] := by
  rw [mathExpr_graph_accepts indices (dotExpr firstLeft firstRight rest)
    inputs output hinputs, dotExpr_denote]

theorem hornerExpr_graph_accepts {n : Nat} (indices : List (Fin n))
    (x leading : Expr (indices.map fun _ => .field) .field)
    (lower : List (Expr (indices.map fun _ => .field) .field))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (specialize (hornerExpr x leading lower) (inputResidual indices)).code.strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [lower.foldr (fun coefficient acc =>
        acc * denote x (inputSource (fun i => inputs.getD i.val 0) indices) +
        denote coefficient (inputSource (fun i => inputs.getD i.val 0) indices))
        (denote leading (inputSource (fun i => inputs.getD i.val 0) indices))] := by
  rw [mathExpr_graph_accepts indices (hornerExpr x leading lower)
    inputs output hinputs, hornerExpr_denote]

end S31.Functional
