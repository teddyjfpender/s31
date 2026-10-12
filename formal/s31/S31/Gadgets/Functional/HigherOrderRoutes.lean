import S31.Gadgets.Functional.Graph

/-!
A typed scalar analogue of the generated higher-order source corpus. A
factory captures `rhs` and returns a function of `v`; that function can be
bound locally or passed through a higher-order helper. All routes specialize
to the same two-node field graph as `x*x + y`.

These are laws of the typed Lean source core. The pinned Python corpus checks
that the real source compiler implements the corresponding routes for many
concrete programs; neither piece alone proves the entire Python compiler.
-/

namespace S31.Functional

open Graph

/-- Input context is `[x, y]`. -/
def directSquarePlus : Expr [.field, .field] .field :=
  .add (.mul (.var .here) (.var .here)) (.var (.there .here))

/-- `fun(rhs) => fun(v) => v*v + rhs`, with both values static closures. -/
def squarePlusFactory : Expr [.field, .field]
    (.arrow .field (.arrow .field .field)) :=
  .lambda (.lambda
    (.add (.mul (.var .here) (.var .here)) (.var (.there .here))))

def squarePlusViaFactory : Expr [.field, .field] .field :=
  .apply (.apply squarePlusFactory (.var (.there .here))) (.var .here)

/-- A local source binding holds the returned function, not a circuit word. -/
def squarePlusViaBinding : Expr [.field, .field] .field :=
  .letValue (.apply squarePlusFactory (.var (.there .here)))
    (.apply (.var .here) (.var (.there .here)))

/-- A higher-order helper receives the returned function and applies it. -/
def squarePlusViaPassedFunction : Expr [.field, .field] .field :=
  .apply
    (.apply
      (.lambda (.lambda (.apply (.var (.there .here)) (.var .here))))
      (.apply squarePlusFactory (.var (.there .here))))
    (.var .here)

/-- Factory return, local binding and higher-order passage leave exactly
`x*x + y` after specialization, for arbitrary residual input polynomials. -/
theorem squarePlus_routes_zero_cost {n : Nat} (x y : Poly n) :
    specialize squarePlusViaFactory (.cons x (.cons y .nil)) =
        specialize directSquarePlus (.cons x (.cons y .nil)) ∧
    specialize squarePlusViaBinding (.cons x (.cons y .nil)) =
        specialize directSquarePlus (.cons x (.cons y .nil)) ∧
    specialize squarePlusViaPassedFunction (.cons x (.cons y .nil)) =
        specialize directSquarePlus (.cons x (.cons y .nil)) := by
  exact ⟨rfl, rfl, rfl⟩

def squarePlusPassedCode : Code M31 FieldOp :=
  (specialize squarePlusViaPassedFunction
    (inputResidual [(0 : Fin 2), (1 : Fin 2)])).code

/-- No closure, call or helper node appears: one multiply and one add. -/
theorem squarePlusPassedCode_shape :
    squarePlusPassedCode =
      ⟨[.apply .mul [0, 0], .apply .add [2, 1]], [3]⟩ := rfl

theorem squarePlusPassedCode_valid :
    squarePlusPassedCode.WellFormedFor fieldArity 2 :=
  Poly.code_valid _

/-- Every satisfying auxiliary witness binds the output to the source
arithmetic, and the honest value has a satisfying witness. -/
theorem squarePlusPassedCode_accepts (x y : M31) (output : List M31) :
    squarePlusPassedCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [x, y] output ↔
      output = [x * x + y] := by
  simpa [squarePlusPassedCode, squarePlusViaPassedFunction,
    squarePlusFactory, inputSource, denote, Env.get]
    using (program_graph_accepts [(0 : Fin 2), (1 : Fin 2)]
      squarePlusViaPassedFunction [x, y] output rfl)

theorem squarePlusPassedCode_rejects_forged (x y claim : M31)
    (falseClaim : claim ≠ x * x + y) :
    ¬ squarePlusPassedCode.strictAccepts fieldArity
        Gadgets.Hash.fieldPrimitive [x, y] [claim] := by
  intro accepted
  have equal : claim = x * x + y := by
    simpa using (squarePlusPassedCode_accepts x y [claim]).mp accepted
  exact falseClaim equal

theorem squarePlusPassedCode_accepts_honest (x y : M31) :
    squarePlusPassedCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [x, y] [x * x + y] :=
  (squarePlusPassedCode_accepts x y [x * x + y]).mpr rfl

end S31.Functional
