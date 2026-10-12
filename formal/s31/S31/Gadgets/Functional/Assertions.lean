import S31.Gadgets.Functional.Outputs

/-!
Source-level field assertions over the typed functional core. The graph emits
the two sides of each assertion as ordinary wires. Acceptance checks equality
of those witnessed outputs; it does not consult the source evaluator.
-/

namespace S31.Functional

open Graph

def assertionExprs {Γ : List Ty}
    (pairs : List (Expr Γ .field × Expr Γ .field)) : List (Expr Γ .field) :=
  pairs.flatMap (fun pair => [pair.1, pair.2])

/-- The checker consumes exactly two values per assertion. An odd trailing
wire, including a forgotten right-hand side, is rejected. -/
def EqualPairs : List M31 → Prop
  | [] => True
  | [_] => False
  | lhs :: rhs :: rest => lhs = rhs ∧ EqualPairs rest

theorem equalPairs_source_iff {Γ : List Ty}
    (pairs : List (Expr Γ .field × Expr Γ .field))
    (env : Env Meaning Γ) :
    EqualPairs ((assertionExprs pairs).map (denote · env)) ↔
      ∀ pair ∈ pairs, denote pair.1 env = denote pair.2 env := by
  induction pairs with
  | nil => simp [assertionExprs, EqualPairs]
  | cons pair rest ih =>
      simp [assertionExprs, EqualPairs]
      intro _
      simpa only [assertionExprs, Prod.forall] using ih

structure Contract (Γ : List Ty) where
  outputs : List (Expr Γ .field)
  assertions : List (Expr Γ .field × Expr Γ .field)

def Contract.code {n : Nat} {indices : List (Fin n)}
    (contract : Contract (indices.map fun _ => .field)) : Code M31 FieldOp :=
  PolyList.code ((contract.outputs ++ assertionExprs contract.assertions).map
    (fun e => specialize e (inputResidual indices)))

/-- The claimed prefix has the declared number of public outputs. The
remaining graph outputs are assertion witnesses, checked pair by pair. -/
def Contract.Accepts {n : Nat} {indices : List (Fin n)}
    (contract : Contract (indices.map fun _ => .field))
    (inputs claimed : List M31) : Prop :=
  ∃ evidence,
    claimed.length = contract.outputs.length ∧
    contract.code.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive
      inputs (claimed ++ evidence) ∧
    EqualPairs evidence

/-- Soundness and completeness for every total typed field contract: all
outputs are bound, all assertions hold, and no arbitrary gate witness can
make a false claim pass. -/
theorem Contract.accepts_iff {n : Nat} (indices : List (Fin n))
    (contract : Contract (indices.map fun _ => .field))
    (inputs claimed : List M31) (hinputs : inputs.length = n) :
    contract.Accepts inputs claimed ↔
      claimed = contract.outputs.map (fun e => denote e
        (inputSource (fun i => inputs.getD i.val 0) indices)) ∧
      (∀ pair ∈ contract.assertions,
        denote pair.1 (inputSource (fun i => inputs.getD i.val 0) indices) =
        denote pair.2 (inputSource (fun i => inputs.getD i.val 0) indices)) := by
  let env := inputSource (fun i => inputs.getD i.val 0) indices
  let evidence := (assertionExprs contract.assertions).map (denote · env)
  have hgraph := programs_graph_accepts indices
    (contract.outputs ++ assertionExprs contract.assertions)
    inputs
  constructor
  · rintro ⟨witness, hlength, haccepted, hequal⟩
    have hvalues := (hgraph (claimed ++ witness) hinputs).mp haccepted
    simp only [List.map_append] at hvalues
    change claimed ++ witness = contract.outputs.map (denote · env) ++ evidence at hvalues
    have hlength' : claimed.length = (contract.outputs.map (denote · env)).length := by
      simpa using hlength
    obtain ⟨hclaimed, hwitness⟩ := List.append_inj hvalues hlength'
    refine ⟨hclaimed, ?_⟩
    rw [hwitness] at hequal
    exact (equalPairs_source_iff contract.assertions env).mp hequal
  · rintro ⟨hclaimed, hassertions⟩
    refine ⟨evidence, ?_, ?_, ?_⟩
    · simp [hclaimed]
    · apply (hgraph (claimed ++ evidence) hinputs).mpr
      simp only [List.map_append]
      change claimed ++ evidence = contract.outputs.map (denote · env) ++ evidence
      rw [hclaimed]
    · exact (equalPairs_source_iff contract.assertions env).mpr hassertions

/-- `assert_eq(x*x, x)` accepts exactly the fixed points of squaring.
The public result is still the input value. -/
def squareFixedPoint : Contract [.field] :=
  ⟨[.var .here], [(.mul (.var .here) (.var .here), .var .here)]⟩

theorem squareFixedPoint_code_shape :
    squareFixedPoint.code (indices := [(0 : Fin 1)]) =
      ⟨[.apply .mul [0, 0]], [0, 1, 0]⟩ := rfl

theorem squareFixedPoint_accepts (x y : M31) :
    (squareFixedPoint : Contract [.field]).Accepts (indices := [(0 : Fin 1)])
      [x] [y] ↔ y = x ∧ x * x = x := by
  have h := Contract.accepts_iff [(0 : Fin 1)] squareFixedPoint [x] [y] rfl
  constructor
  · intro accepted
    obtain ⟨hy, ha⟩ := h.mp accepted
    refine ⟨?_, ?_⟩
    · simpa [squareFixedPoint, inputSource, denote, Env.get] using hy
    · have hp := ha (.mul (.var .here) (.var .here), .var .here)
        (by change _ ∈ [_]; exact List.mem_cons_self)
      simpa [inputSource, denote, Env.get] using hp
  · rintro ⟨hy, hx⟩
    apply h.mpr
    constructor
    · simpa [squareFixedPoint, inputSource, denote, Env.get] using hy
    · intro pair member
      have hpair : pair =
          (.mul (.var .here) (.var .here), .var .here) := by
        change pair ∈ [_] at member
        exact List.mem_singleton.mp member
      subst pair
      simpa [inputSource, denote, Env.get] using hx

theorem squareFixedPoint_rejects_nonfixed (x y : M31)
    (hneq : x * x ≠ x) :
    ¬ (squareFixedPoint : Contract [.field]).Accepts
      (indices := [(0 : Fin 1)]) [x] [y] := by
  intro accepted
  exact hneq ((squareFixedPoint_accepts x y).mp accepted).2

end S31.Functional
