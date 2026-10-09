import S31.Gadgets.FunctionalArrays
import S31.Semantics.Node

/-!
Pointwise M31 array arithmetic across the typed functional core, its strict
field graph, and executable normalized relation nodes. Production Python
emission and Zig AIR lowering remain outside these theorems.
-/

namespace S31.Functional

open Graph

private theorem zipMap_ofFn {n : Nat} (a b : Fin n → M31)
    (combine : M31 → M31 → M31) :
    ((List.ofFn a).zip (List.ofFn b)).map
      (fun (x, y) => combine x y) =
    List.ofFn (fun i => combine (a i) (b i)) := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp

def arithmeticNode (multiply : Bool) : Node :=
  { name := "out", op := if multiply then .mul else .add,
    lhs := some "left", rhs := some "right" }

def arithmeticEnv {n : Nat}
    (a b : Fin n → M31) : S31.Env :=
  [("left", ⟨.m31, List.ofFn a⟩),
   ("right", ⟨.m31, List.ofFn b⟩)]

private theorem m31_shape_beq_self (length : Nat) :
    ((⟨.m31, length⟩ : Shape) == ⟨.m31, length⟩) = true := by
  change ((Kind.m31 == Kind.m31) && (length == length)) = true
  simp [show (Kind.m31 == Kind.m31) = true by rfl]

theorem arithmeticNode_shape {n : Nat} (multiply : Bool)
    (a b : Fin n → M31) :
    inferNode ((arithmeticEnv a b).map
      (fun (name, value) => (name, value.shape)))
      (arithmeticNode multiply) = .ok ⟨.m31, n⟩ := by
  have hkind : (Kind.m31 == Kind.m31) = true := rfl
  cases multiply <;>
    simp [arithmeticNode, arithmeticEnv, inferNode, Node.metadataValid,
      Node.fields, shapeOperand, expectShape, lookup, Value.shape,
      need, require, hkind, Bind.bind, Except.bind, Except.map]
  all_goals
    have hpure : (pure (⟨.m31, n⟩ : Shape) : Result Shape) =
        .ok ⟨.m31, n⟩ := rfl
    simp [hpure]

theorem arithmeticNode_eval {n : Nat} (multiply : Bool)
    (a b : Fin n → M31) :
    evaluateNode (arithmeticEnv a b) (arithmeticNode multiply) =
      .ok ⟨.m31, List.ofFn
        (fun i => if multiply then a i * b i else a i + b i)⟩ := by
  unfold evaluateNode
  rw [arithmeticNode_shape multiply a b]
  have hshape := m31_shape_beq_self n
  cases multiply
  · simp [arithmeticNode, arithmeticEnv, valueOperand, lookup,
      require, Value.shape, Value.valid, zipMap_ofFn,
      Bind.bind, Except.bind]
    have hpure : (pure (List.ofFn (fun i => a i + b i)) : Result (List M31)) =
        .ok (List.ofFn (fun i => a i + b i)) := rfl
    rw [hpure]
    simp [hshape]
    rfl
  · simp [arithmeticNode, arithmeticEnv, valueOperand, lookup,
      require, Value.shape, Value.valid, zipMap_ofFn,
      Bind.bind, Except.bind]
    have hpure : (pure (List.ofFn (fun i => a i * b i)) : Result (List M31)) =
        .ok (List.ofFn (fun i => a i * b i)) := rfl
    rw [hpure]
    simp [hshape]
    rfl

def arithmeticExpr {n length : Nat} (multiply : Bool)
    (a b : Expr [.array n] (.array length)) :
    Expr [.array n] (.array length) :=
  if multiply then .arrayMul a b else .arrayAdd a b

/-- Every satisfying auxiliary witness for an array addition or
multiplication source term yields exactly the result of its executable
normalized relation node. The converse constructs honest graph witnesses. -/
theorem arithmetic_graph_iff_node {n length : Nat} (multiply : Bool)
    (a b : Expr [.array n] (.array length))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (arrayCode (arithmeticExpr multiply a b)).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
    evaluateNode
      (arithmeticEnv
        (denote a (arrayInputSource (fun i => inputs.getD i.val 0)))
        (denote b (arrayInputSource (fun i => inputs.getD i.val 0))))
      (arithmeticNode multiply) = .ok ⟨.m31, output⟩ := by
  cases multiply <;>
    rw [arrayCode_accepts _ inputs output hinputs,
      arithmeticNode_eval] <;>
    simp [arithmeticExpr, denote, eq_comm]

end S31.Functional
