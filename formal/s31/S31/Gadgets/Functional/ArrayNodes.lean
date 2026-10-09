import S31.Gadgets.Functional.Arrays
import S31.Semantics.Node

/-!
Concrete normalized relation nodes for array views. The typed functional
core interprets arrays through `Fin`; this module checks that the executable
relation evaluator uses the same lane order. It does not verify that Python
emits these nodes or that Zig emits corresponding AIR constraints.
-/

namespace S31.Functional

open Graph

private theorem m31_shape_beq_self (length : Nat) :
    ((⟨.m31, length⟩ : Shape) == ⟨.m31, length⟩) = true := by
  change ((Kind.m31 == Kind.m31) && (length == length)) = true
  simp [show (Kind.m31 == Kind.m31) = true by rfl]

def concatNode : Node :=
  { name := "out", op := .array_concat,
    lhs := some "left", rhs := some "right" }

def concatEnv {left right : Nat}
    (a : Fin left → M31) (b : Fin right → M31) : S31.Env :=
  [("left", ⟨.m31, List.ofFn a⟩),
   ("right", ⟨.m31, List.ofFn b⟩)]

theorem concatNode_shape {left right : Nat}
    (a : Fin left → M31) (b : Fin right → M31)
    (hbound : left + right ≤ 4096) :
    inferNode ((concatEnv a b).map
      (fun (name, value) => (name, value.shape))) concatNode =
      .ok ⟨.m31, left + right⟩ := by
  have hkind : (Kind.m31 == Kind.m31) = true := rfl
  simp [concatNode, concatEnv, inferNode, Node.metadataValid,
    Node.fields, shapeOperand, lookup, Value.shape, need, require,
    hbound, hkind, Bind.bind, Except.bind, Except.map]
  rfl

theorem concatNode_eval {left right : Nat}
    (a : Fin left → M31) (b : Fin right → M31)
    (hbound : left + right ≤ 4096) :
    evaluateNode (concatEnv a b) concatNode =
      .ok ⟨.m31, List.ofFn (Fin.append a b)⟩ := by
  unfold evaluateNode
  rw [concatNode_shape a b hbound]
  have hshape := m31_shape_beq_self (left + right)
  simp [concatNode, concatEnv, valueOperand, lookup,
    require, Value.shape, Value.valid, List.ofFn_fin_append,
    Bind.bind, Except.bind]
  have hpure : (pure (List.ofFn a ++ List.ofFn b) : Result (List M31)) =
      .ok (List.ofFn a ++ List.ofFn b) := rfl
  rw [hpure]
  simp [hshape]
  rfl

def arrayGetNode (index : Nat) : Node :=
  { name := "out", op := .array_get,
    lhs := some "array", index := some index }

def arrayGetEnv {length : Nat} (words : Fin length → M31) : S31.Env :=
  [("array", ⟨.m31, List.ofFn words⟩)]

theorem arrayGetNode_shape {length : Nat}
    (words : Fin length → M31) (index : Fin length) :
    inferNode ((arrayGetEnv words).map
      (fun (name, value) => (name, value.shape)))
      (arrayGetNode index.val) = .ok ⟨.m31, 1⟩ := by
  simp [arrayGetNode, arrayGetEnv, inferNode, Node.metadataValid,
    Node.fields, shapeOperand, lookup, Value.shape, need, require,
    index.isLt, Bind.bind, Except.bind, Except.map]
  rfl

theorem arrayGetNode_eval {length : Nat}
    (words : Fin length → M31) (index : Fin length) :
    evaluateNode (arrayGetEnv words) (arrayGetNode index.val) =
      .ok ⟨.m31, [words index]⟩ := by
  unfold evaluateNode
  rw [arrayGetNode_shape words index]
  have hshape := m31_shape_beq_self 1
  simp [arrayGetNode, arrayGetEnv, valueOperand, lookup,
    require, Value.shape, Value.valid, Bind.bind, Except.bind,
    List.getD_eq_getElem?_getD]
  have hpure : (pure [words index] : Result (List M31)) =
      .ok [words index] := rfl
  rw [hpure]
  simp [hshape]
  rfl

/-- A typed concat expression's strict graph has exactly the same complete
array result as a normalized `array_concat` node applied to its two denoted
operands. The proof holds for arbitrary intermediate graph witnesses. -/
theorem arrayConcat_graph_iff_node {n left right : Nat}
    (a : Expr [.array n] (.array left))
    (b : Expr [.array n] (.array right))
    (inputs output : List M31)
    (hinputs : inputs.length = n)
    (hbound : left + right ≤ 4096) :
    (arrayCode (.arrayConcat a b)).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
    evaluateNode
      (concatEnv
        (denote a (arrayInputSource (fun i => inputs.getD i.val 0)))
        (denote b (arrayInputSource (fun i => inputs.getD i.val 0))))
      concatNode = .ok ⟨.m31, output⟩ := by
  rw [arrayCode_accepts _ inputs output hinputs]
  rw [concatNode_eval _ _ hbound]
  simp [denote, eq_comm]

/-- An indexed source read specializes to a strict scalar graph whose only
accepted output agrees with the normalized `array_get` node on the array
subexpression's denoted value. -/
theorem arrayGet_graph_iff_node {n length : Nat}
    (array : Expr [.array n] (.array length))
    (index : Fin length) (inputs : List M31) (output : M31)
    (hinputs : inputs.length = n) :
    ((specialize (.arrayGet array index) (arrayInputResidual (n := n))).code).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs [output] ↔
    evaluateNode
      (arrayGetEnv (denote array
        (arrayInputSource (fun i => inputs.getD i.val 0))))
      (arrayGetNode index.val) = .ok ⟨.m31, [output]⟩ := by
  rw [Poly.code_accepts _ inputs [output] hinputs]
  rw [arrayGetNode_eval _ index]
  have hvalue := array_program_correct array
    (fun i => inputs.getD i.val 0) index
  simp [specialize, eq_comm]
  change output = (specialize array (arrayInputResidual (n := n)) index).eval
      (fun i => inputs.getD i.val 0) ↔
    output = denote array (arrayInputSource (fun i => inputs.getD i.val 0)) index
  rw [hvalue]

def arraySliceNode (offset count : Nat) : Node :=
  { name := "out", op := .array_slice,
    lhs := some "array", index := some offset, length := some count }

theorem arraySliceNode_shape {length : Nat}
    (words : Fin length → M31) (offset count : Nat)
    (hcount : 0 < count) (hbound : offset + count ≤ length) :
    inferNode ((arrayGetEnv words).map
      (fun (name, value) => (name, value.shape)))
      (arraySliceNode offset count) = .ok ⟨.m31, count⟩ := by
  simp [arraySliceNode, arrayGetEnv, inferNode, Node.metadataValid,
    Node.fields, shapeOperand, lookup, Value.shape, need, require,
    hcount, hbound, Bind.bind, Except.bind, Except.map]
  rfl

theorem arraySliceNode_eval {length : Nat}
    (words : Fin length → M31) (offset count : Nat)
    (hcount : 0 < count) (hbound : offset + count ≤ length) :
    evaluateNode (arrayGetEnv words) (arraySliceNode offset count) =
      .ok ⟨.m31, ((List.ofFn words).drop offset).take count⟩ := by
  unfold evaluateNode
  rw [arraySliceNode_shape words offset count hcount hbound]
  have hlength : (((List.ofFn words).drop offset).take count).length = count := by
    rw [List.length_take_of_le]
    simp
    omega
  have hshape := m31_shape_beq_self count
  simp [arraySliceNode, arrayGetEnv, valueOperand, lookup,
    require, Value.shape, Value.valid, Bind.bind, Except.bind]
  have hpure :
      (pure (((List.ofFn words).drop offset).take count) : Result (List M31)) =
      .ok (((List.ofFn words).drop offset).take count) := rfl
  rw [hpure]
  simp [hlength, hshape]
  rfl

theorem arrayTakeFn_list {length count : Nat} (h : count ≤ length)
    (words : Fin length → M31) :
    List.ofFn (arrayTakeFn h words) = (List.ofFn words).take count := by
  apply List.ext_get
  · simp [h]
  · intro i hi hj
    simp [arrayTakeFn]

theorem arrayDropFn_list {length count : Nat} (h : count ≤ length)
    (words : Fin length → M31) :
    List.ofFn (arrayDropFn h words) = (List.ofFn words).drop count := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp [arrayDropFn]

/-- A static take view and the normalized zero-offset slice have the same
accepted array result, with no extra source-level computational gate. -/
theorem arrayTake_graph_iff_node {n length count : Nat}
    (array : Expr [.array n] (.array length))
    (h : count ≤ length) (hcount : 0 < count)
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (arrayCode (.arrayTake count h array)).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
    evaluateNode
      (arrayGetEnv (denote array
        (arrayInputSource (fun i => inputs.getD i.val 0))))
      (arraySliceNode 0 count) = .ok ⟨.m31, output⟩ := by
  rw [arrayCode_accepts _ inputs output hinputs]
  rw [arraySliceNode_eval _ 0 count hcount (by simpa using h)]
  simp [denote, arrayTakeFn_list, eq_comm]

/-- A static drop view and the normalized suffix slice agree whenever the
remaining source array is nonempty. -/
theorem arrayDrop_graph_iff_node {n length count : Nat}
    (array : Expr [.array n] (.array length))
    (h : count ≤ length) (hremain : count < length)
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (arrayCode (.arrayDrop count h array)).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
    evaluateNode
      (arrayGetEnv (denote array
        (arrayInputSource (fun i => inputs.getD i.val 0))))
      (arraySliceNode count (length - count)) = .ok ⟨.m31, output⟩ := by
  have hcount : 0 < length - count := by omega
  have hbound : count + (length - count) ≤ length := by omega
  rw [arrayCode_accepts _ inputs output hinputs]
  rw [arraySliceNode_eval _ count (length - count) hcount hbound]
  simp [denote, arrayDropFn_list, List.take_of_length_le, eq_comm]

/-- `concat(drop<2>(x), take<2>(x))` is only a permutation of four input
wires in the field graph. -/
def rotateFourView : Expr [.array 4] (.array 4) :=
  .arrayConcat
    (.arrayDrop 2 (by decide) (.var .here))
    (.arrayTake 2 (by decide) (.var .here))

theorem rotateFourView_code_shape :
    arrayCode rotateFourView =
      ⟨[], [2, 3, 0, 1]⟩ := rfl

theorem rotateFourView_accepts (a b c d : M31) (output : List M31) :
    (arrayCode rotateFourView).strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [a, b, c, d] output ↔
      output = [c, d, a, b] := by
  simpa [rotateFourView, arrayInputSource, denote, Env.get,
    arrayTakeFn, arrayDropFn, Fin.append] using
    (arrayCode_accepts rotateFourView [a, b, c, d] output rfl)

end S31.Functional
