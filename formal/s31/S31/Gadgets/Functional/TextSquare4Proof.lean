import S31.Gadgets.Functional.TextSquare4
import S31.Gadgets.Functional.Arrays

namespace S31.Functional.TextSquare4Proof
open S31
open S31.Functional

/-- A typed source expression with the meaning of the concrete `.s31`
`apply_twice(square, x)` sample. Its static binding adds no field operation. -/
def sourceSquareTwice : Expr [.array 4] (.array 4) :=
  .letValue (.arrayMul (.var .here) (.var .here))
    (.arrayMul (.var .here) (.var .here))

theorem source_square_twice (input : Fin 4 → M31) (i : Fin 4) :
    denote sourceSquareTwice (arrayInputSource input) i =
      (input i * input i) * (input i * input i) := by
  rfl

/-- The generated IR has exactly two multiplication nodes: the first square
is named once, and the second node reuses it on both sides. -/
theorem text_compiler_shape :
    TextSquare4.compiled.nodes = [
      { name := "_s31_i1_0", op := .mul,
        lhs := some "x", rhs := some "x" },
      { name := "result", op := .mul,
        lhs := some "_s31_i1_0", rhs := some "_s31_i1_0" }
    ] := by
  rfl

theorem text_compiler_validates :
    TextSquare4.compiled.validate = .ok [
      ("x", ⟨.m31, 4⟩),
      ("_s31_i1_0", ⟨.m31, 4⟩),
      ("result", ⟨.m31, 4⟩)] := by
  decide

def inputEnv (a b c d : M31) : S31.Env :=
  [("x", ⟨.m31, [a, b, c, d]⟩)]

/-- The actual text compiler's normalized nodes, interpreted by the Lean
relation semantics, compute the same fourth power on every input lane. -/
theorem text_compiler_nodes_correct (a b c d : M31) :
    (TextSquare4.compiled.nodes.foldlM (fun env node => do
      return env ++ [(node.name, ← evaluateNode env node)])
        (inputEnv a b c d)) =
      .ok (inputEnv a b c d ++ [
        ("_s31_i1_0", ⟨.m31, [a * a, b * b, c * c, d * d]⟩),
        ("result", ⟨.m31,
          [(a * a) * (a * a), (b * b) * (b * b),
           (c * c) * (c * c), (d * d) * (d * d)]⟩)]) := by
  rfl

end S31.Functional.TextSquare4Proof
