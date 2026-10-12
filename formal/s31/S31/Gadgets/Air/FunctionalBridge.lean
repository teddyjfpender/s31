import S31.Gadgets.Air.SimdChunks

/-!
Composition of the typed functional source core, strict scalar field graph,
executable normalized relation node, and one packed circuit AIR row for the
final arithmetic operation. Operand subexpressions are evaluated by the
source graph theorem; their own AIR rows are not modeled here. Python emission
and Zig compiler correctness remain outside this statement.
-/

namespace S31.Gadgets.Air.FunctionalBridge

open S31.Functional
open S31.Graph
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.SimdChunks
open S31.Gadgets.Packed

/-- Every satisfying strict graph witness for a typed pointwise array
expression has precisely the active-lane results admitted by the packed AIR
row for its final operation. The converse constructs both witnesses. This
holds for all source operands in the total functional core, any input
assignment, and every result length `≤ 4`; it does not model AIR rows used to
compute nontrivial operand subexpressions. -/
theorem array_graph_iff_air_row {n length : Nat} (hlen : length ≤ 4)
    (multiply : Bool)
    (a b : Expr [.array n] (.array length))
    (inputs : List S31.M31) (claimed : Fin length → S31.M31)
    (tailA tailB : Fin 4 → S31.M31) (hinputs : inputs.length = n) :
    (arrayCode (arithmeticExpr multiply a b)).strictAccepts
      fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn claimed) ↔
    ∃ packedOutput : Quad,
      accepts (encode (s31Op multiply))
        (packM31 (pad4 hlen
          (denote a (arrayInputSource (fun i => inputs.getD i.val 0))) tailA))
        (packM31 (pad4 hlen
          (denote b (arrayInputSource (fun i => inputs.getD i.val 0))) tailB))
        packedOutput ∧
      ∀ i : Fin length,
        coord packedOutput ⟨i.val, lt_of_lt_of_le i.isLt hlen⟩ =
          S31.Field.toZMod (claimed i) := by
  rw [arithmetic_graph_iff_node multiply a b inputs (List.ofFn claimed) hinputs]
  exact (partial_row_iff_normalized_node hlen multiply
    (denote a (arrayInputSource (fun i => inputs.getD i.val 0)))
    (denote b (arrayInputSource (fun i => inputs.getD i.val 0)))
    claimed tailA tailB).symm

/-- Source, strict graph, normalized arithmetic and every packed AIR row
agree for arrays of any length. Operand computations are still treated as
source values here; their preceding AIR rows require graph-wide composition. -/
theorem array_graph_iff_packed_rows {n length : Nat}
    (multiply : Bool)
    (a b : Expr [.array n] (.array length))
    (inputs : List S31.M31) (claimed : Fin length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31)
    (hinputs : inputs.length = n) :
    (arrayCode (arithmeticExpr multiply a b)).strictAccepts
      fieldArity S31.Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn claimed) ↔
    packedRows multiply
      (denote a (arrayInputSource (fun i => inputs.getD i.val 0)))
      (denote b (arrayInputSource (fun i => inputs.getD i.val 0)))
      claimed tailA tailB := by
  rw [arithmetic_graph_iff_node multiply a b inputs (List.ofFn claimed) hinputs]
  rw [S31.Functional.arithmeticNode_eval, packedRows_iff]
  constructor
  · intro h
    have hlist : List.ofFn
        (fun i : Fin length => if multiply then
          denote a (arrayInputSource (fun j => inputs.getD j.val 0)) i *
            denote b (arrayInputSource (fun j => inputs.getD j.val 0)) i else
          denote a (arrayInputSource (fun j => inputs.getD j.val 0)) i +
            denote b (arrayInputSource (fun j => inputs.getD j.val 0)) i) =
        List.ofFn claimed := by
      injection h with hvalue
      exact congrArg S31.Value.words hvalue
    have heq := List.ofFn_injective hlist
    intro i
    exact (congrFun heq i).symm
  · intro h
    have heq : (fun i : Fin length => if multiply then
          denote a (arrayInputSource (fun j => inputs.getD j.val 0)) i *
            denote b (arrayInputSource (fun j => inputs.getD j.val 0)) i else
          denote a (arrayInputSource (fun j => inputs.getD j.val 0)) i +
            denote b (arrayInputSource (fun j => inputs.getD j.val 0)) i) =
        claimed := by
      funext i
      exact (h i).symm
    rw [heq]

end S31.Gadgets.Air.FunctionalBridge
