import Mathlib.Tactic

/-!
The native terminal verifier's `LinePoly.evalAtPoint` calls `poly.utils.fold`.
That fold uses a pending stack, equivalent to reducing the outermost split
first. S31 capture admission instead reduces adjacent coefficient pairs with
the last doubling factor, then repeats toward the root. This module proves
the two coefficient-basis orders agree for every full binary coefficient tree.

The factor list is ordered as the native `LinePoly` basis: `[x, doubleX x,
... ]`, so the deepest pair consumes the last factor. This is a field-algebra
statement about two algorithms. The native Zig loops, factor generation,
coefficient serialization, and terminal domain points remain separate source
and operational-refinement obligations.
-/

namespace S31.Gadgets.PcsFri.TerminalBasisRefinement

universe u
variable {F : Type u} [Semiring F]

/-- A power-of-two coefficient vector, in the native recursive coefficient
order. A node concatenates its left and right coefficient halves. -/
inductive CoeffTree (F : Type u) : Nat → Type u
  | leaf : F → CoeffTree F 0
  | node : CoeffTree F n → CoeffTree F n → CoeffTree F (n + 1)

def CoeffTree.flatten : CoeffTree F n → List F
  | .leaf value => [value]
  | .node left right => left.flatten ++ right.flatten

omit [Semiring F] in
theorem CoeffTree.flatten_length (tree : CoeffTree F n) :
    tree.flatten.length = 2 ^ n := by
  induction tree with
  | leaf value => simp [CoeffTree.flatten]
  | node left right ihleft ihright =>
      simp only [CoeffTree.flatten, List.length_append, ihleft, ihright, pow_succ]
      omega

/-- Recursive reference for the native pending-stack fold. The first factor
combines the two halves; the remaining factors act within each half. -/
def evalOuter : CoeffTree F n → List F → F
  | .leaf value, _ => value
  | .node _ _, [] => 0
  | .node left right, factor :: rest =>
      evalOuter left rest + evalOuter right rest * factor

/-- One capture-gate pass over adjacent coefficient pairs. -/
def mergeDeepest : (n : Nat) → CoeffTree F (n + 1) → F → CoeffTree F n
  | 0, .node (.leaf left) (.leaf right), factor =>
      .leaf (left + right * factor)
  | n + 1, .node left right, factor =>
      .node (mergeDeepest n left factor) (mergeDeepest n right factor)

/-- Repeat deepest-pair reduction, consuming factors from the end. The
zero fallback only makes malformed factor lists total; the theorem below
requires exactly one factor per tree level. -/
def evalPairs : (n : Nat) → CoeffTree F n → List F → F
  | 0, .leaf value, _ => value
  | n + 1, tree, factors =>
      evalPairs n (mergeDeepest n tree (factors.getLast?.getD 0))
        factors.dropLast

/-- One bottom-pair pass commutes with all outer reductions. -/
theorem evalOuter_mergeDeepest (n : Nat) (tree : CoeffTree F (n + 1))
    (factors : List F) (hsize : factors.length = n) (last : F) :
    evalOuter (mergeDeepest n tree last) factors =
      evalOuter tree (factors ++ [last]) := by
  induction n generalizing factors with
  | zero =>
      cases factors with
      | cons _ _ => simp at hsize
      | nil =>
          cases tree with
          | node left right =>
              cases left with
              | leaf l =>
                  cases right with
                  | leaf r =>
                      simp [mergeDeepest, evalOuter]
  | succ n ih =>
      cases tree with
      | node left right =>
          cases factors with
          | nil => simp at hsize
          | cons first rest =>
              have hrest : rest.length = n := by simpa using hsize
              simp only [mergeDeepest, evalOuter, List.cons_append]
              rw [ih left rest hrest, ih right rest hrest]

/-- The capture gate's pair-reduction value equals the native recursive
reference for all coefficient counts `2^n` and all field inputs. -/
theorem evalPairs_eq_evalOuter (n : Nat) (tree : CoeffTree F n)
    (factors : List F) (hsize : factors.length = n) :
    evalPairs n tree factors = evalOuter tree factors := by
  induction n generalizing factors with
  | zero =>
      cases tree with
      | leaf value => simp [evalPairs, evalOuter]
  | succ n ih =>
      have hnonempty : factors ≠ [] := by
        intro h
        simp [h] at hsize
      have hdrop : factors.dropLast.length = n := by
        have hlen := List.length_dropLast (xs := factors)
        omega
      have hjoin : factors.dropLast ++ [factors.getLast?.getD 0] = factors := by
        have hlast := List.dropLast_append_getLast hnonempty
        rw [List.getLast?_eq_some_getLast hnonempty]
        exact hlast
      calc
        evalPairs (n + 1) tree factors =
            evalPairs n (mergeDeepest n tree (factors.getLast?.getD 0))
              factors.dropLast := rfl
        _ = evalOuter (mergeDeepest n tree (factors.getLast?.getD 0))
              factors.dropLast := ih _ _ hdrop
        _ = evalOuter tree
              (factors.dropLast ++ [factors.getLast?.getD 0]) :=
            evalOuter_mergeDeepest n tree factors.dropLast hdrop _
        _ = evalOuter tree factors := by rw [hjoin]

/-- Four native-order coefficients illustrate the factor order: the deepest
pairs use 49, then the root uses 5. Swapping them changes the answer. -/
private def four : CoeffTree ℚ 2 :=
  .node (.node (.leaf 1) (.leaf 2))
    (.node (.leaf 3) (.leaf 4))

example : four.flatten = [1, 2, 3, 4] := by
  rfl

example : evalPairs 2 four [5, 49] = 1094 := by
  norm_num [evalPairs, mergeDeepest, four]

example : evalPairs 2 four [49, 5] ≠ 1094 := by
  norm_num [evalPairs, mergeDeepest, four]

end S31.Gadgets.PcsFri.TerminalBasisRefinement
