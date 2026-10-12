import S31.Gadgets.Functional.Correspondence.SourceFunctionBytes
import S31.Gadgets.Field

/-!
The three source operations of `release_sub4` as an arbitrary-witness packed
AIR relation. This composes the existing add/sub packed-row and normalized
node theorems without assuming that an honest witness was generated.

This theorem does not parse `release_sub4` source bytes or authenticate native
committed rows. The Python correspondence certificate checks its source,
native selector/address schedule and fixed root; connecting arbitrary proof
openings to these modeled rows remains a separate obligation.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionRelease

open S31.Functional.Correspondence.SourceFunctionBytes

abbrev Lanes := Fin 4 → S31.M31
abbrev Tail := Nat → Fin 4 → S31.M31

/-- The helper computes `doubled = x+x`, `difference = x-doubled`, and
`result = difference-x`. Inactive tail data is arbitrary; four lanes occupy
one full packed row for each operation. -/
def accepts (x doubled difference result : Lanes) (tailA tailB : Tail) : Prop :=
  SourceFunctionBytes.Op.packed .add x x doubled tailA tailB ∧
  SourceFunctionBytes.Op.packed .sub x doubled difference tailA tailB ∧
  SourceFunctionBytes.Op.packed .sub difference x result tailA tailB

theorem accepts_iff (x doubled difference result : Lanes)
    (tailA tailB : Tail) :
    accepts x doubled difference result tailA tailB ↔
      (∀ i, doubled i = x i + x i) ∧
      (∀ i, difference i = x i - doubled i) ∧
      (∀ i, result i = difference i - x i) := by
  simp only [accepts, packed_iff_eval, SourceFunctionBytes.Op.eval]

/-- Every satisfying intermediate witness forces the public result. -/
theorem arbitrary_witness_sound (x doubled difference result : Lanes)
    (tailA tailB : Tail)
    (h : accepts x doubled difference result tailA tailB) :
    result = fun i => (0 : S31.M31) - (x i + x i) := by
  obtain ⟨hdoubled, hdifference, hresult⟩ :=
    (accepts_iff x doubled difference result tailA tailB).mp h
  funext i
  calc
    result i = difference i - x i := hresult i
    _ = (x i - doubled i) - x i := by rw [hdifference i]
    _ = (0 : S31.M31) - (x i + x i) := by
      rw [hdoubled i]
      apply S31.Field.toZMod_injective
      simp only [S31.Field.toZMod_sub, S31.Field.toZMod_add,
                 S31.Field.toZMod_zero]
      ring

/-- The relation is nonvacuous for every public input and every tail. -/
theorem honest_witness_exists (x : Lanes) (tailA tailB : Tail) :
    ∃ doubled difference result : Lanes,
      accepts x doubled difference result tailA tailB ∧
      result = (fun i => (0 : S31.M31) - (x i + x i)) := by
  let doubled : Lanes := fun i => x i + x i
  let difference : Lanes := fun i => x i - doubled i
  let result : Lanes := fun i => difference i - x i
  refine ⟨doubled, difference, result, ?_, ?_⟩
  · exact (accepts_iff x doubled difference result tailA tailB).mpr
      ⟨(by intro i; rfl), (by intro i; rfl), (by intro i; rfl)⟩
  · exact arbitrary_witness_sound x doubled difference result tailA tailB
      ((accepts_iff x doubled difference result tailA tailB).mpr
        ⟨(by intro i; rfl), (by intro i; rfl), (by intro i; rfl)⟩)

/-- These are the same three operations as the executable normalized node
interpreter, including noncommutative subtraction order. -/
theorem accepts_iff_normalized_nodes (x doubled difference result : Lanes)
    (tailA tailB : Tail) :
    accepts x doubled difference result tailA tailB ↔
      S31.evaluateNode (S31.Functional.arithmeticEnv x x)
        (SourceFunctionBytes.Op.node .add) =
        .ok ⟨.m31, List.ofFn doubled⟩ ∧
      S31.evaluateNode (S31.Functional.arithmeticEnv x doubled)
        (SourceFunctionBytes.Op.node .sub) =
        .ok ⟨.m31, List.ofFn difference⟩ ∧
      S31.evaluateNode (S31.Functional.arithmeticEnv difference x)
        (SourceFunctionBytes.Op.node .sub) =
        .ok ⟨.m31, List.ofFn result⟩ := by
  simp only [accepts, packed_iff_node]

end S31.Functional.Correspondence.OrderedSubtractionRelease
