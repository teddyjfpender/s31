import S31.Gadgets.PcsFri.MultiproofRawQueries
import Mathlib.Tactic

/-!
An ideal complete lifted Merkle commitment built from projected columns.
This supplies the committed-opening premise used by the raw-query decoder:
every in-domain projected row has a full sibling path to the one computed
root. The native prover-to-this-model equivalence is tested and source-bound
separately; it is not assumed or proved by this mathematical construction.
-/

namespace S31.Gadgets.PcsFri.MultiproofCommittedColumns

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.MultiproofRawQueries

variable {V H : Type*}

/-- Hash at a level above the full leaf layer. `level = 0` is a leaf. -/
def layerHash (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V)) : Nat → Nat → H
  | 0, position => leafHash (projectedRow height position columns)
  | level + 1, position => parentHash
      (layerHash leafHash parentHash height columns level (2 * position),
       layerHash leafHash parentHash height columns level (2 * position + 1))

def siblingIndex (position : Nat) : Nat :=
  if position % 2 = 0 then position + 1 else position - 1

/-- Full path from a leaf to a higher layer, with native low-bit child order. -/
def layerPath (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V)) : Nat → Nat → Nat → List H
  | _, 0, _ => []
  | level, remaining + 1, position =>
      layerHash leafHash parentHash height columns level
          (siblingIndex position) ::
        layerPath leafHash parentHash height columns (level + 1) remaining
          (position / 2)

def committedRoot (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V)) : H :=
  layerHash leafHash parentHash height columns height 0

def committedPath (leafHash : List V → H) (parentHash : H × H → H)
    (height position : Nat) (columns : List (Column V)) : List H :=
  layerPath leafHash parentHash height columns 0 height position

theorem layerPath_length (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V)) (level remaining position : Nat) :
    (layerPath leafHash parentHash height columns level remaining position).length =
      remaining := by
  induction remaining generalizing level position with
  | zero => rfl
  | succ remaining ih => simp [layerPath, ih]

theorem layerHash_parent_at (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V)) (level position : Nat) :
    parentHash (orderedChildren position
      (layerHash leafHash parentHash height columns level position)
      (layerHash leafHash parentHash height columns level (siblingIndex position))) =
      layerHash leafHash parentHash height columns (level + 1) (position / 2) := by
  by_cases even : position % 2 = 0
  · have pos : position = 2 * (position / 2) := by omega
    have sib : siblingIndex position = 2 * (position / 2) + 1 := by
      simp only [siblingIndex, if_pos even]
      omega
    simp only [orderedChildren, if_pos even]
    change parentHash
      (layerHash leafHash parentHash height columns level position,
       layerHash leafHash parentHash height columns level (siblingIndex position)) =
      parentHash
        (layerHash leafHash parentHash height columns level (2 * (position / 2)),
         layerHash leafHash parentHash height columns level (2 * (position / 2) + 1))
    exact congrArg parentHash (Prod.ext
      (congrArg (layerHash leafHash parentHash height columns level) pos)
      (congrArg (layerHash leafHash parentHash height columns level) sib))
  · have pos : position = 2 * (position / 2) + 1 := by omega
    have sib : siblingIndex position = 2 * (position / 2) := by
      simp only [siblingIndex, if_neg even]
      omega
    simp only [orderedChildren, if_neg even]
    change parentHash
      (layerHash leafHash parentHash height columns level (siblingIndex position),
       layerHash leafHash parentHash height columns level position) =
      parentHash
        (layerHash leafHash parentHash height columns level (2 * (position / 2)),
         layerHash leafHash parentHash height columns level (2 * (position / 2) + 1))
    exact congrArg parentHash (Prod.ext
      (congrArg (layerHash leafHash parentHash height columns level) sib)
      (congrArg (layerHash leafHash parentHash height columns level) pos))

theorem layerPath_replays (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V))
    (level remaining position : Nat) :
    pathRoot parentHash
      (layerHash leafHash parentHash height columns level position)
      position
      (layerPath leafHash parentHash height columns level remaining position) =
    layerHash leafHash parentHash height columns (level + remaining)
      (position / 2 ^ remaining) := by
  induction remaining generalizing level position with
  | zero => simp [layerPath, pathRoot]
  | succ remaining ih =>
      simp only [layerPath, pathRoot]
      rw [layerHash_parent_at leafHash parentHash height columns level position,
        ih (level + 1) (position / 2)]
      congr 1
      · omega
      · rw [pow_succ, Nat.div_div_eq_div_mul]
        simp [Nat.mul_comm]

/-- The complete ideal tree gives every in-domain projected row an accepted
opening at its computed root, with no unproved "committed opening" premise. -/
theorem committedOpening (leafHash : List V → H) (parentHash : H × H → H)
    (height position : Nat) (columns : List (Column V))
    (inDomain : position < 2 ^ height) :
    acceptedOpening leafHash parentHash
      (committedRoot leafHash parentHash height columns) height position
      (projectedRow height position columns)
      (committedPath leafHash parentHash height position columns) := by
  refine ⟨inDomain, ?_, ?_⟩
  · exact layerPath_length leafHash parentHash height columns 0 height position
  · have quotient : position / 2 ^ height = 0 :=
      Nat.div_eq_zero_iff.mpr (Or.inr inDomain)
    simpa [committedRoot, committedPath, layerHash, quotient] using
      layerPath_replays leafHash parentHash height columns 0 height position

/-- A successful raw-query decode against the computed complete-tree root
opens the projected row, unless these particular two paths exhibit a leaf or
parent collision. Native root-to-model equivalence remains a separate bridge. -/
theorem verifyRaw_refines_constructed_commitment [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V))
    (queries : List (RawQuery V)) (witnesses : List H)
    (captures : List (Option (List H)))
    (accepted : verifyRaw leafHash parentHash
      (height := height) (root := committedRoot leafHash parentHash height columns)
      queries witnesses = some captures)
    (i : Nat) (inRange : i < queries.length)
    (nativePath : List H)
    (captured : captures[i]'(by
      obtain ⟨_, layers, _, _, rfl⟩ :=
        verifyRaw_decomposes leafHash parentHash height
          (committedRoot leafHash parentHash height columns) queries witnesses
          captures accepted
      simpa [S31.Gadgets.PcsFri.MultiproofCallerOrder.captureInCallerOrder]
        using inRange) = some nativePath)
    (noCollision : ¬collisionOnOpenings leafHash parentHash
      queries[i].position queries[i].row
      (projectedRow height queries[i].position columns)
      nativePath
      (committedPath leafHash parentHash height queries[i].position columns)) :
    queries[i].row = projectedRow height queries[i].position columns := by
  obtain ⟨path, observed, native⟩ :=
    verifyRaw_each_opening leafHash parentHash height
      (committedRoot leafHash parentHash height columns)
      queries witnesses captures accepted i inRange
  have inDomain := native.1
  exact verifyRaw_refines_committed_row leafHash parentHash height
    (committedRoot leafHash parentHash height columns) queries witnesses
    captures accepted i inRange columns nativePath
    (committedPath leafHash parentHash height queries[i].position columns)
    captured (committedOpening leafHash parentHash height queries[i].position
      columns inDomain) noCollision

/-- The same conditional origin guarantee for every caller slot, including
repeated positions. `verifyRaw_each_opening` supplies each captured path; the
only remaining model premise is absence of a collision on that opening and
the complete-tree opening at the same index. -/
theorem verifyRaw_all_rows_refine [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (columns : List (Column V))
    (queries : List (RawQuery V)) (witnesses : List H)
    (captures : List (Option (List H)))
    (accepted : verifyRaw leafHash parentHash height
      (committedRoot leafHash parentHash height columns)
      queries witnesses = some captures)
    (noCollision : ∀ (i : Nat) (inRange : i < queries.length) (path : List H),
      captures[i]'(by
        obtain ⟨_, layers, _, _, rfl⟩ :=
          verifyRaw_decomposes leafHash parentHash height
            (committedRoot leafHash parentHash height columns) queries witnesses
            captures accepted
        simpa [S31.Gadgets.PcsFri.MultiproofCallerOrder.captureInCallerOrder]
          using inRange) = some path →
      ¬collisionOnOpenings leafHash parentHash
        queries[i].position queries[i].row
        (projectedRow height queries[i].position columns)
        path (committedPath leafHash parentHash height queries[i].position columns)) :
    ∀ (i : Nat) (inRange : i < queries.length),
      queries[i].row = projectedRow height queries[i].position columns := by
  intro i inRange
  obtain ⟨path, captured, _⟩ :=
    verifyRaw_each_opening leafHash parentHash height
      (committedRoot leafHash parentHash height columns)
      queries witnesses captures accepted i inRange
  exact verifyRaw_refines_constructed_commitment leafHash parentHash height
    columns queries witnesses captures accepted i inRange path captured
    (noCollision i inRange path captured)

private def toyLeaf (row : List Nat) : Nat := row.sum
private def toyParent (children : Nat × Nat) : Nat :=
  100 * children.1 + children.2
private def toyColumns : List (Column Nat) :=
  [⟨1, fun i => if i = 0 then 10 else 11⟩]

-- A complete handwritten tree: leaves 10 and 11, root 100·10+11=1011.
example : committedRoot toyLeaf toyParent 1 toyColumns = 1011 := by decide
example : committedPath toyLeaf toyParent 1 0 toyColumns = [11] := by decide
example : committedPath toyLeaf toyParent 1 1 toyColumns = [10] := by decide

end S31.Gadgets.PcsFri.MultiproofCommittedColumns
