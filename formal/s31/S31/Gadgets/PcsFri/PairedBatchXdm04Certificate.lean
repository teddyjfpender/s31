import S31.Gadgets.PcsFri.PairedBatchXdm04Topology
import Mathlib.Tactic

/-!
An independently checked mixed-path certificate is enough to instantiate
`acceptedMixedOpening`. A second theorem derives the committed opening from
an all-node recurrence certificate for the transposed prover tree. These are
semantic implications in Lean. The audit-only Zig checker must still be
related to these definitions and installed in a verifier before its success
can replace the explicit certificate premises in a release theorem.
-/

namespace S31.Gadgets.PcsFri.PairedBatchXdm04Certificate

open S31.Gadgets.PcsFri.PairedBatchXdm04Topology
open S31.Gadgets.PcsFri.PairedBatchSourceCustody

variable {H : Type*}

/-- The fields of one native audit `Opening`: the starting tagged row, a
bottom-up list of sibling hashes and optional inserted ancestor rows, the
native transposed index, its binary-path conversion, and the root. -/
structure OpeningCertificate (H : Type*) where
  level : Nat
  nativeIndex : Nat
  binaryPosition : Nat
  input : NodeInput H
  steps : List (MixedStep H)
  root : H

/-- A direct counterpart of `Opening.check` in the audit-only Zig module.
The hash functions remain abstract, so a concrete BLAKE2s correspondence is
still a separate requirement. -/
def checkOpening [DecidableEq H]
    (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H) (cert : OpeningCertificate H) : Bool :=
  decide (cert.steps.length = cert.level ∧
    cert.nativeIndex < 2 ^ cert.level ∧
    cert.binaryPosition = pathPosition cert.level cert.nativeIndex ∧
    mixedPathRoot upperHash insertedHash
      (taggedNodeHash leafHash insertedHash cert.input)
      cert.binaryPosition cert.steps = cert.root)

theorem checkOpening_sound [DecidableEq H]
    (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H) (cert : OpeningCertificate H)
    (accepted : checkOpening leafHash insertedHash upperHash cert = true) :
    acceptedMixedOpening leafHash insertedHash upperHash cert.root
      cert.level cert.binaryPosition cert.input cert.steps := by
  have checked : cert.steps.length = cert.level ∧
      cert.nativeIndex < 2 ^ cert.level ∧
      cert.binaryPosition = pathPosition cert.level cert.nativeIndex ∧
      mixedPathRoot upperHash insertedHash
        (taggedNodeHash leafHash insertedHash cert.input)
        cert.binaryPosition cert.steps = cert.root := by
    simpa [checkOpening] using (of_decide_eq_true accepted)
  rcases checked with ⟨hdepth, _, hposition, hroot⟩
  exact ⟨by rw [hposition]; exact pathPosition_lt _ _, hdepth, hroot⟩

theorem checkOpening_native_replay [DecidableEq H]
    (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H) (cert : OpeningCertificate H)
    (accepted : checkOpening leafHash insertedHash upperHash cert = true) :
    nativeMixedRoot upperHash insertedHash cert.level cert.nativeIndex
      (taggedNodeHash leafHash insertedHash cert.input) cert.steps = cert.root := by
  have checked : cert.steps.length = cert.level ∧
      cert.nativeIndex < 2 ^ cert.level ∧
      cert.binaryPosition = pathPosition cert.level cert.nativeIndex ∧
      mixedPathRoot upperHash insertedHash
        (taggedNodeHash leafHash insertedHash cert.input)
        cert.binaryPosition cert.steps = cert.root := by
    simpa [checkOpening] using (of_decide_eq_true accepted)
  rcases checked with ⟨hdepth, _, hposition, hroot⟩
  have replay := nativeMixedRoot_eq_mixedPathRoot upperHash insertedHash
    cert.nativeIndex (taggedNodeHash leafHash insertedHash cert.input) cert.steps
  rw [hdepth, ← hposition] at replay
  exact replay.trans hroot

/-- One parent edge's inserted source row, if that parent is at another
source height. Above the last source height it is an upper-only parent. -/
def edgeRow (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) : Option (List Base) :=
  let height := k - (level - 1)
  if 0 < height ∧ height < heightCount then
    some (rows height (nativeParent level index))
  else none

/-- The complete sibling/inserted-row path derived from a layered tree. -/
def committedSteps (nodes : Nat → Nat → H)
    (siblingIndex : Nat → Nat → Nat) (rows : Nat → Nat → List Base)
    (k heightCount : Nat) : Nat → Nat → List (MixedStep H)
  | 0, _ => []
  | level + 1, index =>
      (nodes (level + 1) (siblingIndex (level + 1) index),
        edgeRow rows k heightCount (level + 1) index) ::
      committedSteps nodes siblingIndex rows k heightCount level
        (nativeParent (level + 1) index)

def terminalIndex : Nat → Nat → Nat
  | 0, index => index
  | level + 1, index => terminalIndex level (nativeParent (level + 1) index)

theorem committedSteps_length (nodes : Nat → Nat → H)
    (siblingIndex : Nat → Nat → Nat) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) :
    (committedSteps nodes siblingIndex rows k heightCount level index).length = level := by
  induction level generalizing index with
  | zero => simp [committedSteps]
  | succ level ih => simp [committedSteps, ih]

/-- All-node parent recurrences imply that replaying any derived path returns
the recorded level-zero node. The recurrence is the mathematical condition
checked by the audit-only native `auditCommitment` walk. -/
theorem committed_replay_eq_terminal (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (nodes : Nat → Nat → H) (siblingIndex : Nat → Nat → Nat)
    (rows : Nat → Nat → List Base) (k heightCount level index : Nat)
    (hle : level ≤ k)
    (edges : ∀ l i, 0 < l → l ≤ k →
      nodes (l - 1) (nativeParent l i) =
        mixedHash upperHash insertedHash
          (nativeChildren l i (nodes l i) (nodes l (siblingIndex l i)),
            edgeRow rows k heightCount l i)) :
    nativeMixedRoot upperHash insertedHash level index (nodes level index)
      (committedSteps nodes siblingIndex rows k heightCount level index) =
        nodes 0 (terminalIndex level index) := by
  induction level generalizing index with
  | zero => simp [nativeMixedRoot, committedSteps, terminalIndex]
  | succ level ih =>
      have edge := edges (level + 1) index (by omega) (by omega)
      have tail := ih (nativeParent (level + 1) index) (by omega)
      simp only [nativeMixedRoot, committedSteps, terminalIndex]
      rw [← edge]
      exact tail

/-- The committed prover tree supplies its own modeled opening at any source
height once all parent recurrences, the starting tagged node, and the final
root index are certified. No assumption about the verifier's opening is
smuggled into the committed path. -/
theorem committed_tree_accepted (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H)
    (nodes : Nat → Nat → H) (siblingIndex : Nat → Nat → Nat)
    (rows : Nat → Nat → List Base) (k heightCount level index : Nat)
    (input : NodeInput H) (root : H)
    (hle : level ≤ k)
    (hstart : taggedNodeHash leafHash insertedHash input = nodes level index)
    (hend : terminalIndex level index = 0)
    (hroot : nodes 0 0 = root)
    (edges : ∀ l i, 0 < l → l ≤ k →
      nodes (l - 1) (nativeParent l i) =
        mixedHash upperHash insertedHash
          (nativeChildren l i (nodes l i) (nodes l (siblingIndex l i)),
            edgeRow rows k heightCount l i)) :
    acceptedMixedOpening leafHash insertedHash upperHash root level
      (pathPosition level index) input
      (committedSteps nodes siblingIndex rows k heightCount level index) := by
  apply native_mixed_replay_accepted leafHash insertedHash upperHash root
    level index input _ (committedSteps_length nodes siblingIndex rows k heightCount level index)
  rw [hstart]
  exact (committed_replay_eq_terminal upperHash insertedHash nodes siblingIndex rows
    k heightCount level index hle edges).trans (by rw [hend]; exact hroot)

end S31.Gadgets.PcsFri.PairedBatchXdm04Certificate
