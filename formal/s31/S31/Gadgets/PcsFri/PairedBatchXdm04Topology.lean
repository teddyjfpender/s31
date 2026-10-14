import S31.Gadgets.PcsFri.PairedBatchSourceCustody
import Mathlib.Tactic

/-!
The XDM04 source tree is indexed in transposed order. At levels above one,
the sibling toggles bit 1 and the parent removes bit 1 while preserving bit 0.
At level one, the sibling toggles bit 0 and the parent is the root. The
ordinary `MerkleOpening.pathRoot` instead consumes the low bit at every step.
`pathPosition` converts the native node index to that ordinary path index.

This file proves the conversion for every finite upper path and packages the
result as `acceptedNodeOpening`. Its premise is a *modeled* native root replay;
the source-pinned Zig audit and finite native tests are separate evidence that
the experimental verifier uses these operations. This is not a Zig semantics
theorem or a hash collision-resistance claim.
-/

namespace S31.Gadgets.PcsFri.PairedBatchXdm04Topology

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.PairedBatchSourceCustody
open S31.Gadgets.PcsFri.PairedBatchNativeRefinement
open S31.Gadgets.PcsFri.PairedBatchSourceBinding
open S31.Gadgets.PcsFri.DeepQuotientAlgebra

variable {H : Type*}

/-- XDM04's `topology.parent(level,index)`, on its in-domain indices. -/
def nativeParent (level index : Nat) : Nat :=
  if level = 1 then 0 else index % 2 + 2 * (index / 4)

/-- The side of the current node in XDM04's ordered child pair. -/
def nativeSide (level index : Nat) : Nat :=
  if level = 1 then index % 2 else (index / 2) % 2

/-- Decode native transposed indices into the ordinary bottom-up Merkle path
bits. The recursion is exactly the native sibling/parent walk. -/
def pathPosition : Nat → Nat → Nat
  | 0, _ => 0
  | level + 1, index =>
      nativeSide (level + 1) index +
        2 * pathPosition level (nativeParent (level + 1) index)

theorem nativeSide_lt_two (level index : Nat) : nativeSide level index < 2 := by
  simp only [nativeSide]
  split_ifs <;> exact Nat.mod_lt _ (by decide)

theorem pathPosition_lt (level index : Nat) : pathPosition level index < 2 ^ level := by
  induction level generalizing index with
  | zero => simp [pathPosition]
  | succ level ih =>
      have side := nativeSide_lt_two (level + 1) index
      have tail := ih (nativeParent (level + 1) index)
      simp only [pathPosition, pow_succ]
      omega

theorem pathPosition_mod_two (level index : Nat) :
    pathPosition (level + 1) index % 2 = nativeSide (level + 1) index := by
  have side := nativeSide_lt_two (level + 1) index
  simp only [pathPosition]
  omega

theorem pathPosition_div_two (level index : Nat) :
    pathPosition (level + 1) index / 2 =
      pathPosition level (nativeParent (level + 1) index) := by
  have side := nativeSide_lt_two (level + 1) index
  simp only [pathPosition]
  omega

/-- The three XDM03 tags remain separate: leaf, inserted node (with two
children), and upper parent. The concrete BLAKE2s framing is pinned outside
Lean; these functions are intentionally abstract. -/
def taggedNodeHash (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) : NodeInput H → H
  | (none, row) => leafHash row
  | (some children, row) => insertedHash children row

def nativeChildren (level index : Nat) (current sibling : H) : H × H :=
  if nativeSide level index = 0 then (current, sibling) else (sibling, current)

theorem nativeChildren_eq_ordered (level index : Nat) (current sibling : H) :
    nativeChildren (level + 1) index current sibling =
      orderedChildren (pathPosition (level + 1) index) current sibling := by
  simp [nativeChildren, orderedChildren, pathPosition_mod_two]

/-- Replay of the upper-tree portion of one XDM04 opening. The initial
digest can be a height-zero tagged leaf or a tagged inserted source node. -/
def nativeUpperRoot (upperHash : H × H → H) (level index : Nat) (current : H) :
    List H → H
  | [] => current
  | sibling :: rest =>
      nativeUpperRoot upperHash (level - 1) (nativeParent level index)
        (upperHash (nativeChildren level index current sibling)) rest

theorem nativeUpperRoot_eq_pathRoot (upperHash : H × H → H)
    (index : Nat) (current : H) (siblings : List H) :
    nativeUpperRoot upperHash siblings.length index current siblings =
      pathRoot upperHash current (pathPosition siblings.length index) siblings := by
  induction siblings generalizing index current with
  | nil => simp [nativeUpperRoot, pathRoot]
  | cons sibling rest ih =>
      have step := ih (nativeParent (rest.length + 1) index)
        (upperHash (nativeChildren (rest.length + 1) index current sibling))
      simpa [nativeUpperRoot, pathRoot, nativeChildren_eq_ordered,
        pathPosition_div_two] using step

/-- A modeled successful native upper-tree replay supplies exactly the
`acceptedNodeOpening` premise used by the conditional source-custody theorem.
`position` is the converted path index, not the native transposed node index.
-/
theorem native_replay_accepted (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) (upperHash : H × H → H)
    (root : H) (level index : Nat) (input : NodeInput H)
    (siblings : List H) (hdepth : siblings.length = level)
    (hroot : nativeUpperRoot upperHash level index
      (taggedNodeHash leafHash insertedHash input) siblings = root) :
    acceptedNodeOpening (taggedNodeHash leafHash insertedHash) upperHash
      root level (pathPosition level index) input siblings := by
  subst level
  exact ⟨pathPosition_lt siblings.length index, rfl,
    (nativeUpperRoot_eq_pathRoot upperHash index
      (taggedNodeHash leafHash insertedHash input) siblings).symm.trans hroot⟩

/-- One ancestor of an opened source row: its sibling digest and either a
later source-height row to insert or `none` for an upper-only parent. -/
abbrev MixedStep (H : Type*) := H × Option (List Base)
abbrev MixedInput (H : Type*) := (H × H) × Option (List Base)

def mixedInput (position : Nat) (current : H) (step : MixedStep H) : MixedInput H :=
  (orderedChildren position current step.1, step.2)

def mixedHash (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H) : MixedInput H → H
  | (children, none) => upperHash children
  | (children, some row) => insertedHash children row

def mixedPathRoot (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (current : H) (position : Nat) : List (MixedStep H) → H
  | [] => current
  | step :: rest =>
      mixedPathRoot upperHash insertedHash
        (mixedHash upperHash insertedHash (mixedInput position current step))
        (position / 2) rest

def mixedPathInputs (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (current : H) (position : Nat) : List (MixedStep H) → List (MixedInput H)
  | [] => []
  | step :: rest =>
      let input := mixedInput position current step
      input :: mixedPathInputs upperHash insertedHash
        (mixedHash upperHash insertedHash input) (position / 2) rest

/-- Exact native transposed-index walk, with tagged inserted rows at ancestor
source heights and plain upper parents above the last source height. -/
def nativeMixedRoot (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (level index : Nat) (current : H) : List (MixedStep H) → H
  | [] => current
  | step :: rest =>
      let input : MixedInput H := (nativeChildren level index current step.1, step.2)
      nativeMixedRoot upperHash insertedHash (level - 1) (nativeParent level index)
        (mixedHash upperHash insertedHash input) rest

theorem nativeMixedRoot_eq_mixedPathRoot (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (index : Nat) (current : H) (steps : List (MixedStep H)) :
    nativeMixedRoot upperHash insertedHash steps.length index current steps =
      mixedPathRoot upperHash insertedHash current
        (pathPosition steps.length index) steps := by
  induction steps generalizing index current with
  | nil => simp [nativeMixedRoot, mixedPathRoot]
  | cons step rest ih =>
      have next := ih (nativeParent (rest.length + 1) index)
        (mixedHash upperHash insertedHash
          (nativeChildren (rest.length + 1) index current step.1, step.2))
      simpa [nativeMixedRoot, mixedPathRoot, mixedInput,
        nativeChildren_eq_ordered, pathPosition_div_two] using next

def acceptedMixedOpening (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) (upperHash : H × H → H)
    (root : H) (depth position : Nat) (input : NodeInput H)
    (steps : List (MixedStep H)) : Prop :=
  position < 2 ^ depth ∧ steps.length = depth ∧
    mixedPathRoot upperHash insertedHash
      (taggedNodeHash leafHash insertedHash input) position steps = root

/-- Conditional operational join from a modeled XDM04 mixed replay to the
mixed-path acceptance predicate. It does not infer the replay equation from
the return value of native `verifyAndCollect`; that Zig-to-Lean step remains
separate. -/
theorem native_mixed_replay_accepted (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) (upperHash : H × H → H)
    (root : H) (level index : Nat) (input : NodeInput H)
    (steps : List (MixedStep H)) (hdepth : steps.length = level)
    (hroot : nativeMixedRoot upperHash insertedHash level index
      (taggedNodeHash leafHash insertedHash input) steps = root) :
    acceptedMixedOpening leafHash insertedHash upperHash root level
      (pathPosition level index) input steps := by
  subst level
  exact ⟨pathPosition_lt steps.length index, rfl,
    (nativeMixedRoot_eq_mixedPathRoot upperHash insertedHash index
      (taggedNodeHash leafHash insertedHash input) steps).symm.trans hroot⟩

theorem equal_mixed_roots_force_initial_or_step_collision
    (upperHash : H × H → H) (insertedHash : H × H → List Base → H)
    (position : Nat) (initial₁ initial₂ : H)
    (steps₁ steps₂ : List (MixedStep H))
    (sameDepth : steps₁.length = steps₂.length)
    (sameRoot : mixedPathRoot upperHash insertedHash initial₁ position steps₁ =
      mixedPathRoot upperHash insertedHash initial₂ position steps₂) :
    initial₁ = initial₂ ∨
      ∃ input₁ input₂ : MixedInput H,
        input₁ ∈ mixedPathInputs upperHash insertedHash initial₁ position steps₁ ∧
        input₂ ∈ mixedPathInputs upperHash insertedHash initial₂ position steps₂ ∧
        input₁ ≠ input₂ ∧
        mixedHash upperHash insertedHash input₁ =
          mixedHash upperHash insertedHash input₂ := by
  induction steps₁ generalizing steps₂ initial₁ initial₂ position with
  | nil =>
      cases steps₂ with
      | nil => exact Or.inl sameRoot
      | cons _ _ => simp at sameDepth
  | cons step₁ rest₁ ih =>
      cases steps₂ with
      | nil => simp at sameDepth
      | cons step₂ rest₂ =>
          let input₁ := mixedInput position initial₁ step₁
          let input₂ := mixedInput position initial₂ step₂
          have tailDepth : rest₁.length = rest₂.length := by
            simpa using sameDepth
          have tailRoot :
              mixedPathRoot upperHash insertedHash
                  (mixedHash upperHash insertedHash input₁) (position / 2) rest₁ =
                mixedPathRoot upperHash insertedHash
                  (mixedHash upperHash insertedHash input₂) (position / 2) rest₂ := by
            simpa [mixedPathRoot, input₁, input₂] using sameRoot
          rcases ih (position / 2)
              (mixedHash upperHash insertedHash input₁)
              (mixedHash upperHash insertedHash input₂)
              rest₂ tailDepth tailRoot with sameNext | collision
          · by_cases sameInputs : input₁ = input₂
            · exact Or.inl (orderedChildren_current_injective position
                (congrArg Prod.fst sameInputs))
            · exact Or.inr ⟨input₁, input₂,
                by simp [mixedPathInputs, input₁],
                by simp [mixedPathInputs, input₂], sameInputs, sameNext⟩
          · rcases collision with ⟨later₁, later₂, inTail₁,
                inTail₂, distinct, sameHash⟩
            exact Or.inr ⟨later₁, later₂,
              by simpa [mixedPathInputs, input₁] using Or.inr inTail₁,
              by simpa [mixedPathInputs, input₂] using Or.inr inTail₂,
              distinct, sameHash⟩

def collisionOnMixedOpenings (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) (upperHash : H × H → H)
    (position : Nat) (nativeInput committedInput : NodeInput H)
    (nativeSteps committedSteps : List (MixedStep H)) : Prop :=
  (nativeInput ≠ committedInput ∧
    taggedNodeHash leafHash insertedHash nativeInput =
      taggedNodeHash leafHash insertedHash committedInput) ∨
  ∃ input₁ input₂ : MixedInput H,
    input₁ ∈ mixedPathInputs upperHash insertedHash
      (taggedNodeHash leafHash insertedHash nativeInput) position nativeSteps ∧
    input₂ ∈ mixedPathInputs upperHash insertedHash
      (taggedNodeHash leafHash insertedHash committedInput) position committedSteps ∧
    input₁ ≠ input₂ ∧ mixedHash upperHash insertedHash input₁ =
      mixedHash upperHash insertedHash input₂

/-- Fixed-position custody for every modeled source height, including paths
that cross inserted source nodes. The collision premise is local to the two
compared tagged openings; no hash probability or native execution theorem is
asserted. -/
theorem conflicting_mixed_rows_produce_collision
    (leafHash : List Base → H) (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H) (root : H) (depth position : Nat)
    (nativeInput committedInput : NodeInput H)
    (nativeSteps committedSteps : List (MixedStep H))
    (native : acceptedMixedOpening leafHash insertedHash upperHash
      root depth position nativeInput nativeSteps)
    (committed : acceptedMixedOpening leafHash insertedHash upperHash
      root depth position committedInput committedSteps)
    (differentRows : nodeRow nativeInput ≠ nodeRow committedInput) :
    collisionOnMixedOpenings leafHash insertedHash upperHash position
      nativeInput committedInput nativeSteps committedSteps := by
  rcases native with ⟨_, nativeDepth, nativeRoot⟩
  rcases committed with ⟨_, committedDepth, committedRoot⟩
  have sameDepth : nativeSteps.length = committedSteps.length :=
    nativeDepth.trans committedDepth.symm
  have sameRoot := nativeRoot.trans committedRoot.symm
  rcases equal_mixed_roots_force_initial_or_step_collision upperHash insertedHash
      position (taggedNodeHash leafHash insertedHash nativeInput)
      (taggedNodeHash leafHash insertedHash committedInput)
      nativeSteps committedSteps sameDepth sameRoot with sameNode | stepCollision
  · exact Or.inl ⟨by
      intro sameInput
      exact differentRows (congrArg nodeRow sameInput), sameNode⟩
  · exact Or.inr stepCollision

theorem mixed_row_refines_committed_row
    (leafHash : List Base → H) (insertedHash : H × H → List Base → H)
    (upperHash : H × H → H) (root : H) (depth position : Nat)
    (nativeInput committedInput : NodeInput H)
    (nativeSteps committedSteps : List (MixedStep H))
    (native : acceptedMixedOpening leafHash insertedHash upperHash
      root depth position nativeInput nativeSteps)
    (committed : acceptedMixedOpening leafHash insertedHash upperHash
      root depth position committedInput committedSteps)
    (noCollision : ¬collisionOnMixedOpenings leafHash insertedHash upperHash
      position nativeInput committedInput nativeSteps committedSteps) :
    nodeRow nativeInput = nodeRow committedInput := by
  by_contra differentRows
  exact noCollision (conflicting_mixed_rows_produce_collision
    leafHash insertedHash upperHash root depth position nativeInput committedInput
    nativeSteps committedSteps native committed differentRows)

/-- The prior public-claim and local own-quotient batch theorem now takes a
mixed inserted/upper path at any source height. It is still conditional on
both modeled openings and absence of a collision in their compared inputs.
The actual `verifyAndCollect` return-to-model correspondence and committed
prover-tree construction are not proved here. -/
theorem authenticated_public_row_batch_mixed {n : Nat}
    (leafHash : List Base → H)
    (insertedHash : H × H → List Base → H) (upperHash : H × H → H)
    (depth position : Nat)
    (proofHeader statement : SourceStatement H n)
    (nativeChildren committedChildren : Option (H × H))
    (nativeSteps committedSteps : List (MixedStep H))
    (opened committedSource : Fin n → Base)
    (challenge pointX pointY : QM31) (rowX rowY : Base)
    (matched : statementMatches proofHeader statement)
    (native : acceptedMixedOpening leafHash insertedHash upperHash
      proofHeader.sourceRoot depth position
      (nativeChildren, List.ofFn opened) nativeSteps)
    (committed : acceptedMixedOpening leafHash insertedHash upperHash
      statement.sourceRoot depth position
      (committedChildren, List.ofFn committedSource) committedSteps)
    (noCollision : ¬collisionOnMixedOpenings leafHash insertedHash upperHash position
      (nativeChildren, List.ofFn opened)
      (committedChildren, List.ofFn committedSource)
      nativeSteps committedSteps)
    (hcircle : pointX ^ 2 + pointY ^ 2 = 1)
    (hrow : (⟨rowX, 0⟩ : CM31) ^ 2 + (⟨rowY, 0⟩ : CM31) ^ 2 = 1)
    (hguard : pointY.c1 ≠ 0) :
    let denominator := rowDenominator pointX pointY ⟨rowX, 0⟩ ⟨rowY, 0⟩
    let coefficients := publicCoefficients pointY statement.claims
    conjugate pointY - pointY ≠ 0 ∧
    CheckedRecipes (fun i => recipe (coefficients i) rowY denominator) ∧
    nativeBatch challenge 1 rowY denominator
        (List.ofFn fun i => (opened i,
          (publicCoefficients pointY proofHeader.claims) i)) =
      (rowPoly (sourcePairs
        (fun i => recipe (coefficients i) rowY denominator)
        (fun i => fromBase (committedSource i)))).eval challenge := by
  obtain ⟨hroot, hclaims⟩ := matched
  have acceptedAtStatementRoot : acceptedMixedOpening leafHash insertedHash upperHash
      statement.sourceRoot depth position
      (nativeChildren, List.ofFn opened) nativeSteps := by
    simpa only [hroot] using native
  have rowEquality : List.ofFn opened = List.ofFn committedSource :=
    mixed_row_refines_committed_row leafHash insertedHash upperHash
      statement.sourceRoot depth position _ _ nativeSteps committedSteps
      acceptedAtStatementRoot committed noCollision
  have sourceEquality : opened = committedSource := List.ofFn_injective rowEquality
  subst opened
  dsimp only
  rw [hclaims]
  obtain ⟨hchecked, _, hbatch⟩ := accepted_row_local_refinement
    challenge pointX pointY rowX rowY
    (publicCoefficients pointY statement.claims) committedSource
    hcircle hrow hguard
  exact ⟨conjugate_span_nonzero pointY hguard, hchecked, hbatch⟩

end S31.Gadgets.PcsFri.PairedBatchXdm04Topology
