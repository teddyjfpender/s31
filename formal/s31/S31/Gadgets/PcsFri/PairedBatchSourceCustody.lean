import S31.Gadgets.PcsFri.PairedBatchNativeRefinement
import S31.Gadgets.PcsFri.MerkleOpening
import Mathlib.Tactic

/-!
Conditional fixed-source ownership for one experimental CAS05/XDM04 row.
The native verifier returns an original row only after XDM04 reconstructs
the source root. In this model an opening starts at either a tagged leaf
or a tagged inserted source node, then follows the upper-tree path.
Two different rows accepted at the same root and position produce a
collision in one of the compared node or upper-path hash inputs.

The native `verifyAndCollect`-to-`acceptedNodeOpening` correspondence and
the committed prover-tree opening remain explicit premises. The source
audit pins their operational call and publication order, but this is not a
Zig semantics theorem, a hash probability bound, or a PCS/FRI soundness
result. Public claim equality is an explicit statement-match premise.
-/

namespace S31.Gadgets.PcsFri.PairedBatchSourceCustody

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.PairedBatchNativeRefinement
open S31.Gadgets.PcsFri.PairedBatchSourceBinding
open S31.Gadgets.PcsFri.DeepQuotientAlgebra

variable {H : Type*}
abbrev Base := PairedBatchNativeRefinement.M31

/-- `none` is a height-zero XDM04 leaf; `some (left,right)` is an inserted
source row above two authenticated child hashes. The hash implementation
uses distinct native tags for those cases. -/
abbrev NodeInput (H : Type*) := Option (H × H) × List Base

def nodeRow (input : NodeInput H) : List Base := input.2

/-- Full opening of one XDM04 row at the source tree level containing it.
`depth` counts the remaining upper-tree edges, so the native node index is
bounded by `2^depth`. -/
def acceptedNodeOpening (nodeHash : NodeInput H → H)
    (upperHash : H × H → H) (root : H) (depth position : Nat)
    (input : NodeInput H) (siblings : List H) : Prop :=
  position < 2 ^ depth ∧ siblings.length = depth ∧
    pathRoot upperHash (nodeHash input) position siblings = root

/-- A witness tied to the two compared openings. Finite-output hashes are
not assumed globally injective. -/
def collisionOnNodeOpenings (nodeHash : NodeInput H → H)
    (upperHash : H × H → H) (position : Nat)
    (nativeInput committedInput : NodeInput H)
    (nativePath committedPath : List H) : Prop :=
  (nativeInput ≠ committedInput ∧
    nodeHash nativeInput = nodeHash committedInput) ∨
  ∃ children₁ children₂ : H × H,
    children₁ ∈ pathInputs upperHash (nodeHash nativeInput) position nativePath ∧
    children₂ ∈ pathInputs upperHash (nodeHash committedInput) position committedPath ∧
    children₁ ≠ children₂ ∧ upperHash children₁ = upperHash children₂

theorem conflicting_xdm_rows_produce_collision
    (nodeHash : NodeInput H → H) (upperHash : H × H → H)
    (root : H) (depth position : Nat)
    (nativeInput committedInput : NodeInput H)
    (nativePath committedPath : List H)
    (native : acceptedNodeOpening nodeHash upperHash root depth position
      nativeInput nativePath)
    (committed : acceptedNodeOpening nodeHash upperHash root depth position
      committedInput committedPath)
    (differentRows : nodeRow nativeInput ≠ nodeRow committedInput) :
    collisionOnNodeOpenings nodeHash upperHash position
      nativeInput committedInput nativePath committedPath := by
  rcases native with ⟨_, nativeDepth, nativeRoot⟩
  rcases committed with ⟨_, committedDepth, committedRoot⟩
  have sameDepth : nativePath.length = committedPath.length :=
    nativeDepth.trans committedDepth.symm
  have sameRoot : pathRoot upperHash (nodeHash nativeInput) position nativePath =
      pathRoot upperHash (nodeHash committedInput) position committedPath :=
    nativeRoot.trans committedRoot.symm
  rcases equal_roots_force_leaf_hash_or_parent_collision upperHash position
      (nodeHash nativeInput) (nodeHash committedInput)
      nativePath committedPath sameDepth sameRoot with sameNode | upperCollision
  · exact Or.inl ⟨by
      intro sameInput
      exact differentRows (congrArg nodeRow sameInput), sameNode⟩
  · exact Or.inr upperCollision

theorem xdm_row_refines_committed_row
    (nodeHash : NodeInput H → H) (upperHash : H × H → H)
    (root : H) (depth position : Nat)
    (nativeInput committedInput : NodeInput H)
    (nativePath committedPath : List H)
    (native : acceptedNodeOpening nodeHash upperHash root depth position
      nativeInput nativePath)
    (committed : acceptedNodeOpening nodeHash upperHash root depth position
      committedInput committedPath)
    (noCollision : ¬collisionOnNodeOpenings nodeHash upperHash position
      nativeInput committedInput nativePath committedPath) :
    nodeRow nativeInput = nodeRow committedInput := by
  by_contra differentRows
  exact noCollision (conflicting_xdm_rows_produce_collision
    nodeHash upperHash root depth position nativeInput committedInput
    nativePath committedPath native committed differentRows)

/-- QM31's native quadratic conjugation negates its upper CM31 coordinate. -/
noncomputable def conjugate (value : QM31) : QM31 :=
  ⟨value.c0, -value.c1⟩

theorem conjugate_span_nonzero (value : QM31)
    (hguard : value.c1 ≠ 0) : conjugate value - value ≠ 0 := by
  intro hspan
  have equal : conjugate value = value := sub_eq_zero.mp hspan
  have upper : -value.c1 = value.c1 := congrArg (fun x : QM31 => x.c1) equal
  have twoNonzero : (2 : CM31) ≠ 0 := NeZero.ne _
  have doubled : (2 : CM31) * value.c1 = 0 := by
    calc
      (2 : CM31) * value.c1 = value.c1 - (-value.c1) := by ring
      _ = 0 := by rw [upper]; ring
  exact hguard ((mul_eq_zero.mp doubled).resolve_left twoNonzero)

/-- The coefficients are determined entirely by the sampled OOD point and
the *statement's* public claim roster; the batch challenge is not an input. -/
noncomputable def publicCoefficients {n : Nat} (sampleY : QM31)
    (claims : Fin n → QM31) : Fin n → LineCoeffs QM31 :=
  fun i => conjugateLineCoeffs sampleY (conjugate sampleY)
    (claims i) (conjugate (claims i)) 1

theorem public_coefficients_of_statement_match {n : Nat}
    (sampleY : QM31) (proofClaims statementClaims : Fin n → QM31)
    (matched : proofClaims = statementClaims) :
    publicCoefficients sampleY proofClaims =
      publicCoefficients sampleY statementClaims := by
  rw [matched]

/-- Only the two fields used by the CAS05 statement-bound source/claim
admission. Native profile equality and shape checks are source-pinned
separately, while `Fin n` fixes this row's column count in the theorem. -/
structure SourceStatement (H : Type*) (n : Nat) where
  sourceRoot : H
  claims : Fin n → QM31

def statementMatches {n : Nat} (proofHeader statement : SourceStatement H n) : Prop :=
  proofHeader.sourceRoot = statement.sourceRoot ∧
    proofHeader.claims = statement.claims

/-- Accepted XDM04 node openings and public-statement claim matching provide
the fixed original row and fixed recipe roster used by the prior paired-batch
theorem. The two openings must have the same root, level and position; absent
a concrete node/upper hash collision, the batch consumes the committed row.
No global polynomial degree or adaptive-challenge claim follows. -/
theorem authenticated_public_row_batch {n : Nat}
    (nodeHash : NodeInput H → H) (upperHash : H × H → H)
    (depth position : Nat)
    (proofHeader statement : SourceStatement H n)
    (nativeChildren committedChildren : Option (H × H))
    (nativePath committedPath : List H)
    (opened committedSource : Fin n → Base)
    (challenge pointX pointY : QM31) (rowX rowY : Base)
    (matched : statementMatches proofHeader statement)
    (native : acceptedNodeOpening nodeHash upperHash proofHeader.sourceRoot depth position
      (nativeChildren, List.ofFn opened) nativePath)
    (committed : acceptedNodeOpening nodeHash upperHash statement.sourceRoot depth position
      (committedChildren, List.ofFn committedSource) committedPath)
    (noCollision : ¬collisionOnNodeOpenings nodeHash upperHash position
      (nativeChildren, List.ofFn opened)
      (committedChildren, List.ofFn committedSource)
      nativePath committedPath)
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
  have acceptedAtStatementRoot : acceptedNodeOpening nodeHash upperHash
      statement.sourceRoot depth position
      (nativeChildren, List.ofFn opened) nativePath := by
    simpa only [hroot] using native
  have rowEquality : List.ofFn opened = List.ofFn committedSource :=
    xdm_row_refines_committed_row nodeHash upperHash statement.sourceRoot
      depth position _ _ nativePath committedPath acceptedAtStatementRoot
      committed noCollision
  have sourceEquality : opened = committedSource := List.ofFn_injective rowEquality
  subst opened
  dsimp only
  rw [hclaims]
  obtain ⟨hchecked, _, hbatch⟩ := accepted_row_local_refinement
    challenge pointX pointY rowX rowY
    (publicCoefficients pointY statement.claims) committedSource
    hcircle hrow hguard
  exact ⟨conjugate_span_nonzero pointY hguard, hchecked, hbatch⟩

end S31.Gadgets.PcsFri.PairedBatchSourceCustody
