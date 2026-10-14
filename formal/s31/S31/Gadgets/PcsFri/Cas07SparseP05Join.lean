import S31.Gadgets.PcsFri.PairedProtocolRecurrence
import S31.Gadgets.PcsFri.CircleLaurentUniqueness
import Mathlib.Tactic

/-!
Two conditional CAS07/P05 joins. An absent XDM05 source height has an empty
ordered column roster. CAS07 still folds the previous line at that height and
draws its own challenge; it inserts the zero *batch*, not a zero source row.
The first lemmas identify the exact normalized recurrence for this case.

The second join is the two-point analogue of the algebraic uniqueness step in
the S-two degree-corrected batch-opening proof: if an original and its own
quotient have *joint* agreement with bounded circle Laurent polynomials on
more than `2n` distinct Fourier rows, their own-quotient equation holds as a
polynomial identity and forces the claimed OOD value. This assumes the joint
agreement set. It does not extract that set from CAS07 FRI acceptance, tie it
to authenticated native rows, prove the published circle-code filtration, or
transfer a paper soundness bound to native query/Fiat-Shamir sampling.
-/

namespace S31.Gadgets.PcsFri.Cas07SparseP05Join

open S31.Gadgets.PcsFri.PairedProtocolRecurrence
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentQuotient
open S31.Gadgets.PcsFri.CircleLaurentUniqueness
open LaurentPolynomial AddMonoidAlgebra

variable {F : Type*} [Field F]

/-- At an absent height no `f, own-quotient` pair is silently inserted. The
empty batch has zero value for every batch challenge and starting power. -/
theorem absent_batch_zero (batchChallenge power : F) :
    batchLoop batchChallenge power [] = 0 ∧
      batchPowers batchChallenge 0 [] = 0 := by
  simp [batchLoop, batchPowers]

/-- An interior absent height is still a line-fold round. In particular,
dropping that round or reusing the preceding challenge would be a different
protocol. `haccepted` is the checked native row equation, not a theorem about
the Zig verifier's execution. -/
theorem absent_height_native_line_fold (height : Nat) (slot : AcceptedSlot F)
    (hheight : 0 < height) (heven : slot.evenColumns = [])
    (hodd : slot.oddColumns = [])
    (haccepted : slot.forwarded = nativeForward height (nativeRoundOf slot)) :
    slot.forwarded = pair slot.previousLeft slot.previousRight
      slot.lineCoord slot.challenge := by
  rw [haccepted]
  simp [nativeForward, nativeRoundOf, batchLoop, heven, hodd,
    Nat.ne_of_gt hheight, pair, FoldAlgebra.pairFold]

/-- The same zero insertion has the paper's normalized line fold at exactly
the `2^(height+1)` scale. The previous line is divided by `2^height`; the
absent source batch contributes no term even though its challenge is used. -/
theorem absent_height_normalized_line_fold (height : Nat)
    (slot : AcceptedSlot F) (htwo : (2 : F) ≠ 0)
    (hheight : 0 < height) (heven : slot.evenColumns = [])
    (hodd : slot.oddColumns = [])
    (haccepted : slot.forwarded = nativeForward height (nativeRoundOf slot)) :
    slot.forwarded = (2 : F) ^ (height + 1) *
      normalizedPair (slot.previousLeft / (2 : F) ^ height)
        (slot.previousRight / (2 : F) ^ height)
        slot.lineCoord slot.challenge := by
  have h := accepted_slot_refines_protocol3 height slot htwo haccepted
  simpa [protocol3Forward, paperRoundOf, batchPowers, heven, hodd,
    Nat.ne_of_gt hheight, normalizedPair, pair, FoldAlgebra.pairFold] using h

/-- The exact joint-agreement premise needed at one *nonempty* CAS07 height.
The finite set is a common set of rows for the original and own quotient.
Separate proximity sets cannot be substituted without an intersection or
correlated-agreement argument. -/
theorem two_point_joint_agreement_forces_relation [DecidableEq F]
    (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (n : Nat) (hn : 1 ≤ n)
    (original quotient interpolation : CirclePoly F)
    (horiginal : InCircleBand n original)
    (hinterpolation : InCircleBand 1 interpolation)
    (hquotient : InCircleBand (n - 1) quotient)
    (source ownQuotient : Fˣ → F) (rows : Finset Fˣ)
    (hmany : 2 * n < rows.card)
    (hden : ∀ t ∈ rows,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (hsource : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t original = source t)
    (hown : ∀ t ∈ rows,
      ownQuotient t =
        (source t - eval₂ (RingHom.id F) t interpolation) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val))
    (hquot : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t quotient = ownQuotient t) :
    original = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * quotient := by
  apply paired_relation_of_row_agreement i x₀ y₀ x₁ y₁ hi n hn
    original interpolation quotient horiginal hinterpolation hquotient
    rows hmany hden
  intro t ht
  rw [hquot t ht, hown t ht, ← hsource t ht]

/-- A sufficient, explicit way to obtain the common agreement set from two
separately known sets. The bound is strict: each original/quotient proximity
claim alone says nothing about whether the *same* rows are good. The paper's
cross-domain correlated-agreement argument must produce the appropriate
sets and bounds; this finite-set lemma does not do that work. -/
theorem intersection_large_enough {Row : Type*} [DecidableEq Row]
    (domainRows originalRows quotientRows : Finset Row) (n : Nat)
    (horiginal : originalRows ⊆ domainRows)
    (hquotient : quotientRows ⊆ domainRows)
    (hsum : domainRows.card + 2 * n <
      originalRows.card + quotientRows.card) :
    2 * n < (originalRows ∩ quotientRows).card := by
  have hunion : originalRows ∪ quotientRows ⊆ domainRows :=
    Finset.union_subset horiginal hquotient
  have hcard := Finset.card_le_card hunion
  have hpartition := Finset.card_union_add_card_inter originalRows quotientRows
  omega

/-- Gate's smallest occupied source height has `2^4=16` circle rows and
blowup `2^2=4`; its four ordered source coefficients fit the already-proved
radius-two Laurent model. Thus the `>2n` row count is numerically possible:
at least five distinct rows, subject to proving the native Fourier map is
injective on this canonical domain. -/
theorem gate_smallest_height_numeric_room : 2 * 2 < 2 ^ (4 : Nat) := by
  decide

private def gateOriginalRows : Finset (Fin 16) :=
  Finset.univ.filter fun row => row.val < 9

private def gateQuotientRows : Finset (Fin 16) :=
  Finset.univ.filter fun row => 7 ≤ row.val

/-- Two separate 9-of-16 majorities can overlap in just two rows. For
radius `n=2`, this is below the strict five-row uniqueness threshold. The
common good set cannot be inferred from separate majority claims alone. -/
theorem gate_separate_majorities_insufficient :
    gateOriginalRows.card = 9 ∧
      gateQuotientRows.card = 9 ∧
      (gateOriginalRows ∩ gateQuotientRows).card = 2 := by
  decide

/-- If that same native two-point line vanishes at the OOD point, the
polynomial identity obtained from joint agreement forces the claimed value.
The line-root premise is separate from the native guarded-point sampler. -/
theorem two_point_joint_agreement_forces_ood [DecidableEq F]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (n : Nat) (hn : 1 ≤ n)
    (original quotient interpolation : CirclePoly F)
    (horiginal : InCircleBand n original)
    (hinterpolation : InCircleBand 1 interpolation)
    (hquotient : InCircleBand (n - 1) quotient)
    (source ownQuotient : Fˣ → F) (rows : Finset Fˣ)
    (hmany : 2 * n < rows.card)
    (hden : ∀ t ∈ rows,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (hsource : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t original = source t)
    (hown : ∀ t ∈ rows,
      ownQuotient t =
        (source t - eval₂ (RingHom.id F) t interpolation) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val))
    (hquot : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t quotient = ownQuotient t)
    (hlineRoot : eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0) :
    eval₂ (algebraMap F E) z original =
      eval₂ (algebraMap F E) z interpolation := by
  have hrelation := two_point_joint_agreement_forces_relation
    i x₀ y₀ x₁ y₁ hi n hn original quotient interpolation
    horiginal hinterpolation hquotient source ownQuotient rows
    hmany hden hsource hown hquot
  rw [hrelation, map_add, map_mul, hlineRoot, zero_mul, add_zero]

end S31.Gadgets.PcsFri.Cas07SparseP05Join
