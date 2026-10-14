import S31.Gadgets.PcsFri.Cas07SparseP05Join
import Mathlib.Tactic

/-!
A conditional degree-correction interface for an original-plus-own-quotient
source roster. It keeps three obligations separate:

* a pre-challenge, authenticated *whole* source oracle supplies the opened
  originals (`howned`);
* a native-to-paper FRI theorem supplies bounded original and own-quotient
  candidate polynomials that agree on the stated row sets (`horiginalRows`
  and `hquotientRows`);
* a two-point circle theorem supplies the radius-one interpolation, native
  circle line, its OOD root, and the strict joint-agreement threshold; the
  public claim is explicitly identified with that interpolation at the OOD
  coordinate (`hclaim`).

The theorem below composes those premises. It proves that the claimed OOD
interpolation equals the bounded original at the OOD Fourier coordinate for
every occupied column. It does not derive any of the premises from CAS05
acceptance, establish a probability bound, identify the paper's circle-code
filtration with native columns, or admit experimental CAS05 in production.
-/

namespace S31.Gadgets.PcsFri.PairedRosterDegreeCorrection

open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentQuotient
open S31.Gadgets.PcsFri.Cas07SparseP05Join
open LaurentPolynomial AddMonoidAlgebra

variable {F E : Type*} [Field F] [DecidableEq F]
  [Field E] [Algebra F E]

/-- Two separate proximity row sets are sufficient only when their
intersection clears the circle-Laurent uniqueness threshold. `source` is the
fixed, authenticated whole-oracle value; `opened` is the value used to derive
the quotient. Equality on the domain is an explicit external ownership
premise, rather than a consequence of a sampled Merkle opening. -/
theorem one_column_from_separate_agreement
    (z : Eˣ) (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (n : Nat) (hn : 1 ≤ n)
    (original quotient interpolation : CirclePoly F)
    (horiginal : InCircleBand n original)
    (hquotient : InCircleBand (n - 1) quotient)
    (hinterpolation : InCircleBand 1 interpolation)
    (source opened : Fˣ → F)
    (domainRows originalRows quotientRows : Finset Fˣ)
    (horiginalSubset : originalRows ⊆ domainRows)
    (hquotientSubset : quotientRows ⊆ domainRows)
    (hjoint : domainRows.card + 2 * n <
      originalRows.card + quotientRows.card)
    (howned : ∀ t ∈ domainRows, opened t = source t)
    (hden : ∀ t ∈ domainRows,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (horiginalRows : ∀ t ∈ originalRows,
      eval₂ (RingHom.id F) t original = source t)
    (hquotientRows : ∀ t ∈ quotientRows,
      eval₂ (RingHom.id F) t quotient =
        (opened t - eval₂ (RingHom.id F) t interpolation) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val))
    (claim : E)
    (hclaim : eval₂ (algebraMap F E) z interpolation = claim)
    (hlineRoot : eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0) :
    original = interpolation +
      nativeLineLaurent i x₀ y₀ x₁ y₁ * quotient ∧
    eval₂ (algebraMap F E) z original = claim := by
  let rows := originalRows ∩ quotientRows
  let own : Fˣ → F := fun t =>
    (opened t - eval₂ (RingHom.id F) t interpolation) /
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)
  have hmany : 2 * n < rows.card :=
    intersection_large_enough domainRows originalRows quotientRows n
      horiginalSubset hquotientSubset hjoint
  have hdenRows : ∀ t ∈ rows,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0 := by
    intro t ht
    exact hden t (horiginalSubset (Finset.mem_inter.mp ht).1)
  have hsourceRows : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t original = source t := by
    intro t ht
    exact horiginalRows t (Finset.mem_inter.mp ht).1
  have hownRows : ∀ t ∈ rows,
      own t =
        (source t - eval₂ (RingHom.id F) t interpolation) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) := by
    intro t ht
    dsimp [own]
    rw [howned t (horiginalSubset (Finset.mem_inter.mp ht).1)]
  have hquotRows : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t quotient = own t := by
    intro t ht
    exact hquotientRows t (Finset.mem_inter.mp ht).2
  constructor
  · exact two_point_joint_agreement_forces_relation
      i x₀ y₀ x₁ y₁ hi n hn original quotient interpolation
      horiginal hinterpolation hquotient source own rows hmany
      hdenRows hsourceRows hownRows hquotRows
  · exact (two_point_joint_agreement_forces_ood
      z i x₀ y₀ x₁ y₁ hi n hn original quotient interpolation
      horiginal hinterpolation hquotient source own rows hmany
      hdenRows hsourceRows hownRows hquotRows hlineRoot).trans hclaim

/-- The same conditional result for an arbitrary, possibly sparse,
multi-height original-plus-own-quotient roster. Empty heights and empty
column rosters are vacuous; no phantom source word is inserted. Each occupied
column needs its own bounded quotient and joint row threshold. In particular,
a single batched FRI proximity claim does not discharge these hypotheses. -/
theorem all_roster_columns_from_separate_agreement
    {H : Nat} (columns radius : Fin H → Nat)
    (z : Eˣ) (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (hradius : ∀ height, 1 ≤ radius height)
    (original quotient interpolation :
      (height : Fin H) → Fin (columns height) → CirclePoly F)
    (claim : (height : Fin H) → Fin (columns height) → E)
    (horiginal : ∀ height column,
      InCircleBand (radius height) (original height column))
    (hquotient : ∀ height column,
      InCircleBand (radius height - 1) (quotient height column))
    (hinterpolation : ∀ height column,
      InCircleBand 1 (interpolation height column))
    (source opened :
      (height : Fin H) → Fin (columns height) → Fˣ → F)
    (domainRows : Fin H → Finset Fˣ)
    (originalRows quotientRows :
      (height : Fin H) → Fin (columns height) → Finset Fˣ)
    (horiginalSubset : ∀ height column,
      originalRows height column ⊆ domainRows height)
    (hquotientSubset : ∀ height column,
      quotientRows height column ⊆ domainRows height)
    (hjoint : ∀ height column,
      (domainRows height).card + 2 * radius height <
        (originalRows height column).card +
          (quotientRows height column).card)
    (howned : ∀ height column, ∀ t ∈ domainRows height,
      opened height column t = source height column t)
    (hden : ∀ height, ∀ t ∈ domainRows height,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (horiginalRows : ∀ height column, ∀ t ∈ originalRows height column,
      eval₂ (RingHom.id F) t (original height column) =
        source height column t)
    (hquotientRows : ∀ height column, ∀ t ∈ quotientRows height column,
      eval₂ (RingHom.id F) t (quotient height column) =
        (opened height column t -
          eval₂ (RingHom.id F) t (interpolation height column)) /
            CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
              (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val))
    (hclaim : ∀ height column,
      eval₂ (algebraMap F E) z (interpolation height column) =
        claim height column)
    (hlineRoot : eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0) :
    ∀ height column,
      original height column = interpolation height column +
        nativeLineLaurent i x₀ y₀ x₁ y₁ * quotient height column ∧
      eval₂ (algebraMap F E) z (original height column) =
        claim height column := by
  intro height column
  exact one_column_from_separate_agreement z i x₀ y₀ x₁ y₁ hi
    (radius height) (hradius height)
    (original height column) (quotient height column)
    (interpolation height column)
    (horiginal height column) (hquotient height column)
    (hinterpolation height column)
    (source height column) (opened height column)
    (domainRows height) (originalRows height column)
    (quotientRows height column)
    (horiginalSubset height column) (hquotientSubset height column)
    (hjoint height column) (howned height column)
    (hden height) (horiginalRows height column)
    (hquotientRows height column) (claim height column)
    (hclaim height column) hlineRoot

private def exampleOriginalRows : Finset (Fin 16) :=
  Finset.univ.filter fun row => row.val < 12

private def exampleQuotientRows : Finset (Fin 16) :=
  Finset.univ.filter fun row => 3 ≤ row.val

/-- A hand-sized roster count: twelve original rows (`0..11`) and thirteen
quotient rows (`3..15`) have nine common rows. For radius `n=2`, the strict
uniqueness threshold is five common rows. This checks only set arithmetic on
row IDs; it does not prove native Fourier injectivity or that FRI acceptance
provides either agreement set. -/
theorem sixteen_row_joint_threshold_example :
    exampleOriginalRows.card = 12 ∧
    exampleQuotientRows.card = 13 ∧
    (exampleOriginalRows ∩ exampleQuotientRows).card = 9 ∧
    (Finset.univ : Finset (Fin 16)).card + 2 * 2 <
      exampleOriginalRows.card + exampleQuotientRows.card ∧
    2 * 2 < (exampleOriginalRows ∩ exampleQuotientRows).card := by
  decide

end S31.Gadgets.PcsFri.PairedRosterDegreeCorrection
