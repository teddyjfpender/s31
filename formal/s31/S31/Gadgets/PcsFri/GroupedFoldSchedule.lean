import S31.Gadgets.PcsFri.FoldAlgebra

/-!
An algebraic interface for the native *line* part of a grouped FRI fold.

`foldLineNWithWorkspace` draws one `alpha` for an authenticated layer and
uses `alpha, alpha², alpha⁴, ...` in successive butterflies. This file shows
that, when the opened leaf values and inverse coordinates are fixed before
that draw, an `n`-fold output is the evaluation of one polynomial of degree
at most `2^n - 1` in `alpha`. For four line folds the bound is 15.

This is not a FRI proximity or commitment-error theorem. It does not model
the first circle-to-line accumulation, the batch insertions, adaptive oracle
selection, or the Merkle/Fiat--Shamir reduction. In particular it does not
license four applications of a theorem using fresh independent challenges.
-/

namespace S31.Gadgets.PcsFri.GroupedFoldSchedule

open Polynomial
open S31.Gadgets.PcsFri.FoldAlgebra

variable {F : Type*} [Field F]

/-- A polynomial for one native inverse-butterfly, with the challenge used at
zero-indexed depth `step`. The `invCoord` and both input polynomials are fixed
before the challenge is evaluated. -/
noncomputable def pairPolynomial (invCoord : F) (step : Nat)
    (left right : Polynomial F) : Polynomial F :=
  (left + right) + X ^ (2 ^ step) * ((left - right) * C invCoord)

theorem eval_pairPolynomial (invCoord alpha : F) (step : Nat)
    (left right : Polynomial F) :
    eval alpha (pairPolynomial invCoord step left right) =
      pairFold (challengeAt alpha step) invCoord
        (eval alpha left) (eval alpha right) := by
  simp [pairPolynomial, pairFold, challengeAt]

theorem pairPolynomial_natDegree_le (invCoord : F) (step d : Nat)
    (left right : Polynomial F)
    (hl : left.natDegree ≤ d) (hr : right.natDegree ≤ d) :
    (pairPolynomial invCoord step left right).natDegree ≤ d + 2 ^ step := by
  have hsum : (left + right).natDegree ≤ d :=
    natDegree_add_le_of_degree_le hl hr
  have hdiff : (left - right).natDegree ≤ d :=
    (natDegree_sub_le left right).trans (max_le hl hr)
  have hscaled : ((left - right) * C invCoord).natDegree ≤ d := by
    calc
      _ ≤ (left - right).natDegree + (C invCoord).natDegree := natDegree_mul_le
      _ ≤ d := by simpa using hdiff
  have hchallenge :
      (X ^ (2 ^ step) * ((left - right) * C invCoord)).natDegree ≤
        2 ^ step + d := by
    calc
      _ ≤ (X ^ (2 ^ step) : Polynomial F).natDegree +
            ((left - right) * C invCoord).natDegree := natDegree_mul_le
      _ ≤ 2 ^ step + d := by simpa using hscaled
  unfold pairPolynomial
  have hleft : (left + right).natDegree ≤ d + 2 ^ step :=
    hsum.trans (Nat.le_add_right _ _)
  have hright :
      (X ^ (2 ^ step) * ((left - right) * C invCoord)).natDegree ≤
        d + 2 ^ step := by simpa [add_comm] using hchallenge
  exact (natDegree_add_le _ _).trans (max_le hleft hright)

/-- A complete binary butterfly tree. The branch coordinate is the inverse
coordinate used for that pair; every leaf is an opened QM31 value. -/
inductive FullTree (F : Type u) : Nat → Type u where
  | leaf : F → FullTree F 0
  | branch {n : Nat} : F → FullTree F n → FullTree F n → FullTree F (n + 1)

noncomputable def polynomial : {n : Nat} → FullTree F n → Polynomial F
  | 0, .leaf value => C value
  | n + 1, .branch invCoord left right =>
      pairPolynomial invCoord n (polynomial left) (polynomial right)

def evaluate (alpha : F) : {n : Nat} → FullTree F n → F
  | 0, .leaf value => value
  | n + 1, .branch invCoord left right =>
      pairFold (challengeAt alpha n) invCoord
        (evaluate alpha left) (evaluate alpha right)

/-- The fixed butterfly tree evaluates exactly as its one-variable challenge
polynomial. This is a local algebraic identity for line folds. -/
theorem eval_polynomial (alpha : F) {n : Nat} (tree : FullTree F n) :
    eval alpha (polynomial tree) = evaluate alpha tree := by
  induction tree with
  | leaf value => simp [polynomial, evaluate]
  | branch invCoord left right ihl ihr =>
      simp [polynomial, evaluate, eval_pairPolynomial, ihl, ihr]

/-- Reusing powers of one challenge gives a degree bound of `2^n-1` for a
fixed `n`-fold line tree. This is the algebraic input for a future grouped
round failure bound, not such a bound itself. -/
theorem polynomial_natDegree_le {n : Nat} (tree : FullTree F n) :
    (polynomial tree).natDegree ≤ 2 ^ n - 1 := by
  induction tree with
  | leaf value => simp [polynomial]
  | @branch n invCoord left right ihl ihr =>
      have h := pairPolynomial_natDegree_le invCoord n (2 ^ n - 1)
        (polynomial left) (polynomial right) ihl ihr
      simpa only [polynomial] using
        (show (pairPolynomial invCoord n (polynomial left)
          (polynomial right)).natDegree ≤ 2 ^ (n + 1) - 1 from by
            have hp : 1 ≤ 2 ^ n := by
              have hpos : 0 < 2 ^ n := pow_pos (by omega) _
              omega
            calc
              _ ≤ (2 ^ n - 1) + 2 ^ n := h
              _ = 2 ^ (n + 1) - 1 := by rw [pow_succ]; omega)

theorem four_line_folds_degree_le (tree : FullTree F 4) :
    (polynomial tree).natDegree ≤ 15 := by
  simpa using polynomial_natDegree_le tree

section CorrelatedChallengeCounterexample

variable [Fintype F]

/-- A simple event that depends on two fold challenges. This is a
distributional counterexample, not an FRI cheating strategy. -/
def bothZero (pair : F × F) : Prop := pair.1 = 0 ∧ pair.2 = 0

/-- The first two challenges of a native group are `alpha` and `alpha²`.
Exactly one seed makes both zero. -/
noncomputable def groupedBothZero : Finset F := by
  classical
  exact Finset.univ.filter fun alpha => bothZero (alpha, challengeAt alpha 1)

/-- With fresh independent challenges, exactly one *pair* makes both zero. -/
noncomputable def independentBothZero : Finset (F × F) := by
  classical
  exact Finset.univ.filter bothZero

theorem groupedBothZero_eq_singleton : groupedBothZero (F := F) = {0} := by
  classical
  ext alpha
  simp [groupedBothZero, bothZero, challengeAt]

theorem independentBothZero_eq_singleton :
    independentBothZero (F := F) = {(0, 0)} := by
  classical
  ext pair
  cases pair with
  | mk first second => simp [independentBothZero, bothZero, Prod.mk.injEq]

theorem groupedBothZero_card : (groupedBothZero (F := F)).card = 1 := by
  rw [groupedBothZero_eq_singleton]
  simp

theorem independentBothZero_card :
    (independentBothZero (F := F)).card = 1 := by
  rw [independentBothZero_eq_singleton]
  simp

omit [Field F] in
theorem independentSampleSpace_card :
    (Finset.univ : Finset (F × F)).card = (Fintype.card F) ^ 2 := by
  simp [Fintype.card_prod, pow_two]

/-- For a field with more than one element, this event has mass `1/q`
under one reused uniform seed, versus `1/q²` under two fresh uniform draws.
The equation is expressed by cross multiplication of the exact finite
counts, so no probability model or random-oracle premise is hidden. -/
theorem grouped_zero_event_exceeds_independent
    (hsize : 1 < Fintype.card F) :
    (groupedBothZero (F := F)).card * (Fintype.card F) ^ 2 >
      (independentBothZero (F := F)).card * Fintype.card F := by
  rw [groupedBothZero_card, independentBothZero_card]
  nlinarith

end CorrelatedChallengeCounterexample

end S31.Gadgets.PcsFri.GroupedFoldSchedule
