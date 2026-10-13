import S31.Gadgets.PcsFri.PairedProtocolRecurrence
import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod

/-!
CAS05 source-column binding for a single fixed source row and fixed OOD
metadata. `Recipe` stores the per-column native-shaped conjugate line
coefficients, row y-coordinate, and denominator; `CheckedRecipes` requires
that denominator to be nonzero. The quotient is derived from the
same original source word as its adjacent batch term, with powers
`1, λ, λ², λ³, ...`.

For a fixed number of columns, different source rows give different formal
batch polynomials. A finite challenge set therefore contains at most `2n`
colliding challenges for two fixed, distinct n-column rows. The polynomial
bound is deliberately conservative by one degree. This is a local algebraic
fixed-oracle fact: it assumes the source row and OOD claim metadata are fixed
before λ, and supplies neither Merkle binding, oracle degree/correlated
agreement, adaptive Fiat-Shamir sampling, nor any PCS/FRI security bits.
The recipe models the native CM31 denominator inside the batch field; the
CM31-to-QM31 embedding and compiled Zig arithmetic remain separate refinements.
-/

namespace S31.Gadgets.PcsFri.PairedBatchSourceBinding
open Polynomial
open S31.Gadgets.PcsFri.PairedProtocolRecurrence
open S31.Gadgets.PcsFri.DeepQuotientAlgebra
variable {F : Type*} [Field F]

noncomputable def rowPoly : List (F × F) → Polynomial F
  | [] => 0
  | (original, quotient) :: rest =>
      C original + X * C quotient + X ^ 2 * rowPoly rest

def rowHorner (challenge : F) : List (F × F) → F
  | [] => 0
  | (original, quotient) :: rest =>
      original + challenge * quotient + challenge ^ 2 * rowHorner challenge rest

theorem batchLoop_eq_rowHorner (challenge power : F)
    (columns : List (F × F)) :
    batchLoop challenge power columns = power * rowHorner challenge columns := by
  induction columns generalizing power with
  | nil => simp [batchLoop, rowHorner]
  | cons head tail ih =>
      rcases head with ⟨f, q⟩
      simp only [batchLoop, rowHorner]
      rw [ih (power * challenge * challenge)]
      ring

theorem rowPoly_eval_horner (challenge : F) (columns : List (F × F)) :
    (rowPoly columns).eval challenge = rowHorner challenge columns := by
  induction columns with
  | nil => simp [rowPoly, rowHorner]
  | cons head tail ih =>
      rcases head with ⟨f, q⟩
      simp [rowPoly, rowHorner, ih]
      ring

theorem rowPoly_eval (challenge : F) (columns : List (F × F)) :
    (rowPoly columns).eval challenge = batchLoop challenge 1 columns := by
  rw [rowPoly_eval_horner, batchLoop_eq_rowHorner]
  ring

theorem rowPoly_eval_protocol3 (challenge : F) (columns : List (F × F)) :
    (rowPoly columns).eval challenge = batchPowers challenge 0 columns := by
  rw [rowPoly_eval, native_batch_eq_protocol3]

theorem rowPoly_coeff_zero (f q : F) (tail : List (F × F)) :
    (rowPoly ((f,q)::tail)).coeff 0 = f := by
  simp [rowPoly]

theorem rowPoly_coeff_one (f q : F) (tail : List (F × F)) :
    (rowPoly ((f,q)::tail)).coeff 1 = q := by
  simp only [rowPoly, coeff_add, coeff_C_succ, zero_add]
  rw [coeff_X_pow_mul']
  simp

theorem rowPoly_injective_at_fixed_length (xs ys : List (F × F))
    (hlen : xs.length = ys.length) (hpoly : rowPoly xs = rowPoly ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons head tail ih =>
      cases ys with
      | nil => simp at hlen
      | cons head' tail' =>
          rcases head with ⟨f, q⟩
          rcases head' with ⟨g, r⟩
          have hf : f = g := by
            simpa [rowPoly_coeff_zero] using congrArg (fun p : Polynomial F => p.coeff 0) hpoly
          have hq : q = r := by
            simpa [rowPoly_coeff_one] using congrArg (fun p : Polynomial F => p.coeff 1) hpoly
          have htailpoly : X ^ 2 * rowPoly tail = X ^ 2 * rowPoly tail' := by
            simpa [rowPoly, hf, hq] using hpoly
          have htail : rowPoly tail = rowPoly tail' :=
            mul_left_cancel₀ (by simp : (X : Polynomial F) ^ 2 ≠ 0) htailpoly
          have hlen' : tail.length = tail'.length := by simpa using hlen
          simpa [hf, hq] using ih tail' hlen' htail

theorem rowPoly_natDegree_le (xs : List (F × F)) :
    (rowPoly xs).natDegree ≤ 2 * xs.length := by
  induction xs with
  | nil => simp [rowPoly]
  | cons head tail ih =>
      rcases head with ⟨f, q⟩
      have h0 : (C f : Polynomial F).natDegree ≤ 0 := by simp
      have h1 : (X * C q : Polynomial F).natDegree ≤ 1 := by
        calc
          _ ≤ (X : Polynomial F).natDegree + (C q : Polynomial F).natDegree := natDegree_mul_le
          _ ≤ 1 := by simp
      have h2 : (X ^ 2 * rowPoly tail).natDegree ≤ 2 + 2 * tail.length := by
        calc
          _ ≤ (X ^ 2 : Polynomial F).natDegree + (rowPoly tail).natDegree := natDegree_mul_le
          _ ≤ 2 + 2 * tail.length := by simpa using Nat.add_le_add_left ih 2
      simp only [rowPoly, List.length_cons]
      calc
        (C f + X * C q + X ^ 2 * rowPoly tail).natDegree ≤
          max (max (C f : Polynomial F).natDegree (X * C q).natDegree)
            (X ^ 2 * rowPoly tail).natDegree :=
          (natDegree_add_le _ _).trans (max_le_max_right _ (natDegree_add_le _ _))
        _ ≤ 2 * (tail.length + 1) := by omega

/-- A fixed metadata entry determines one native-style own quotient from an original word. -/
structure Recipe (F : Type*) where
  coeffs : LineCoeffs F
  rowY : F
  denominator : F

def ownQuotient (recipe : Recipe F) (original : F) : F :=
  lineResidual recipe.coeffs recipe.rowY original /
    recipe.denominator

/-- The native verifier rejects a zero quotient denominator. The CAS05
OOD guard and circle/tower lemmas must supply this premise for every opened
row before the abstract recipe can model an accepted native batch. -/
def CheckedRecipes {n : Nat} (recipes : Fin n → Recipe F) : Prop :=
  ∀ i, (recipes i).denominator ≠ 0

def claimRecipe (sampleY conjugateY sampleValue conjugateValue
    rowY denominator : F) : Recipe F :=
  { coeffs := conjugateLineCoeffs sampleY conjugateY
      sampleValue conjugateValue 1
    rowY := rowY
    denominator := denominator }

theorem claimRecipe_own_quotient_eq_interpolation
    (sampleY conjugateY sampleValue conjugateValue rowY denominator original : F)
    (hspan : conjugateY - sampleY ≠ 0) :
    ownQuotient (claimRecipe sampleY conjugateY sampleValue conjugateValue
      rowY denominator) original =
      ((conjugateY - sampleY) *
        (original - conjugateInterpolant sampleY conjugateY
          sampleValue conjugateValue rowY)) / denominator := by
  exact own_quotient_eq_interpolation sampleY conjugateY sampleValue
    conjugateValue rowY original denominator hspan

theorem ownQuotient_cross_mul (recipe : Recipe F) (original : F)
    (hden : recipe.denominator ≠ 0) :
    ownQuotient recipe original * recipe.denominator =
      lineResidual recipe.coeffs recipe.rowY original := by
  simp [ownQuotient, hden]

def sourcePairs {n : Nat} (recipes : Fin n → Recipe F) (source : Fin n → F) :
    List (F × F) :=
  List.ofFn fun i => (source i, ownQuotient (recipes i) (source i))

theorem sourcePairs_length {n : Nat} (recipes : Fin n → Recipe F)
    (source : Fin n → F) : (sourcePairs recipes source).length = n := by
  simp [sourcePairs]

theorem sourcePairs_injective {n : Nat} (recipes : Fin n → Recipe F) :
    Function.Injective (sourcePairs recipes) := by
  intro source source' h
  have hpair : (fun i : Fin n =>
      (source i, ownQuotient (recipes i) (source i))) =
      (fun i : Fin n =>
      (source' i, ownQuotient (recipes i) (source' i))) := by
    exact List.ofFn_injective h
  funext i
  exact congrArg Prod.fst (congrFun hpair i)

theorem source_batch_polynomial_injective {n : Nat}
    (recipes : Fin n → Recipe F) :
    Function.Injective (fun source : Fin n → F => rowPoly (sourcePairs recipes source)) := by
  intro source source' hpoly
  apply sourcePairs_injective recipes
  exact rowPoly_injective_at_fixed_length _ _
    (by simp [sourcePairs_length]) hpoly

/-- With a fixed source roster and OOD metadata before the batch challenge,
two different source oracles can collide on at most `2n` field challenges.
This is an algebraic fixed-oracle count, not a Fiat-Shamir reduction. -/
theorem source_batch_collision_card [DecidableEq F] {n : Nat} (recipes : Fin n → Recipe F)
    (source source' : Fin n → F) (hsource : source ≠ source')
    (challenges : Finset F) :
    (challenges.filter fun challenge =>
      batchLoop challenge 1 (sourcePairs recipes source) =
      batchLoop challenge 1 (sourcePairs recipes source')).card ≤ 2 * n := by
  classical
  let p := rowPoly (sourcePairs recipes source)
  let q := rowPoly (sourcePairs recipes source')
  have hpq : p ≠ q := by
    intro h
    exact hsource (source_batch_polynomial_injective recipes h)
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsubset :
      ((challenges.filter fun challenge =>
        batchLoop challenge 1 (sourcePairs recipes source) =
        batchLoop challenge 1 (sourcePairs recipes source')).val) ⊆
      (p - q).roots := by
    intro challenge hmem
    have hcollision := (Finset.mem_filter.mp hmem).2
    apply (Polynomial.mem_roots hd).2
    simp only [Polynomial.IsRoot, eval_sub]
    simpa [p, q, rowPoly_eval] using sub_eq_zero.mpr hcollision
  have hcard := Polynomial.card_le_degree_of_subset_roots hsubset
  have hdeg : (p - q).natDegree ≤ 2 * n := by
    calc
      _ ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
      _ ≤ 2 * n := by
        apply max_le
        · simpa [p, sourcePairs_length] using
            rowPoly_natDegree_le (sourcePairs recipes source)
        · simpa [q, sourcePairs_length] using
            rowPoly_natDegree_le (sourcePairs recipes source')
  exact hcard.trans hdeg

/-- The acceptance-facing version names the native zero-denominator check.
It gives both the checked own-quotient identity and the fixed-metadata
challenge count; the guard-to-`CheckedRecipes` Zig refinement is separate. -/
theorem checked_source_quotients_and_collision [DecidableEq F] {n : Nat}
    (recipes : Fin n → Recipe F) (hchecked : CheckedRecipes recipes)
    (source source' : Fin n → F) (hsource : source ≠ source')
    (challenges : Finset F) :
    (∀ i, ownQuotient (recipes i) (source i) *
      (recipes i).denominator =
      lineResidual (recipes i).coeffs (recipes i).rowY (source i)) ∧
    (challenges.filter fun challenge =>
      batchLoop challenge 1 (sourcePairs recipes source) =
      batchLoop challenge 1 (sourcePairs recipes source')).card ≤ 2 * n := by
  constructor
  · intro i
    exact ownQuotient_cross_mul (recipes i) (source i) (hchecked i)
  · exact source_batch_collision_card recipes source source' hsource challenges

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private def toyRecipe : Fin 1 → Recipe (ZMod 7) := fun _ =>
  { coeffs := { a := 0, b := 0, c := 1 }
    rowY := 0
    denominator := 1 }
private def toyZero : Fin 1 → ZMod 7 := fun _ => 0
private def toyOne : Fin 1 → ZMod 7 := fun _ => 1

/-- The two distinct one-column sources collide at `λ=-1` when the quotient
equals the original. A challenge bound is needed; deterministic equality at
every challenge would be false. -/
theorem toy_distinct_sources_collide_at_six :
    batchLoop (6 : ZMod 7) 1 (sourcePairs toyRecipe toyZero) =
      batchLoop (6 : ZMod 7) 1 (sourcePairs toyRecipe toyOne) := by
  decide

theorem toy_distinct_sources_separate_at_zero :
    batchLoop (0 : ZMod 7) 1 (sourcePairs toyRecipe toyZero) ≠
      batchLoop (0 : ZMod 7) 1 (sourcePairs toyRecipe toyOne) := by
  decide

theorem toy_sources_distinct : toyZero ≠ toyOne := by
  decide

end S31.Gadgets.PcsFri.PairedBatchSourceBinding
