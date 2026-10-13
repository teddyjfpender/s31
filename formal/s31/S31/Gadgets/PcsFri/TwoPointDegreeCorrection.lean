import S31.Gadgets.PcsFri.PairedProtocolRecurrence
import Mathlib.Tactic

/-!
A precise ordinary-polynomial analogue of Protocol 4's own-quotient degree
correction. This file does **not** identify native circle polynomials with
`F[X]`. In particular the native circle vanishing line is not asserted to
have the degree of the quadratic divisor used below. A future circle-basis
refinement must supply its actual point-removal and degree laws.

What is proved here: two distinct claimed points determine an affine line;
when an original polynomial agrees with those claims, its residual is
divisible by the two-point vanishing polynomial. An exact reconstruction
`f = line + vanishing * q` makes the degree of `q` smaller than that of `f`
by the divisor degree, except for the zero quotient. Conversely, a bounded
own quotient reconstructs a bounded original. A finite Protocol 3 batch of
such original/own-quotient pairs stays under the same degree bound. No
commitment, approximate agreement, Fiat–Shamir, or security bound is used.
-/

namespace S31.Gadgets.PcsFri.TwoPointDegreeCorrection

open Polynomial

variable {F : Type*} [Field F]

noncomputable def vanishing (a b : F) : Polynomial F :=
  (X - C a) * (X - C b)

noncomputable def claimLine (a b va vb : F) : Polynomial F :=
  C va + C ((vb - va) / (b - a)) * (X - C a)

theorem claimLine_eval_left (a b va vb : F) :
    (claimLine a b va vb).eval a = va := by
  simp [claimLine]

theorem claimLine_eval_right (a b va vb : F) (hab : a ≠ b) :
    (claimLine a b va vb).eval b = vb := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  simp [claimLine, hba]

theorem claimLine_natDegree_le_one (a b va vb : F) :
    (claimLine a b va vb).natDegree ≤ 1 := by
  unfold claimLine
  have hterm :
      (C ((vb - va) / (b - a)) * (X - C a)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  exact (natDegree_add_le _ _).trans (max_le (by simp) hterm)

theorem vanishing_natDegree (a b : F) :
    (vanishing a b).natDegree = 2 := by
  have ha : (X - C a : Polynomial F) ≠ 0 := X_sub_C_ne_zero a
  have hb : (X - C b : Polynomial F) ≠ 0 := X_sub_C_ne_zero b
  simp [vanishing, natDegree_mul ha hb]

theorem vanishing_ne_zero (a b : F) : vanishing a b ≠ 0 := by
  intro hzero
  have hdegree := vanishing_natDegree a b
  simp [hzero] at hdegree

/-- Agreement with two distinct claims gives exact two-point removal. -/
theorem exists_own_quotient (a b va vb : F) (hab : a ≠ b)
    (f : Polynomial F) (ha : f.eval a = va) (hb : f.eval b = vb) :
    ∃ q : Polynomial F, f = claimLine a b va vb + vanishing a b * q := by
  have hroota : (X - C a) ∣ f - claimLine a b va vb := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, ha, claimLine_eval_left, sub_self]
  have hrootb : (X - C b) ∣ f - claimLine a b va vb := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, hb, claimLine_eval_right a b va vb hab,
      sub_self]
  have hcop : IsCoprime (X - C a : Polynomial F) (X - C b) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  obtain ⟨q, hq⟩ := hcop.mul_dvd hroota hrootb
  refine ⟨q, ?_⟩
  unfold vanishing
  calc
    f = claimLine a b va vb + (f - claimLine a b va vb) := by ring
    _ = claimLine a b va vb + (X - C a) * (X - C b) * q := by rw [hq]

/-- Exact reconstruction and a nonzero divisor force the quotient's degree
down by the divisor's degree. The `q=0` branch handles the zero polynomial
without pretending its natural degree is negative. -/
theorem quotient_degree_of_reconstruction
    (f line divisor q : Polynomial F) (d m : Nat)
    (hdivisor : divisor ≠ 0) (hdegree : divisor.natDegree = m)
    (hreconstruct : f = line + divisor * q)
    (hf : f.natDegree < d) (hline : line.natDegree < d) :
    q = 0 ∨ m + q.natDegree < d := by
  by_cases hq : q = 0
  · exact Or.inl hq
  right
  have hresidual : (f - line).natDegree < d :=
    (natDegree_sub_le f line).trans_lt (max_lt hf hline)
  have hproduct : f - line = divisor * q := by rw [hreconstruct]; ring
  rw [hproduct, natDegree_mul hdivisor hq, hdegree] at hresidual
  exact hresidual

/-- The converse: a low-degree own quotient and exact reconstruction bound
the original. Checking only the quotient, without reconstruction, does not. -/
theorem reconstructed_degree_of_quotient
    (f line divisor q : Polynomial F) (d m : Nat)
    (hdegree : divisor.natDegree = m)
    (hreconstruct : f = line + divisor * q)
    (hline : line.natDegree < d)
    (hq : q = 0 ∨ m + q.natDegree < d) :
    f.natDegree < d := by
  have hproduct : (divisor * q).natDegree < d := by
    rcases hq with hzero | hbound
    · simp [hzero, Nat.zero_lt_of_lt hline]
    · exact (natDegree_mul_le (p := divisor) (q := q)).trans_lt
        (by simpa [hdegree] using hbound)
  rw [hreconstruct]
  exact (natDegree_add_le _ _).trans_lt (max_lt hline hproduct)

/-- A fixed original, interpolation line, and nonzero vanishing polynomial
determine at most one exact own quotient. -/
theorem own_quotient_unique
    (f line divisor q₁ q₂ : Polynomial F)
    (hdivisor : divisor ≠ 0)
    (h₁ : f = line + divisor * q₁)
    (h₂ : f = line + divisor * q₂) : q₁ = q₂ := by
  have hproducts : divisor * q₁ = divisor * q₂ :=
    add_left_cancel (h₁.symm.trans h₂)
  exact mul_left_cancel₀ hdivisor hproducts

theorem exists_unique_own_quotient (a b va vb : F) (hab : a ≠ b)
    (f : Polynomial F) (ha : f.eval a = va) (hb : f.eval b = vb) :
    ∃! q : Polynomial F,
      f = claimLine a b va vb + vanishing a b * q := by
  obtain ⟨q, hq⟩ := exists_own_quotient a b va vb hab f ha hb
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  exact own_quotient_unique f (claimLine a b va vb)
    (vanishing a b) q' q (vanishing_ne_zero a b) hq' hq

/-- The concrete two-point divisor has ordinary polynomial degree two. -/
theorem two_point_quotient_degree
    (a b va vb : F) (hab : a ≠ b) (f : Polynomial F) (d : Nat)
    (hd : 2 ≤ d) (hf : f.natDegree < d)
    (ha : f.eval a = va) (hb : f.eval b = vb) :
    ∃ q : Polynomial F,
      f = claimLine a b va vb + vanishing a b * q ∧
      (q = 0 ∨ 2 + q.natDegree < d) := by
  obtain ⟨q, hq⟩ := exists_own_quotient a b va vb hab f ha hb
  refine ⟨q, hq, ?_⟩
  apply quotient_degree_of_reconstruction f (claimLine a b va vb)
    (vanishing a b) q d 2
  · exact vanishing_ne_zero a b
  · exact vanishing_natDegree a b
  · exact hq
  · exact hf
  · exact (claimLine_natDegree_le_one a b va vb).trans_lt (by omega)

/-- Polynomial version of the exact `f₀, q₀, f₁, q₁, ...` batch. -/
noncomputable def polynomialBatch (challenge : F) (column : Nat) :
    List (Polynomial F × Polynomial F) → Polynomial F
  | [] => 0
  | (original, quotient) :: rest =>
      C (challenge ^ (2 * column)) * original +
        C (challenge ^ (2 * column + 1)) * quotient +
        polynomialBatch challenge (column + 1) rest

/-- Evaluation of the derived polynomial agrees with the previously proved
Protocol 3 value-batch on the original/own-quotient evaluations. -/
theorem polynomialBatch_eval (challenge x : F) (column : Nat)
    (columns : List (Polynomial F × Polynomial F)) :
    (polynomialBatch challenge column columns).eval x =
      PairedProtocolRecurrence.batchPowers challenge column
        (columns.map fun (original, quotient) =>
          (original.eval x, quotient.eval x)) := by
  induction columns generalizing column with
  | nil => simp [polynomialBatch, PairedProtocolRecurrence.batchPowers]
  | cons head tail ih =>
      rcases head with ⟨original, quotient⟩
      simp [polynomialBatch, PairedProtocolRecurrence.batchPowers, ih]

theorem polynomialBatch_degree_lt (challenge : F) (column d : Nat)
    (columns : List (Polynomial F × Polynomial F)) (hd : 0 < d)
    (hcolumns : ∀ pair ∈ columns,
      pair.1.natDegree < d ∧ pair.2.natDegree < d) :
    (polynomialBatch challenge column columns).natDegree < d := by
  induction columns generalizing column with
  | nil => simpa [polynomialBatch] using hd
  | cons head tail ih =>
      rcases head with ⟨original, quotient⟩
      have hhead := hcolumns (original, quotient) (by simp)
      have htail : ∀ pair ∈ tail,
          pair.1.natDegree < d ∧ pair.2.natDegree < d := by
        intro pair hmem
        exact hcolumns pair (by simp [hmem])
      have hfirst :
          (C (challenge ^ (2 * column)) * original).natDegree < d :=
        (natDegree_C_mul_le _ _).trans_lt hhead.1
      have hsecond :
          (C (challenge ^ (2 * column + 1)) * quotient).natDegree < d :=
        (natDegree_C_mul_le _ _).trans_lt hhead.2
      have hrest := ih (column + 1) htail
      simp only [polynomialBatch]
      exact (natDegree_add_le _ _).trans_lt
        (max_lt ((natDegree_add_le _ _).trans_lt (max_lt hfirst hsecond)) hrest)

/-- Exact two-point reconstruction gives every quotient a safe degree for
the derived Protocol 3 polynomial batch. This theorem uses a polynomial
identity for every column; it makes no commitment-oracle claim. -/
theorem reconstructed_two_point_batch_degree
    (a b challenge : F) (d : Nat) (hd : 2 ≤ d)
    (columns : List (Polynomial F × Polynomial F))
    (horiginal : ∀ pair ∈ columns, pair.1.natDegree < d)
    (hrelations : ∀ pair ∈ columns,
      ∃ va vb : F,
        pair.1 = claimLine a b va vb + vanishing a b * pair.2) :
    (polynomialBatch challenge 0 columns).natDegree < d := by
  apply polynomialBatch_degree_lt challenge 0 d columns (by omega)
  intro pair hmem
  constructor
  · exact horiginal pair hmem
  obtain ⟨va, vb, hrelation⟩ := hrelations pair hmem
  have hline : (claimLine a b va vb).natDegree < d :=
    (claimLine_natDegree_le_one a b va vb).trans_lt (by omega)
  have hquot := quotient_degree_of_reconstruction pair.1
    (claimLine a b va vb) (vanishing a b) pair.2 d 2
    (vanishing_ne_zero a b)
    (vanishing_natDegree a b) hrelation (horiginal pair hmem) hline
  rcases hquot with hzero | hbound
  · simp [hzero]; omega
  · omega

end S31.Gadgets.PcsFri.TwoPointDegreeCorrection
