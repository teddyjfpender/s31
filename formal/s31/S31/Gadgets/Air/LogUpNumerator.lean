import Mathlib.Algebra.Polynomial.Roots

namespace S31.Gadgets.Air.LogUpNumerator

open Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def numerator (support : Finset K) (weight : K → K) : K[X] :=
  ∑ a ∈ support,
    C (weight a) * ∏ b ∈ support.erase a, (X - C b)

theorem numerator_eval_at (support : Finset K) (weight : K → K)
    (a : K) (ha : a ∈ support) :
    eval a (numerator support weight) =
      weight a * ∏ b ∈ support.erase a, (a - b) := by
  classical
  simp only [numerator, eval_finset_sum, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X]
  apply Finset.sum_eq_single a
  · intro b hb hba
    have hamem : a ∈ support.erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩
    have hzero : ∏ c ∈ support.erase b, (a - c) = 0 :=
      Finset.prod_eq_zero hamem (sub_self a)
    simp [hzero]
  · intro hnot
    exact (hnot ha).elim

theorem numerator_ne_zero (support : Finset K) (weight : K → K)
    (a : K) (ha : a ∈ support) (hw : weight a ≠ 0) :
    numerator support weight ≠ 0 := by
  have hprod : ∏ b ∈ support.erase a, (a - b) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm
  intro hzero
  have heval := numerator_eval_at support weight a ha
  rw [hzero] at heval
  exact (mul_ne_zero hw hprod) (by simpa using heval.symm)

theorem numerator_natDegree_le (support : Finset K)
    (weight : K → K) :
    (numerator support weight).natDegree ≤ support.card - 1 := by
  classical
  unfold numerator
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have hprod := natDegree_prod_le (support.erase a)
    (fun b : K => X - C b)
  have hterm :
      (C (weight a) * ∏ b ∈ support.erase a, (X - C b)).natDegree ≤
        (support.erase a).card := by
    calc
      _ ≤ (C (weight a)).natDegree +
          (∏ b ∈ support.erase a, (X - C b)).natDegree :=
        natDegree_mul_le
      _ ≤ (support.erase a).card := by
        simpa [natDegree_X_sub_C] using hprod
  simpa only [Finset.card_erase_of_mem ha] using hterm

theorem numerator_roots_card_le (support : Finset K)
    (weight : K → K) :
    (numerator support weight).roots.card ≤ support.card - 1 :=
  (Polynomial.card_roots' _).trans (numerator_natDegree_le support weight)

theorem numerator_eval_zero_iff_root (support : Finset K)
    (weight : K → K) (a : K) (ha : a ∈ support)
    (hw : weight a ≠ 0) (z : K) :
    eval z (numerator support weight) = 0 ↔
      z ∈ (numerator support weight).roots := by
  rw [mem_roots (numerator_ne_zero support weight a ha hw)]
  rfl

def denominatorAt (support : Finset K) (z : K) : K :=
  ∏ a ∈ support, (z - a)

def reciprocalSum (support : Finset K) (weight : K → K) (z : K) : K :=
  ∑ a ∈ support, weight a / (z - a)

theorem numerator_eval_eq_denominator_mul_sum
    (support : Finset K) (weight : K → K) (z : K)
    (hz : z ∉ support) :
    eval z (numerator support weight) =
      denominatorAt support z * reciprocalSum support weight z := by
  classical
  simp only [numerator, eval_finset_sum, eval_mul, eval_C, eval_prod,
    eval_sub, eval_X, reciprocalSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hza : z - a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hz (heq.symm ▸ ha)
  have hproduct :
      denominatorAt support z =
        (z - a) * ∏ b ∈ support.erase a, (z - b) := by
    exact (Finset.mul_prod_erase support (fun b => z - b) ha).symm
  rw [hproduct]
  symm
  rw [div_eq_mul_inv]
  calc
    ((z - a) * ∏ b ∈ support.erase a, (z - b)) *
        (weight a * (z - a)⁻¹) =
      (weight a * ∏ b ∈ support.erase a, (z - b)) *
        ((z - a) * (z - a)⁻¹) := by ac_rfl
    _ = weight a * ∏ b ∈ support.erase a, (z - b) := by simp [hza]

noncomputable def badBalanceZ [Fintype K]
    (support : Finset K) (weight : K → K) : Finset K :=
  Finset.univ.filter fun z =>
    z ∉ support ∧ reciprocalSum support weight z = 0

theorem badBalanceZ_card_le [Fintype K]
    (support : Finset K) (weight : K → K)
    (a : K) (ha : a ∈ support) (hw : weight a ≠ 0) :
    (badBalanceZ support weight).card ≤ support.card - 1 := by
  have hsubset : badBalanceZ support weight ⊆
      (numerator support weight).roots.toFinset := by
    intro z hz
    obtain ⟨hzsupport, hzsum⟩ := (Finset.mem_filter.mp hz).2
    have heval : eval z (numerator support weight) = 0 := by
      rw [numerator_eval_eq_denominator_mul_sum support weight z hzsupport,
        hzsum, mul_zero]
    exact Multiset.mem_toFinset.mpr
      ((numerator_eval_zero_iff_root support weight a ha hw z).mp heval)
  calc
    (badBalanceZ support weight).card ≤
        (numerator support weight).roots.toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ (numerator support weight).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ support.card - 1 := numerator_roots_card_le support weight

end S31.Gadgets.Air.LogUpNumerator
