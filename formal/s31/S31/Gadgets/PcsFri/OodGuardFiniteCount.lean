import Mathlib.Tactic

/-!
The finite-field part of the CAS05 early OOD guard.  Write a QM31 seed as
`a + b*u` over CM31, where `u² = R`.  The `u` coordinate of its mapped `y`
vanishes exactly when `b = 0` or `a² - R*b² = 1`, away from the two singular
seeds.  This module counts the norm-one conic without enumerating the field.
-/

namespace S31.Gadgets.PcsFri.OodGuardFiniteCount

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [NeZero (2 : K)]

def normOne (R a b : K) : Prop := a ^ 2 - R * b ^ 2 = 1

def conic (R : K) : Type _ := { z : K × K // normOne R z.1 z.2 }

noncomputable instance (R : K) : Fintype (conic R) := by
  classical
  unfold conic
  infer_instance

omit [Fintype K] [DecidableEq K] [NeZero (2 : K)] in
private theorem param_den_ne_zero (R : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (t : K) : 1 - R * t ^ 2 ≠ 0 := by
  intro h
  have ht : t ≠ 0 := by
    intro hz
    simp [hz] at h
  have hsq : (t⁻¹) ^ 2 = R := by
    field_simp [ht]
    linear_combination h
  exact hR t⁻¹ hsq

def param (R t : K) : K × K :=
  ((1 + R * t ^ 2) / (1 - R * t ^ 2),
    (2 * t) / (1 - R * t ^ 2))

omit [Fintype K] [DecidableEq K] [NeZero (2 : K)] in
private theorem param_norm_one (R : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (t : K) :
    normOne R (param R t).1 (param R t).2 := by
  have hd := param_den_ne_zero R hR t
  unfold normOne param
  dsimp
  field_simp [hd]
  ring

omit [Fintype K] [DecidableEq K] in
private theorem param_inverse (R : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (t : K) :
    (param R t).2 / (1 + (param R t).1) = t := by
  have hd := param_den_ne_zero R hR t
  have hs : 1 + (param R t).1 = 2 / (1 - R * t ^ 2) := by
    dsimp [param]
    field_simp [hd]
    ring
  rw [hs]
  dsimp [param]
  have hsne : (2 : K) / (1 - R * t ^ 2) ≠ 0 :=
    div_ne_zero (NeZero.ne (2 : K)) hd
  field_simp [hd, hsne, NeZero.ne (2 : K)]
  have heq : 1 - t ^ 2 * R = 1 - R * t ^ 2 := by ring
  rw [heq]
  exact mul_div_cancel_right₀ t hd

omit [Fintype K] [DecidableEq K] in
private theorem conic_other_has_param (R a b : K)
    (h : normOne R a b) (ha : 1 + a ≠ 0) :
    param R (b / (1 + a)) = (a, b) := by
  unfold normOne at h
  have hd : 1 - R * (b / (1 + a)) ^ 2 = 2 / (1 + a) := by
    field_simp [ha]
    linear_combination h
  unfold param
  apply Prod.ext
  · dsimp
    rw [hd]
    field_simp [ha, NeZero.ne (2 : K)]
    linear_combination -h
  · dsimp
    rw [hd]
    field_simp [ha, NeZero.ne (2 : K)]

omit [Fintype K] [DecidableEq K] [NeZero (2 : K)] in
private theorem conic_minus_one (R a b : K)
    (h : normOne R a b) (ha : 1 + a = 0)
    (hR : R ≠ 0) : a = -1 ∧ b = 0 := by
  have haa : a = -1 := by linear_combination ha
  subst a
  have hb2 : b ^ 2 = 0 := by
    unfold normOne at h
    have hmul : R * b ^ 2 = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hmul).resolve_left hR
  exact ⟨rfl, (eq_zero_of_pow_eq_zero hb2)⟩

def optionPoint (R : K) (hR : ∀ v : K, v ^ 2 ≠ R) :
    Option K → conic R
  | none => ⟨(-1, 0), by simp [normOne]⟩
  | some t => ⟨param R t, param_norm_one R hR t⟩

omit [Fintype K] in
theorem optionPoint_bijective (R : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) :
    Function.Bijective (optionPoint R hR) := by
  have hRn : R ≠ 0 := by
    intro hz
    exact hR 0 (by simp [hz])
  constructor
  · intro s t hst
    cases s with
    | none =>
      cases t with
      | none => rfl
      | some t =>
        have hx : (param R t).1 = -1 :=
          congrArg (fun z : conic R => z.1.1) hst.symm
        have hden : 1 + (param R t).1 ≠ 0 := by
          have hd := param_den_ne_zero R hR t
          have hs : 1 + (param R t).1 = 2 / (1 - R * t ^ 2) := by
            dsimp [param]
            field_simp [hd]
            ring
          rw [hs]
          exact div_ne_zero (NeZero.ne (2 : K)) hd
        exact False.elim (hden (by rw [hx]; ring))
    | some s =>
      cases t with
      | none =>
        have hx : (param R s).1 = -1 :=
          congrArg (fun z : conic R => z.1.1) hst
        have hden : 1 + (param R s).1 ≠ 0 := by
          have hd := param_den_ne_zero R hR s
          have hs : 1 + (param R s).1 = 2 / (1 - R * s ^ 2) := by
            dsimp [param]
            field_simp [hd]
            ring
          rw [hs]
          exact div_ne_zero (NeZero.ne (2 : K)) hd
        exact False.elim (hden (by rw [hx]; ring))
      | some t =>
        have hx : (param R s).1 = (param R t).1 :=
          congrArg (fun z : conic R => z.1.1) hst
        have hy : (param R s).2 = (param R t).2 :=
          congrArg (fun z : conic R => z.1.2) hst
        congr 1
        calc
          s = (param R s).2 / (1 + (param R s).1) :=
            (param_inverse R hR s).symm
          _ = (param R t).2 / (1 + (param R t).1) := by rw [hx, hy]
          _ = t := param_inverse R hR t
  · intro z
    by_cases ha : 1 + z.1.1 = 0
    · have ⟨hx, hy⟩ := conic_minus_one R z.1.1 z.1.2 z.2 ha hRn
      refine ⟨none, ?_⟩
      apply Subtype.ext
      exact Prod.ext hx.symm hy.symm
    · refine ⟨some (z.1.2 / (1 + z.1.1)), ?_⟩
      apply Subtype.ext
      exact conic_other_has_param R z.1.1 z.1.2 z.2 ha

theorem card_conic (R : K) (hR : ∀ v : K, v ^ 2 ≠ R) :
    Fintype.card (conic R) = Fintype.card K + 1 := by
  classical
  have e : Option K ≃ conic R := Equiv.ofBijective _ (optionPoint_bijective R hR)
  rw [← Fintype.card_congr e]
  simp

def bZero (_R : K) : Finset (K × K) :=
  Finset.univ.filter (fun z => z.2 = 0)

noncomputable def normOneSet (R : K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter (fun z => normOne R z.1 z.2)

omit [NeZero (2 : K)] in
private theorem card_b_zero (R : K) : (bZero R).card = Fintype.card K := by
  classical
  let e : K ≃ { z : K × K // z.2 = 0 } := Equiv.ofBijective
    (fun a => (⟨(a, 0), rfl⟩ : { z : K × K // z.2 = 0 }))
    (by
      constructor
      · intro a b hab
        exact congrArg (fun z : { z : K × K // z.2 = 0 } => z.1.1) hab
      · intro z
        refine ⟨z.1.1, ?_⟩
        apply Subtype.ext
        exact Prod.ext rfl z.2.symm)
  rw [bZero, ← Fintype.card_subtype (fun z : K × K => z.2 = 0)]
  exact Fintype.card_congr e.symm

private theorem card_norm_one_set (R : K) (hR : ∀ v : K, v ^ 2 ≠ R) :
    (normOneSet R).card = Fintype.card K + 1 := by
  classical
  rw [normOneSet, ← Fintype.card_subtype (fun z : K × K => normOne R z.1 z.2)]
  exact card_conic R hR

private theorem card_overlap (R : K) :
    ((bZero R) ∩ (normOneSet R)).card = 2 := by
  classical
  have h1 : (1 : K) ≠ -1 := by
    intro h
    have : (2 : K) = 0 := by linear_combination h
    exact (NeZero.ne (2 : K)) this
  have heq : (bZero R) ∩ (normOneSet R) =
      ({(1, 0), (-1, 0)} : Finset (K × K)) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', hn'⟩
      have hb : z.2 = 0 := (Finset.mem_filter.mp hb').2
      have hn : normOne R z.1 z.2 := by
        simpa [normOneSet] using hn'
      have ha : z.1 ^ 2 = 1 := by simpa [normOne, hb] using hn
      rcases sq_eq_one_iff.mp ha with ha | ha
      · left; exact Prod.ext ha hb
      · right; exact Prod.ext ha hb
    · rintro (hz | hz)
      · subst z; simp [bZero, normOneSet, normOne]
      · subst z; simp [bZero, normOneSet, normOne]
  rw [heq]
  simp [h1, Prod.mk.injEq]

/-- Before removing singular seeds, `b=0` or norm one covers exactly
`2*|K|-1` pairs. The overlap consists of `(1,0)` and `(-1,0)`. -/
theorem card_zero_or_norm_one (R : K) (hR : ∀ v : K, v ^ 2 ≠ R) :
    ((bZero R) ∪ (normOneSet R)).card = 2 * Fintype.card K - 1 := by
  have hb := card_b_zero R
  have hn := card_norm_one_set R hR
  have hi := card_overlap R
  have hu := Finset.card_union_add_card_inter (bZero R) (normOneSet R)
  rw [hb, hn, hi] at hu
  omega

/-- Norm of `1 + (a+b*u)²` in the quadratic extension `u²=R`. -/
def denominatorNorm (R a b : K) : K :=
  (1 + a ^ 2 + R * b ^ 2) ^ 2 - R * (2 * a * b) ^ 2

/-- The `u` coefficient of the native `y=2t/(1+t²)` rational map. -/
def yUpper (R a b : K) : K :=
  (2 * b * (1 - a ^ 2 + R * b ^ 2)) / denominatorNorm R a b

omit [Fintype K] [DecidableEq K] in
theorem y_upper_zero_iff (R a b : K)
    (hd : denominatorNorm R a b ≠ 0) :
    yUpper R a b = 0 ↔ b = 0 ∨ normOne R a b := by
  have hnum :
      2 * b * (1 - a ^ 2 + R * b ^ 2) = 0 ↔
        b = 0 ∨ normOne R a b := by
    rw [mul_eq_zero]
    constructor
    · rintro (hb | hq)
      · left
        exact (mul_eq_zero.mp hb).resolve_left (NeZero.ne (2 : K))
      · right
        unfold normOne
        linear_combination -hq
    · rintro (hb | hq)
      · left; simp [hb]
      · right
        unfold normOne at hq
        linear_combination -hq
  unfold yUpper
  rw [div_eq_zero_iff]
  simp [hd, hnum]

omit [Fintype K] [NeZero (2 : K)] in
private theorem norm_zero_second (R c d : K)
    (hR : ∀ v : K, v ^ 2 ≠ R)
    (h : c ^ 2 - R * d ^ 2 = 0) : d = 0 := by
  by_contra hd
  have hs : (c / d) ^ 2 = R := by
    field_simp [hd]
    linear_combination h
  exact hR (c / d) hs

omit [Fintype K] in
/-- Since `-1` already has a square root in CM31, a nonsquare `R` makes
every singular rational-map seed lie in the `b=0` subfield. -/
theorem denominator_zero_implies_b_zero (R i a b : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1)
    (hd : denominatorNorm R a b = 0) : b = 0 := by
  have hcross : 2 * a * b = 0 := by
    apply norm_zero_second R (1 + a ^ 2 + R * b ^ 2) (2 * a * b) hR
    exact hd
  have hab : a = 0 ∨ b = 0 := by
    have h2 : 2 * (a * b) = 0 := by simpa [mul_assoc] using hcross
    have hab0 := (mul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : K))
    exact mul_eq_zero.mp hab0
  rcases hab with ha | hb
  · by_contra hb
    have hc : 1 + R * b ^ 2 = 0 := by
      have hwhole : 1 + a ^ 2 + R * b ^ 2 = 0 := by
        unfold denominatorNorm at hd
        have hsq : (1 + a ^ 2 + R * b ^ 2) ^ 2 = 0 := by
          simpa [hcross] using hd
        exact eq_zero_of_pow_eq_zero hsq
      simpa [ha] using hwhole
    have hs : (i / b) ^ 2 = R := by
      field_simp [hb]
      rw [hi]
      linear_combination -hc
    exact hR (i / b) hs
  · exact hb

noncomputable def acceptedGuard (R : K) : Finset (K × K) :=
  Finset.univ \ ((bZero R) ∪ (normOneSet R))

/-- This is the actual quotient guard: singular seeds are rejected, and
regular seeds pass precisely when the upper CM31 coefficient of `y` is
nonzero. -/
theorem accepted_guard_iff (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1) (z : K × K) :
    z ∈ acceptedGuard R ↔
      denominatorNorm R z.1 z.2 ≠ 0 ∧ yUpper R z.1 z.2 ≠ 0 := by
  have hset : z ∈ (bZero R) ∪ (normOneSet R) ↔
      z.2 = 0 ∨ normOne R z.1 z.2 := by
    simp [bZero, normOneSet]
  simp only [acceptedGuard, Finset.mem_sdiff, Finset.mem_univ, true_and, hset]
  constructor
  · intro hz
    have hd : denominatorNorm R z.1 z.2 ≠ 0 := by
      intro he
      exact hz (Or.inl (denominator_zero_implies_b_zero R i z.1 z.2 hR hi he))
    refine ⟨hd, ?_⟩
    intro hy
    exact hz ((y_upper_zero_iff R z.1 z.2 hd).mp hy)
  · rintro ⟨hd, hy⟩ hz
    exact hy ((y_upper_zero_iff R z.1 z.2 hd).mpr hz)

theorem accepted_guard_card (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (_hi : i ^ 2 = -1) :
    (acceptedGuard R).card = (Fintype.card K - 1) ^ 2 := by
  have hc := card_zero_or_norm_one R hR
  have hsub : ((bZero R) ∪ (normOneSet R)) ⊆ (Finset.univ : Finset (K × K)) :=
    Finset.subset_univ _
  have htotal : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  rw [acceptedGuard, Finset.card_sdiff_of_subset hsub, Finset.card_univ,
    Fintype.card_prod, hc]
  cases hq : Fintype.card K with
  | zero => contradiction
  | succ n =>
    simp only [Nat.add_sub_cancel_right]
    have hA : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have hB : (n + 1) * (n + 1) = n ^ 2 + (2 * n + 1) := by ring
    rw [hA, hB]
    omega

noncomputable def singularSet (R : K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter (fun z => denominatorNorm R z.1 z.2 = 0)

theorem singular_set_eq_pair (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1) :
    singularSet R = ({(i, 0), (-i, 0)} : Finset (K × K)) := by
  ext z
  simp only [singularSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hd
    have hb := denominator_zero_implies_b_zero R i z.1 z.2 hR hi hd
    have ha2 : z.1 ^ 2 = i ^ 2 := by
      unfold denominatorNorm at hd
      simp [hb] at hd
      have ha0 : 1 + z.1 ^ 2 = 0 := hd
      linear_combination ha0 - hi
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha2 with ha | ha
    · left; exact Prod.ext ha hb
    · right; exact Prod.ext ha hb
  · rintro (hz | hz)
    · subst z
      simp [denominatorNorm, hi]
    · subst z
      simp [denominatorNorm, hi]

theorem singular_set_card (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1) :
    (singularSet R).card = 2 := by
  have hi0 : i ≠ 0 := by
    intro hz
    simp [hz] at hi
  have hine : i ≠ -i := by
    intro he
    have h2 : (2 : K) * i = 0 := by linear_combination he
    exact hi0 ((mul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : K)))
  rw [singular_set_eq_pair R i hR hi]
  simp [Prod.mk.injEq, hine]

noncomputable def excludedRegular (R : K) : Finset (K × K) :=
  ((bZero R) ∪ (normOneSet R)) \ singularSet R

/-- The exact regular-seed count suppressed by the CAS05 `y.c1 != 0`
guard, in any odd quadratic tower whose lower field has size `Q`. -/
theorem excluded_regular_card (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1) :
    (excludedRegular R).card = 2 * Fintype.card K - 3 := by
  have hsub : singularSet R ⊆ (bZero R) ∪ (normOneSet R) := by
    intro z hz
    have hd : denominatorNorm R z.1 z.2 = 0 := by
      simpa [singularSet] using hz
    exact Finset.mem_union.mpr (Or.inl (by
      simpa [bZero] using denominator_zero_implies_b_zero R i z.1 z.2 hR hi hd))
  rw [excludedRegular, Finset.card_sdiff_of_subset hsub,
    card_zero_or_norm_one R hR, singular_set_card R i hR hi]
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  omega

end S31.Gadgets.PcsFri.OodGuardFiniteCount
