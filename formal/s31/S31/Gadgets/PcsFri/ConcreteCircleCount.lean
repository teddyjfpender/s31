import S31.Gadgets.PcsFri.OodRationalMap
import S31.Gadgets.PcsFri.QM31FieldInstance
import Mathlib.Tactic

/-!
The rational OOD map can be counted over the actual modeled finite fields.
This file proves the cardinality of their affine circles from an explicit
seed-to-point equivalence; the support sizes are not postulated numerals.
It does not refine the Zig transcript draw or establish an OOD soundness bound.
-/

namespace S31.Gadgets.PcsFri.ConcreteCircleCount

open OodRationalMap
open NativeTowerFormulas

def qmEquiv (K : Type*) : QM K ≃ CM K × CM K where
  toFun x := (x.c0, x.c1)
  invFun x := ⟨x.1, x.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

noncomputable instance {K : Type*} [Fintype K] : Fintype (QM K) :=
  Fintype.ofEquiv (CM K × CM K) (qmEquiv K).symm

theorem card_qm {K : Type*} [Fintype K] :
    Fintype.card (QM K) = Fintype.card K ^ 4 := by
  rw [Fintype.card_congr (qmEquiv K), Fintype.card_prod,
    ConcreteCM31Tower.card_cm]
  ring

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [NeZero (2 : K)]

noncomputable instance : DecidablePred (regular : K → Prop) :=
  Classical.decPred _

def Circle (K : Type*) [Field K] :=
  { point : K × K // point.1 ^ 2 + point.2 ^ 2 = 1 }

noncomputable instance : Fintype (Circle K) := by
  classical
  unfold Circle
  infer_instance

/-- Adjoin the one point omitted by the regular rational map. -/
def optionSeedToCircle : Option { t : K // regular t } → Circle K
  | none => ⟨(-1, 0), by norm_num⟩
  | some t => ⟨(x t.1, y t.1), on_circle t.1 t.2⟩

omit [Fintype K] in
theorem option_seed_to_circle_bijective :
    Function.Bijective (optionSeedToCircle (K := K)) := by
  constructor
  · intro s t hst
    cases s with
    | none =>
      cases t with
      | none => rfl
      | some t =>
        have hx : x t.1 = -1 :=
          congrArg (fun p : Circle K => p.1.1) hst.symm
        exact False.elim ((one_add_x_ne_zero t.1 t.2) (by rw [hx]; ring))
    | some s =>
      cases t with
      | none =>
        have hx : x s.1 = -1 :=
          congrArg (fun p : Circle K => p.1.1) hst
        exact False.elim ((one_add_x_ne_zero s.1 s.2) (by rw [hx]; ring))
      | some t =>
        have hx : x s.1 = x t.1 :=
          congrArg (fun p : Circle K => p.1.1) hst
        have hy : y s.1 = y t.1 :=
          congrArg (fun p : Circle K => p.1.2) hst
        congr 1
        exact Subtype.ext (injective_on_regular s.1 t.1 s.2 t.2 hx hy)
  · intro p
    by_cases h : 1 + p.1.1 = 0
    · obtain ⟨hx, hy⟩ := omitted_circle_point p.1.1 p.1.2 p.2 h
      refine ⟨none, ?_⟩
      apply Subtype.ext
      exact Prod.ext hx.symm hy.symm
    · obtain ⟨t, ht, hx, hy⟩ :=
        circle_point_has_preimage p.1.1 p.1.2 p.2 h
      refine ⟨some ⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext hx hy

noncomputable def optionSeedCircleEquiv :
    Option { t : K // regular t } ≃ Circle K :=
  Equiv.ofBijective optionSeedToCircle option_seed_to_circle_bijective

omit [NeZero (2 : K)] in
/-- Exactly two seeds are excluded by `1+t²=0` when `i²=-1`. -/
theorem singular_seeds (i : K) (hi : i ^ 2 = -1) :
    (Finset.univ.filter (fun t : K => ¬ regular t)) = {i, -i} := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  unfold regular
  constructor
  · intro h
    have ht : t ^ 2 = i ^ 2 := by
      push Not at h
      linear_combination h - hi
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp ht)
  · rintro (rfl | rfl)
    · simp [hi]
    · simp [hi, even_two]

theorem card_regular_seeds (i : K) (hi : i ^ 2 = -1) :
    Fintype.card { t : K // regular t } = Fintype.card K - 2 := by
  classical
  have hi0 : i ≠ 0 := by
    intro h
    simp [h] at hi
  have hine : i ≠ -i := by
    intro h
    have hmul : (2 : K) * i = 0 := by linear_combination h
    exact hi0 ((mul_eq_zero.mp hmul).resolve_left (NeZero.ne (2 : K)))
  have hsing : (Finset.univ.filter (fun t : K => ¬ regular t)).card = 2 := by
    rw [singular_seeds i hi]
    simp [hine]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset K)) regular
  rw [hsing, Finset.card_univ] at hsplit
  rw [Fintype.card_of_subtype (Finset.univ.filter regular) (by intro x; simp)]
  omega

/-- An affine circle over any finite odd field containing `√(-1)` has
`|K|-1` points. The proof counts the exact rational-map image plus its one
omitted point. -/
theorem card_circle (i : K) (hi : i ^ 2 = -1) :
    Fintype.card (Circle K) = Fintype.card K - 1 := by
  classical
  calc
    Fintype.card (Circle K) =
        Fintype.card (Option { t : K // regular t }) :=
      Fintype.card_congr optionSeedCircleEquiv.symm
    _ = Fintype.card K - 2 + 1 := by
      rw [Fintype.card_option, card_regular_seeds i hi]
    _ = Fintype.card K - 1 := by
      have htwo : 2 ≤ Fintype.card K := by
        have hsub := Finset.card_le_card
          (Finset.filter_subset (s := (Finset.univ : Finset K))
            (p := fun t : K => ¬ regular t))
        rw [singular_seeds i hi] at hsub
        have hi0 : i ≠ 0 := by intro h; simp [h] at hi
        have hine : i ≠ -i := by
          intro h
          have hm : (2 : K) * i = 0 := by linear_combination h
          exact hi0 ((mul_eq_zero.mp hm).resolve_left (NeZero.ne (2 : K)))
        simpa [hine] using hsub
      omega

abbrev CM31 := CM S31.Field.F
abbrev QM31 := QM S31.Field.F

noncomputable instance : DecidableEq QM31 := Classical.decEq _

instance : NeZero (2 : QM31) := ⟨by
  intro h
  have h0 := congrArg (fun z : QM31 => z.c0.a) h
  change (2 : S31.Field.F) = 0 at h0
  exact (show (2 : S31.Field.F) ≠ 0 from by decide) h0⟩

theorem card_qm31 : Fintype.card QM31 = 2147483647 ^ 4 := by
  simpa [QM31, S31.Field.F] using (card_qm (K := S31.Field.F)).trans
    (congrArg (· ^ 4) (ZMod.card 2147483647))

theorem qm_imaginary_square :
    (⟨⟨0, 1⟩, ⟨0, 0⟩⟩ : QM31) ^ 2 = -1 := by
  have hneg : (-1 : QM31) = ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩ := by
    change QM31FieldInstance.toQuadratic.symm (-1) = _
    rfl
  rw [QM31FieldInstance.square_eq_qmSquare]
  rw [hneg]
  ext <;> simp [qmSquare, cmSquare, cmAdd, cmMulByR, cmMul]

theorem card_circle_cm31 :
    Fintype.card (Circle CM31) = 2147483647 ^ 2 - 1 := by
  rw [card_circle (⟨0, 1⟩ : CM31)
    CM31FieldInstance.imaginary_square,
    ConcreteCM31Tower.card_cm31]

theorem card_circle_qm31 :
    Fintype.card (Circle QM31) = 2147483647 ^ 4 - 1 := by
  rw [card_circle (⟨⟨0, 1⟩, ⟨0, 0⟩⟩ : QM31)
    qm_imaginary_square, card_qm31]

theorem cm31_zero_eq : (0 : CM31) = ⟨0, 0⟩ := by
  change CM31FieldInstance.toQuadratic.symm 0 = _
  rfl

noncomputable def embedCM (a : CM31) : QM31 := ⟨a, 0⟩

theorem embedCM_add (a b : CM31) :
    embedCM (a + b) = embedCM a + embedCM b := by
  rw [QM31FieldInstance.add_eq_qmAdd]
  ext <;> simp [embedCM, qmAdd, cmAdd,
    CM31FieldInstance.add_eq_cmAdd, cm31_zero_eq]

theorem embedCM_one : embedCM (1 : CM31) = (1 : QM31) := by
  rw [QM31FieldInstance.one_eq_qmOne]
  rfl

theorem embedCM_square (a : CM31) :
    embedCM (a ^ 2) = (embedCM a) ^ 2 := by
  rw [QM31FieldInstance.square_eq_qmSquare,
    CM31FieldInstance.square_eq_cmSquare]
  ext <;> simp [embedCM, qmSquare, cmSquare, cmAdd, cmMulByR, cmMul,
    cm31_zero_eq]

noncomputable def lowerCircle (p : Circle CM31) : Circle QM31 :=
  ⟨(embedCM p.1.1, embedCM p.1.2), by
    have h := congrArg embedCM p.2
    simpa only [embedCM_add, embedCM_square, embedCM_one] using h⟩

theorem lowerCircle_injective : Function.Injective lowerCircle := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : Circle QM31 => p.1.1.c0) h
  · exact congrArg (fun p : Circle QM31 => p.1.2.c0) h

theorem lower_circle_image_card :
    (Set.range lowerCircle).ncard = 2147483647 ^ 2 - 1 := by
  rw [Set.ncard_range_of_injective lowerCircle_injective,
    Nat.card_eq_fintype_card, card_circle_cm31]

/-- Actual modeled affine two-point universe, excluding the embedded CM31
circle. This cardinality is a set difference theorem, not a bad-set bound
or a native Fiat–Shamir sampler theorem. -/
theorem two_point_universe_card :
    (Set.range lowerCircle)ᶜ.ncard =
      2147483647 ^ 4 - 2147483647 ^ 2 := by
  rw [Set.ncard_compl, Nat.card_eq_fintype_card,
    card_circle_qm31, lower_circle_image_card]
  norm_num

/-- Comparing the actual modeled set difference with the already-proved
CM31 guard seed count leaves exactly `q²−1` omitted support points. This
does not identify the guard's image inside the two-point universe or prove
the native transcript's conditional distribution. -/
theorem concrete_two_point_minus_guarded_count :
    (Set.range lowerCircle)ᶜ.ncard -
      (OodGuardFiniteCount.acceptedGuard (r : CM31)).card =
      2147483647 ^ 2 - 1 := by
  rw [two_point_universe_card, CM31FieldInstance.accepted_guard_card_cm31]
  norm_num

end S31.Gadgets.PcsFri.ConcreteCircleCount
