import Mathlib.Algebra.Polynomial.Roots
import S31.Gadgets.Air.QuadField
import S31.Gadgets.Air.GateLookup

namespace S31.Gadgets.Air.GateChallenge

open Polynomial
variable {K : Type*} [Field K]

noncomputable def tuplePoly (tuple : Fin 6 → K) : K[X] :=
  ∑ i : Fin 6, C (tuple i) * X ^ i.val

theorem tuplePoly_coeff (tuple : Fin 6 → K) (i : Fin 6) :
    (tuplePoly tuple).coeff i.val = tuple i := by
  simp [tuplePoly, Fin.val_inj]

theorem tuplePoly_injective : Function.Injective (tuplePoly (K := K)) := by
  intro left right heq
  funext i
  have h := congrArg (fun p : K[X] => p.coeff i.val) heq
  simpa [tuplePoly_coeff] using h

theorem tuplePoly_natDegree_le (tuple : Fin 6 → K) :
    (tuplePoly tuple).natDegree ≤ 5 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hnot : ∀ i : Fin 6, N ≠ i.val := by
    intro i
    omega
  simp [tuplePoly, hnot]

theorem tuple_collision_roots_card_le (left right : Fin 6 → K) :
    ((tuplePoly left - tuplePoly right).roots).card ≤ 5 := by
  exact (Polynomial.card_roots' _).trans
    ((natDegree_sub_le_of_le (tuplePoly_natDegree_le left)
      (tuplePoly_natDegree_le right)).trans (by decide))

theorem tuple_collision_iff_root (left right : Fin 6 → K)
    (hne : left ≠ right) (alpha : K) :
    eval alpha (tuplePoly left) = eval alpha (tuplePoly right) ↔
      alpha ∈ (tuplePoly left - tuplePoly right).roots := by
  have hpoly : tuplePoly left ≠ tuplePoly right := by
    intro heq
    exact hne (tuplePoly_injective heq)
  have hdiff : tuplePoly left - tuplePoly right ≠ 0 :=
    sub_ne_zero.mpr hpoly
  rw [mem_roots hdiff]
  simp [IsRoot, eval_sub, sub_eq_zero]

def tupleHorner (tuple : Fin 6 → K) (alpha : K) : K :=
  tuple ⟨0, by decide⟩ + alpha *
  (tuple ⟨1, by decide⟩ + alpha *
  (tuple ⟨2, by decide⟩ + alpha *
  (tuple ⟨3, by decide⟩ + alpha *
  (tuple ⟨4, by decide⟩ + alpha * tuple ⟨5, by decide⟩))))

theorem tuplePoly_eval_eq_horner (tuple : Fin 6 → K) (alpha : K) :
    eval alpha (tuplePoly tuple) = tupleHorner tuple alpha := by
  simp [tuplePoly, tupleHorner, Fin.sum_univ_succ]
  ring

def combineTerm (tuple : Fin 6 → K) (alpha z : K) : K :=
  tupleHorner tuple alpha - z

theorem combineTerm_collision_iff (left right : Fin 6 → K)
    (alpha z : K) :
    combineTerm left alpha z = combineTerm right alpha z ↔
      tupleHorner left alpha = tupleHorner right alpha := by
  simp [combineTerm]

noncomputable def collisionChallenges [Fintype K] [DecidableEq K]
    (left right : Fin 6 → K) : Finset K :=
  Finset.univ.filter fun alpha => tupleHorner left alpha = tupleHorner right alpha

theorem collisionChallenges_card_le [Fintype K] [DecidableEq K]
    (left right : Fin 6 → K) (hne : left ≠ right) :
    (collisionChallenges left right).card ≤ 5 := by
  classical
  have hsubset : collisionChallenges left right ⊆
      (tuplePoly left - tuplePoly right).roots.toFinset := by
    intro alpha hmember
    have heq : tupleHorner left alpha = tupleHorner right alpha :=
      (Finset.mem_filter.mp hmember).2
    have hpoly : eval alpha (tuplePoly left) = eval alpha (tuplePoly right) := by
      simpa [tuplePoly_eval_eq_horner] using heq
    exact Multiset.mem_toFinset.mpr
      ((tuple_collision_iff_root left right hne alpha).mp hpoly)
  calc
    (collisionChallenges left right).card ≤
        (tuplePoly left - tuplePoly right).roots.toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ (tuplePoly left - tuplePoly right).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ 5 := tuple_collision_roots_card_le left right

theorem combineTerm_zero_iff (tuple : Fin 6 → K) (alpha z : K) :
    combineTerm tuple alpha z = 0 ↔ z = tupleHorner tuple alpha := by
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    exact sub_eq_zero.mpr h.symm

theorem combineTerm_unique_bad_z (tuple : Fin 6 → K) (alpha : K) :
    ∃! z : K, combineTerm tuple alpha z = 0 := by
  refine ⟨tupleHorner tuple alpha, ?_, ?_⟩
  · simp [combineTerm]
  · intro z hz
    exact (combineTerm_zero_iff tuple alpha z).mp hz

open S31.Gadgets.Packed

abbrev GateSecure := S31.Gadgets.Air.QuadField.QM

private instance : Finite GateSecure :=
  Finite.of_injective
    (fun q : GateSecure => (q.re.re, q.re.im, q.im.re, q.im.im))
    (by
      intro left right h
      have ha : left.re.re = right.re.re := congrArg (fun t => t.1) h
      have hb : left.re.im = right.re.im := congrArg (fun t => t.2.1) h
      have hc : left.im.re = right.im.re := congrArg (fun t => t.2.2.1) h
      have hd : left.im.im = right.im.im := congrArg (fun t => t.2.2.2) h
      exact QuadraticAlgebra.ext
        (QuadraticAlgebra.ext ha hb) (QuadraticAlgebra.ext hc hd))

noncomputable instance : Fintype GateSecure := Fintype.ofFinite _

def secureEquivFour : GateSecure ≃ (F × F × F × F) where
  toFun q := (q.re.re, q.re.im, q.im.re, q.im.im)
  invFun v := ⟨⟨v.1, v.2.1⟩, ⟨v.2.2.1, v.2.2.2⟩⟩
  left_inv q := by
    apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl
  right_inv v := by
    rcases v with ⟨a, b, c, d⟩
    rfl

theorem card_secure : Fintype.card GateSecure = 2147483647 ^ 4 := by
  calc
    Fintype.card GateSecure = Fintype.card (F × F × F × F) :=
      Fintype.card_congr secureEquivFour
    _ = 2147483647 ^ 4 := by norm_num [Fintype.card_prod]

def liftBase (value : F) : GateSecure :=
  ⟨(⟨value, 0⟩ : S31.Gadgets.Air.QuadField.CM), 0⟩

theorem liftBase_injective : Function.Injective liftBase := by
  intro left right h
  simpa [liftBase] using congrArg (fun q : GateSecure => q.re.re) h

/-- The six Gate tuple elements in production order: fixed relation id,
canonical address, then four packed limbs. -/
def gateTuple (address : F) (value : Quad) : Fin 6 → GateSecure :=
  fun i => match i.val with
    | 0 => liftBase 378353459
    | 1 => liftBase address
    | 2 => liftBase value.a
    | 3 => liftBase value.b
    | 4 => liftBase value.c
    | 5 => liftBase value.d
    | _ => liftBase 0

theorem gateTuple_injective (leftAddr rightAddr : F)
    (leftValue rightValue : Quad)
    (h : gateTuple leftAddr leftValue =
      gateTuple rightAddr rightValue) :
    leftAddr = rightAddr ∧ leftValue = rightValue := by
  have haddr : liftBase leftAddr = liftBase rightAddr := by
    simpa [gateTuple] using congrFun h ⟨1, by decide⟩
  have ha : liftBase leftValue.a = liftBase rightValue.a := by
    simpa [gateTuple] using congrFun h ⟨2, by decide⟩
  have hb : liftBase leftValue.b = liftBase rightValue.b := by
    simpa [gateTuple] using congrFun h ⟨3, by decide⟩
  have hc : liftBase leftValue.c = liftBase rightValue.c := by
    simpa [gateTuple] using congrFun h ⟨4, by decide⟩
  have hd : liftBase leftValue.d = liftBase rightValue.d := by
    simpa [gateTuple] using congrFun h ⟨5, by decide⟩
  have haddr := liftBase_injective haddr
  have ha := liftBase_injective ha
  have hb := liftBase_injective hb
  have hc := liftBase_injective hc
  have hd := liftBase_injective hd
  exact ⟨haddr, Quad.ext ha hb hc hd⟩

theorem gateTuple_collision_card_le (leftAddr rightAddr : F)
    (leftValue rightValue : Quad)
    (hne : leftAddr ≠ rightAddr ∨ leftValue ≠ rightValue) :
    (collisionChallenges (gateTuple leftAddr leftValue)
      (gateTuple rightAddr rightValue)).card ≤ 5 := by
  apply collisionChallenges_card_le
  intro h
  obtain ⟨ha, hv⟩ := gateTuple_injective _ _ _ _ h
  exact hne.elim (· ha) (· hv)

theorem gateTuple_collision_rate_le (leftAddr rightAddr : F)
    (leftValue rightValue : Quad)
    (hne : leftAddr ≠ rightAddr ∨ leftValue ≠ rightValue) :
    ((collisionChallenges (gateTuple leftAddr leftValue)
      (gateTuple rightAddr rightValue)).card : ℚ) /
        Fintype.card GateSecure ≤
      5 / (2147483647 ^ 4 : ℚ) := by
  rw [card_secure]
  have hcount := gateTuple_collision_card_le _ _ _ _ hne
  have hcast :
      ((collisionChallenges (gateTuple leftAddr leftValue)
        (gateTuple rightAddr rightValue)).card : ℚ) ≤ 5 := by
    exact_mod_cast hcount
  exact div_le_div_of_nonneg_right hcast (by positivity)

def eventTuple (event : S31.Gadgets.Air.GateLookup.Event) :
    Fin 6 → GateSecure :=
  gateTuple (event.1 : F) event.2

theorem eventTuple_injective_of_canonical
    (left right : S31.Gadgets.Air.GateLookup.Event)
    (hleft : left.1 < 2147483647)
    (hright : right.1 < 2147483647)
    (heq : eventTuple left = eventTuple right) :
    left = right := by
  obtain ⟨haddr, hvalue⟩ := gateTuple_injective
    (left.1 : F) (right.1 : F) left.2 right.2 heq
  have hnat : left.1 = right.1 := by
    have hval := congrArg ZMod.val haddr
    simpa [ZMod.val_natCast_of_lt hleft,
      ZMod.val_natCast_of_lt hright] using hval
  exact Prod.ext hnat hvalue

theorem canonical_event_collision_rate_le
    (left right : S31.Gadgets.Air.GateLookup.Event)
    (hleft : left.1 < 2147483647)
    (hright : right.1 < 2147483647)
    (hne : left ≠ right) :
    ((collisionChallenges (eventTuple left) (eventTuple right)).card : ℚ) /
        Fintype.card GateSecure ≤
      5 / (2147483647 ^ 4 : ℚ) := by
  apply gateTuple_collision_rate_le
  by_cases hv : left.2 = right.2
  · left
    intro ha
    have ht : eventTuple left = eventTuple right := by
      simp [eventTuple, ha, hv]
    exact hne (eventTuple_injective_of_canonical left right hleft hright ht)
  · exact Or.inr hv

theorem example_zero_alpha_collision (z : GateSecure) :
    combineTerm (gateTuple 7 (base 5)) 0 z =
      combineTerm (gateTuple 7 (base 4)) 0 z := by
  simp [combineTerm, tupleHorner, gateTuple]

/-- A union bound over a finite list of distinct tuple pairs. -/
noncomputable def collisionUnion [Fintype K] [DecidableEq K] :
    List ((Fin 6 → K) × (Fin 6 → K)) → Finset K
  | [] => ∅
  | pair :: rest =>
      collisionChallenges pair.1 pair.2 ∪ collisionUnion rest

theorem collisionUnion_card_le [Fintype K] [DecidableEq K]
    (pairs : List ((Fin 6 → K) × (Fin 6 → K)))
    (hne : ∀ pair ∈ pairs, pair.1 ≠ pair.2) :
    (collisionUnion pairs).card ≤ 5 * pairs.length := by
  induction pairs with
  | nil => simp [collisionUnion]
  | cons pair rest ih =>
      have hp : pair.1 ≠ pair.2 := hne pair (by simp)
      have hrest : ∀ p ∈ rest, p.1 ≠ p.2 := by
        intro p hmem
        exact hne p (by simp [hmem])
      calc
        (collisionUnion (pair :: rest)).card ≤
            (collisionChallenges pair.1 pair.2).card +
              (collisionUnion rest).card := by
          simpa [collisionUnion] using
            Finset.card_union_le
              (collisionChallenges pair.1 pair.2)
              (collisionUnion rest)
        _ ≤ 5 + 5 * rest.length :=
          Nat.add_le_add (collisionChallenges_card_le pair.1 pair.2 hp)
            (ih hrest)
        _ = 5 * (pair :: rest).length := by simp; omega

/-- At a fixed tuple-compression challenge, these are precisely the second
challenges that zero at least one reciprocal denominator. -/
noncomputable def badDenominatorZ [DecidableEq K]
    (tuples : List (Fin 6 → K)) (alpha : K) : Finset K :=
  (tuples.map fun tuple => tupleHorner tuple alpha).toFinset

theorem badDenominatorZ_card_le [DecidableEq K]
    (tuples : List (Fin 6 → K)) (alpha : K) :
    (badDenominatorZ tuples alpha).card ≤ tuples.length := by
  simpa [badDenominatorZ] using
    (List.toFinset_card_le
      (tuples.map fun tuple => tupleHorner tuple alpha))

theorem denominator_zero_iff_mem_badZ [DecidableEq K]
    (tuples : List (Fin 6 → K)) (alpha z : K) :
    z ∈ badDenominatorZ tuples alpha ↔
      ∃ tuple ∈ tuples, combineTerm tuple alpha z = 0 := by
  simp only [badDenominatorZ, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨tuple, hmem, hvalue⟩
    exact ⟨tuple, hmem,
      (combineTerm_zero_iff tuple alpha z).mpr hvalue.symm⟩
  · rintro ⟨tuple, hmem, hzero⟩
    exact ⟨tuple, hmem,
      ((combineTerm_zero_iff tuple alpha z).mp hzero).symm⟩

end S31.Gadgets.Air.GateChallenge
