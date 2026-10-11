import S31.Gadgets.Air.LogUpCount
import S31.Gadgets.Air.GateChallenge
import Mathlib.Tactic

/-!
Ideal challenge accounting for the experimental two-call tagged pair profile.
The native chip contributes `1/q(call,step,input) - 1/q(call,step+1,output)`;
each of the bridge's sixteen rows contributes four paired Gate fractions and
one paired chip-endpoint fraction, each scaled by `1/16`. The lemmas below
identify these exact fractions with reciprocal event sums when denominators
are nonzero. They do not prove that the production AIR/PCS enforces those
fractions or that Fiat–Shamir challenges are independent uniform samples.
-/

namespace S31.Gadgets.Air.TaggedPairChallenge

open Polynomial
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpCount

variable {K : Type*} [Field K]

noncomputable def tuplePoly7 (tuple : Fin 7 → K) : K[X] :=
  ∑ i : Fin 7, C (tuple i) * X ^ i.val

theorem tuplePoly7_coeff (tuple : Fin 7 → K) (i : Fin 7) :
    (tuplePoly7 tuple).coeff i.val = tuple i := by
  simp [tuplePoly7, Fin.val_inj]

theorem tuplePoly7_injective : Function.Injective (tuplePoly7 (K := K)) := by
  intro left right heq
  funext i
  have h := congrArg (fun p : K[X] => p.coeff i.val) heq
  simpa [tuplePoly7_coeff] using h

theorem tuplePoly7_natDegree_le (tuple : Fin 7 → K) :
    (tuplePoly7 tuple).natDegree ≤ 6 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hnot : ∀ i : Fin 7, N ≠ i.val := by
    intro i
    omega
  simp [tuplePoly7, hnot]

theorem tuplePoly7_collision_roots_card_le (left right : Fin 7 → K) :
    ((tuplePoly7 left - tuplePoly7 right).roots).card ≤ 6 := by
  exact (Polynomial.card_roots' _).trans
    ((natDegree_sub_le_of_le (tuplePoly7_natDegree_le left)
      (tuplePoly7_natDegree_le right)).trans (by decide))

theorem tuplePoly7_collision_iff_root (left right : Fin 7 → K)
    (hne : left ≠ right) (alpha : K) :
    eval alpha (tuplePoly7 left) = eval alpha (tuplePoly7 right) ↔
      alpha ∈ (tuplePoly7 left - tuplePoly7 right).roots := by
  have hpoly : tuplePoly7 left ≠ tuplePoly7 right := by
    intro heq
    exact hne (tuplePoly7_injective heq)
  have hdiff : tuplePoly7 left - tuplePoly7 right ≠ 0 :=
    sub_ne_zero.mpr hpoly
  rw [mem_roots hdiff]
  simp [IsRoot, eval_sub, sub_eq_zero]

/-- Native `Elements.combine`: Horner's rule for seven tagged coordinates,
followed by subtraction of `z`. Gate events embed with a zero seventh word. -/
def tupleHorner7 (tuple : Fin 7 → K) (alpha : K) : K :=
  tuple ⟨0, by decide⟩ + alpha *
  (tuple ⟨1, by decide⟩ + alpha *
  (tuple ⟨2, by decide⟩ + alpha *
  (tuple ⟨3, by decide⟩ + alpha *
  (tuple ⟨4, by decide⟩ + alpha *
  (tuple ⟨5, by decide⟩ + alpha * tuple ⟨6, by decide⟩)))))

theorem tuplePoly7_eval_eq_horner (tuple : Fin 7 → K) (alpha : K) :
    eval alpha (tuplePoly7 tuple) = tupleHorner7 tuple alpha := by
  simp [tuplePoly7, tupleHorner7, Fin.sum_univ_succ]
  ring

def combine7 (tuple : Fin 7 → K) (alpha z : K) : K :=
  tupleHorner7 tuple alpha - z

noncomputable def collisionChallenges7 [Fintype K] [DecidableEq K]
    (left right : Fin 7 → K) : Finset K :=
  Finset.univ.filter fun alpha =>
    tupleHorner7 left alpha = tupleHorner7 right alpha

theorem collisionChallenges7_card_le [Fintype K] [DecidableEq K]
    (left right : Fin 7 → K) (hne : left ≠ right) :
    (collisionChallenges7 left right).card ≤ 6 := by
  classical
  have hsubset : collisionChallenges7 left right ⊆
      (tuplePoly7 left - tuplePoly7 right).roots.toFinset := by
    intro alpha hmember
    have heq : tupleHorner7 left alpha = tupleHorner7 right alpha :=
      (Finset.mem_filter.mp hmember).2
    have hpoly : eval alpha (tuplePoly7 left) =
        eval alpha (tuplePoly7 right) := by
      simpa [tuplePoly7_eval_eq_horner] using heq
    exact Multiset.mem_toFinset.mpr
      ((tuplePoly7_collision_iff_root left right hne alpha).mp hpoly)
  calc
    (collisionChallenges7 left right).card ≤
        (tuplePoly7 left - tuplePoly7 right).roots.toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ (tuplePoly7 left - tuplePoly7 right).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ 6 := tuplePoly7_collision_roots_card_le left right

/-- A joint Gate/chip event is represented by its seven compressed words.
Production Gate tuples have a zero seventh word; tagged chip tuples use all
seven words. Relation and call IDs are fixed by the verifier profile. -/
abbrev JointTuple := Fin 7 → GateSecure

open S31.Gadgets.Packed

/-- Native `private_pair_boundary.gateTuple`, padded from six to seven words. -/
def gateTuple7 (address value : F) : JointTuple :=
  fun i => match i.val with
    | 0 => liftBase 378353459
    | 1 => liftBase address
    | 2 => liftBase value
    | _ => 0

theorem padded_gate_compression_eq_six
    (address value : F) (alpha : GateSecure) :
    tupleHorner7 (gateTuple7 address value) alpha =
      GateChallenge.tupleHorner
        (GateChallenge.gateTuple address (base value)) alpha := by
  dsimp [tupleHorner7, GateChallenge.tupleHorner, gateTuple7,
    GateChallenge.gateTuple, base]
  have hzero : liftBase 0 = (0 : GateSecure) := rfl
  simp [hzero]

/-- Native `private_pair_boundary.chipTuple`: verifier-fixed relation and
call tags, witness step, and four state lanes. -/
def chipTuple7 (call step : F) (state : Fin 4 → F) : JointTuple :=
  fun i => match i.val with
    | 0 => liftBase 1395863811
    | 1 => liftBase call
    | 2 => liftBase step
    | 3 => liftBase (state ⟨0, by decide⟩)
    | 4 => liftBase (state ⟨1, by decide⟩)
    | 5 => liftBase (state ⟨2, by decide⟩)
    | 6 => liftBase (state ⟨3, by decide⟩)
    | _ => 0

/-- Equality of seven-word chip tuples preserves both canonical tags and
all four state lanes; field-valued steps still require `R < p` to recover
canonical natural indices. -/
theorem chipTuple7_injective (call₁ call₂ step₁ step₂ : F)
    (state₁ state₂ : Fin 4 → F)
    (heq : chipTuple7 call₁ step₁ state₁ =
      chipTuple7 call₂ step₂ state₂) :
    call₁ = call₂ ∧ step₁ = step₂ ∧ state₁ = state₂ := by
  have hcall : call₁ = call₂ := by
    apply liftBase_injective
    simpa [chipTuple7] using congrFun heq ⟨1, by decide⟩
  have hstep : step₁ = step₂ := by
    apply liftBase_injective
    simpa [chipTuple7] using congrFun heq ⟨2, by decide⟩
  have hstate : state₁ = state₂ := by
    funext i
    fin_cases i
    all_goals
      apply liftBase_injective
      first
      | simpa [chipTuple7] using congrFun heq ⟨3, by decide⟩
      | simpa [chipTuple7] using congrFun heq ⟨4, by decide⟩
      | simpa [chipTuple7] using congrFun heq ⟨5, by decide⟩
      | simpa [chipTuple7] using congrFun heq ⟨6, by decide⟩
  exact ⟨hcall, hstep, hstate⟩

/-- The verifier-fixed relation tags keep padded Gate and tagged-chip events
disjoint as seven-word tuples, regardless of addresses and state values. -/
theorem gate_chip_tuple_ne (address value call step : F)
    (state : Fin 4 → F) :
    gateTuple7 address value ≠ chipTuple7 call step state := by
  intro heq
  have hfirst := congrFun heq ⟨0, by decide⟩
  have hfield : (378353459 : F) = (1395863811 : F) := by
    exact liftBase_injective (by simpa [gateTuple7, chipTuple7] using hfirst)
  have hneq : (378353459 : F) ≠ (1395863811 : F) := by decide
  exact hneq hfield

noncomputable def badAlpha7 (events : List JointTuple) :
    Finset GateSecure := by
  classical
  exact events.toFinset.biUnion fun a =>
    events.toFinset.biUnion fun b =>
      if a = b then ∅ else collisionChallenges7 a b

/-- For `s` distinct joint tuples, at most `6s²` choices of alpha collide
some pair of different seven-coordinate tuples. -/
theorem badAlpha7_card_le (events : List JointTuple) :
    (badAlpha7 events).card ≤ 6 * events.toFinset.card ^ 2 := by
  classical
  let support := events.toFinset
  let s := support.card
  have hinner (a : JointTuple) :
      (support.biUnion fun b =>
        if a = b then ∅ else collisionChallenges7 a b).card ≤ 6 * s := by
    calc
      _ ≤ ∑ b ∈ support,
          (if a = b then (∅ : Finset GateSecure)
            else collisionChallenges7 a b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ support, 6 := by
        apply Finset.sum_le_sum
        intro b _
        by_cases hab : a = b
        · simp [hab]
        · simpa [hab] using collisionChallenges7_card_le a b hab
      _ = 6 * s := by simp [s]; omega
  change (support.biUnion fun a => support.biUnion fun b =>
    if a = b then ∅ else collisionChallenges7 a b).card ≤ 6 * s ^ 2
  calc
    _ ≤ ∑ a ∈ support,
        (support.biUnion fun b =>
          if a = b then ∅ else collisionChallenges7 a b).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ support, 6 * s := by
      exact Finset.sum_le_sum (fun a _ => hinner a)
    _ = 6 * s ^ 2 := by simp [s]; ring

theorem compressed7_injective_outside_badAlpha
    (events : List JointTuple) (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha7 events)
    (a : JointTuple) (ha : a ∈ events)
    (b : JointTuple) (hb : b ∈ events)
    (heq : tupleHorner7 a alpha = tupleHorner7 b alpha) :
    a = b := by
  by_contra hne
  apply hgood
  unfold badAlpha7
  apply Finset.mem_biUnion.mpr
  refine ⟨a, by simpa using ha, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b, by simpa using hb, ?_⟩
  simp [hne, collisionChallenges7, heq]

def compressed7 (alpha : GateSecure) (tuple : JointTuple) : GateSecure :=
  tupleHorner7 tuple alpha

def productionReciprocalSum7 (events : List JointTuple)
    (alpha z : GateSecure) : GateSecure :=
  (events.map fun event => 1 / combine7 event alpha z).sum

theorem productionReciprocalSum7_eq_neg (events : List JointTuple)
    (alpha z : GateSecure) :
    productionReciprocalSum7 events alpha z =
      - (events.map fun event =>
        1 / (z - compressed7 alpha event)).sum := by
  induction events with
  | nil => simp [productionReciprocalSum7]
  | cons event rest ih =>
      unfold productionReciprocalSum7
      simp only [List.map_cons, List.sum_cons]
      rw [show (rest.map fun e => 1 / combine7 e alpha z).sum =
          productionReciprocalSum7 rest alpha z from rfl, ih]
      have hden : combine7 event alpha z =
          -(z - compressed7 alpha event) := by
        simp [combine7, compressed7]
      rw [hden, div_neg]
      ring

noncomputable def badBalanceZ7 (left right : List JointTuple)
    (alpha : GateSecure) : Finset GateSecure :=
  let support := eventSupport (left.map (compressed7 alpha))
    (right.map (compressed7 alpha))
  support ∪ LogUpNumerator.badBalanceZ support
    (netWeight (left.map (compressed7 alpha))
      (right.map (compressed7 alpha)))

/-- Exact joint event balance follows from one closed reciprocal identity at
a challenge outside both pole and cancellation sets, provided compression is
injective on the committed event support. This is a conditional algebraic
reduction. `left` and `right` include the circuit, both chips, and both
bridges; it does not by itself authenticate the five native claimed sums. -/
theorem exact_joint_events_of_good_challenge
    (left right : List JointTuple) (alpha z : GateSecure)
    (hinjective : ∀ a ∈ left ++ right, ∀ b ∈ left ++ right,
      compressed7 alpha a = compressed7 alpha b → a = b)
    (hgoodZ : z ∉ badBalanceZ7 left right alpha)
    (hclosed : productionReciprocalSum7 left alpha z =
      productionReciprocalSum7 right alpha z) :
    left.Perm right := by
  classical
  have hmap : (left.map (compressed7 alpha)).Perm
      (right.map (compressed7 alpha)) := by
    by_contra hnotmap
    have hz : z ∉ eventSupport (left.map (compressed7 alpha))
        (right.map (compressed7 alpha)) := by
      intro hz
      exact hgoodZ (Finset.mem_union_left _ hz)
    have hnotbalance : z ∉ LogUpNumerator.badBalanceZ
        (eventSupport (left.map (compressed7 alpha))
          (right.map (compressed7 alpha)))
        (netWeight (left.map (compressed7 alpha))
          (right.map (compressed7 alpha))) := by
      intro hb
      exact hgoodZ (Finset.mem_union_right _ hb)
    have hrec := reciprocal_rejected_outside_bad_set
      (left.map (compressed7 alpha))
      (right.map (compressed7 alpha)) z hz hnotbalance
    apply hrec
    rw [productionReciprocalSum7_eq_neg,
      productionReciprocalSum7_eq_neg] at hclosed
    exact neg_injective (by simpa only [List.map_map] using hclosed)
  exact mapped_perm_reflects left right (compressed7 alpha)
    hinjective hmap

/-- For unequal lists with total multiplicities below the field
characteristic, the cancellation branch has at most `s−1` good-alpha
challenge values `z`, where `s` is compressed support size. Including poles,
the explicit bad set has cardinality at most `2s`. -/
theorem badBalanceZ7_card_le
    (left right : List JointTuple) (alpha : GateSecure)
    (hinjective : ∀ a ∈ left ++ right, ∀ b ∈ left ++ right,
      compressed7 alpha a = compressed7 alpha b → a = b)
    (hleft : left.length < 2147483647)
    (hright : right.length < 2147483647)
    (hne : ¬ left.Perm right) :
    (badBalanceZ7 left right alpha).card ≤
      2 * (left ++ right).toFinset.card := by
  classical
  let cl := left.map (compressed7 alpha)
  let cr := right.map (compressed7 alpha)
  let support := eventSupport cl cr
  have hnotmapped : ¬ cl.Perm cr := by
    intro hmap
    exact hne (mapped_perm_reflects left right (compressed7 alpha)
      hinjective hmap)
  have hbad : (LogUpNumerator.badBalanceZ support
      (netWeight cl cr)).card ≤ support.card - 1 := by
    exact unequal_lists_bad_balance_card_le cl cr
      (by simpa [cl] using hleft) (by simpa [cr] using hright)
      hnotmapped
  have hsupport : support.card ≤ (left ++ right).toFinset.card := by
    have heq : support = (left ++ right).toFinset.image (compressed7 alpha) := by
      ext value
      simp only [support, cl, cr, eventSupport, List.mem_toFinset,
        List.mem_append, List.mem_map, Finset.mem_image]
      aesop
    rw [heq]
    exact Finset.card_image_le
  unfold badBalanceZ7
  calc
    (support ∪ LogUpNumerator.badBalanceZ support
      (netWeight cl cr)).card ≤
      support.card + (LogUpNumerator.badBalanceZ support
        (netWeight cl cr)).card := Finset.card_union_le _ _
    _ ≤ support.card + (support.card - 1) :=
      Nat.add_le_add_left hbad _
    _ ≤ 2 * (left ++ right).toFinset.card := by omega

noncomputable def badPairs7 (left right : List JointTuple) :
    Finset (GateSecure × GateSecure) := by
  classical
  let badA := badAlpha7 (left ++ right)
  exact (badA.product (Finset.univ : Finset GateSecure)) ∪
    ((Finset.univ : Finset GateSecure).biUnion fun alpha =>
      if alpha ∈ badA then ∅
      else (badBalanceZ7 left right alpha).image fun z => (alpha, z))

/-- A fixed unequal joint multiset can close at no more than
`(6s²+2s)|QM31|` ideal independent challenge pairs, with `s` distinct
seven-coordinate tuples. This requires fewer than `p` events on each side.
It is a combinatorial bound, not a Fiat–Shamir or native verifier theorem. -/
theorem badPairs7_card_le
    (left right : List JointTuple)
    (hleft : left.length < 2147483647)
    (hright : right.length < 2147483647)
    (hne : ¬ left.Perm right) :
    (badPairs7 left right).card ≤
      (6 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card) *
        Fintype.card GateSecure := by
  classical
  let s := (left ++ right).toFinset.card
  let n := Fintype.card GateSecure
  let badA := badAlpha7 (left ++ right)
  let badGood := (Finset.univ : Finset GateSecure).biUnion fun alpha =>
    if alpha ∈ badA then ∅
    else (badBalanceZ7 left right alpha).image fun z => (alpha, z)
  have hgoodCount : badGood.card ≤ n * (2 * s) := by
    calc
      badGood.card ≤ ∑ alpha ∈ (Finset.univ : Finset GateSecure),
          (if alpha ∈ badA then (∅ : Finset (GateSecure × GateSecure))
          else (badBalanceZ7 left right alpha).image
            fun z => (alpha, z)).card := Finset.card_biUnion_le
      _ ≤ ∑ _alpha ∈ (Finset.univ : Finset GateSecure),
          2 * s := by
        apply Finset.sum_le_sum
        intro alpha _
        by_cases ha : alpha ∈ badA
        · simp [ha]
        · simp only [ha, ↓reduceIte]
          have hinj : ∀ a ∈ left ++ right, ∀ b ∈ left ++ right,
              compressed7 alpha a = compressed7 alpha b → a = b := by
            intro a haa b hbb heq
            exact compressed7_injective_outside_badAlpha
              (left ++ right) alpha ha a haa b hbb heq
          exact Finset.card_image_le.trans
            (badBalanceZ7_card_le left right alpha hinj
              hleft hright hne)
      _ = n * (2 * s) := by simp [n]
  have hbadA : badA.card ≤ 6 * s ^ 2 :=
    badAlpha7_card_le (left ++ right)
  change (badA.product (Finset.univ : Finset GateSecure) ∪
    badGood).card ≤ (6 * s ^ 2 + 2 * s) * n
  calc
    (badA.product (Finset.univ : Finset GateSecure) ∪ badGood).card ≤
        (badA.product (Finset.univ : Finset GateSecure)).card +
          badGood.card := Finset.card_union_le _ _
    _ ≤ badA.card * n + n * (2 * s) := by
      simpa [Finset.card_product, n] using
        Nat.add_le_add_left hgoodCount (badA.card * n)
    _ ≤ (6 * s ^ 2) * n + n * (2 * s) := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right n hbadA) _
    _ = (6 * s ^ 2 + 2 * s) * n := by ring

/-- Under an ideal independent uniform draw from `QM31²`, the bound above
has failure fraction at most `(6s² + 2s)/p⁴`. The production transcript is
not modeled by this probability calculation. -/
theorem uniform_pair_failure_rate7_le
    (left right : List JointTuple)
    (hleft : left.length < 2147483647)
    (hright : right.length < 2147483647)
    (hne : ¬ left.Perm right) :
    ((badPairs7 left right).card : ℚ) /
      (Fintype.card GateSecure : ℚ) ^ 2 ≤
      (((6 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card : Nat) : ℚ) /
        (2147483647 ^ 4 : ℚ)) := by
  let n := Fintype.card GateSecure
  let b := 6 * (left ++ right).toFinset.card ^ 2 +
    2 * (left ++ right).toFinset.card
  have hnat := badPairs7_card_le left right hleft hright hne
  have hcast : ((badPairs7 left right).card : ℚ) ≤
      ((b * n : Nat) : ℚ) := by
    exact_mod_cast hnat
  have hn : (0 : ℚ) < n := by
    dsimp [n]
    rw [card_secure]
    positivity
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt hn
  have hcard : (Fintype.card GateSecure : ℚ) =
      (2147483647 : ℚ) ^ 4 := by exact_mod_cast card_secure
  rw [← hcard]
  change ((badPairs7 left right).card : ℚ) / (n : ℚ) ^ 2 ≤
    (b : ℚ) / (n : ℚ)
  calc
    ((badPairs7 left right).card : ℚ) / (n : ℚ) ^ 2 ≤
        ((b * n : Nat) : ℚ) / (n : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hcast (sq_nonneg _)
    _ = (b : ℚ) / (n : ℚ) := by
      push_cast
      field_simp

/-- The exact joint seven-coordinate event multiset is recovered from the
single native-shape reciprocal closure whenever the challenge pair avoids the
explicit collision, pole, and cancellation sets. The theorem's `hclosed`
remains an assumption about field sums, not about PCS/FRI verification. -/
theorem exact_joint_events_outside_badPairs7
    (left right : List JointTuple) (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ badPairs7 left right)
    (hclosed : productionReciprocalSum7 left alpha z =
      productionReciprocalSum7 right alpha z) :
    left.Perm right := by
  classical
  have hnotA : alpha ∉ badAlpha7 (left ++ right) := by
    intro ha
    apply hgood
    apply Finset.mem_union_left
    exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ z⟩
  have hnotZ : z ∉ badBalanceZ7 left right alpha := by
    intro hz
    apply hgood
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨alpha, Finset.mem_univ _, ?_⟩
    simp [hnotA, hz]
  exact exact_joint_events_of_good_challenge left right alpha z
    (by
      intro a ha b hb heq
      exact compressed7_injective_outside_badAlpha
        (left ++ right) alpha hnotA a ha b hb heq)
    hnotZ hclosed

/-- Every denominator used by the joint event lists is nonzero outside
the explicit exceptional pair set; this is needed to interpret the native
inverse constraints and paired bridge fractions. -/
theorem event_denominator_nonzero_outside_badPairs7
    (left right : List JointTuple) (event : JointTuple)
    (hmem : event ∈ left ++ right)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ badPairs7 left right) :
    combine7 event alpha z ≠ 0 := by
  intro hzero
  have hvalue : z = compressed7 alpha event := by
    exact (sub_eq_zero.mp hzero).symm
  have hsupport : compressed7 alpha event ∈
      eventSupport (left.map (compressed7 alpha))
        (right.map (compressed7 alpha)) := by
    simp only [eventSupport, List.mem_toFinset, List.mem_append,
      List.mem_map]
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨event, hl, rfl⟩
    · exact Or.inr ⟨event, hr, rfl⟩
  have hbadZ : z ∈ badBalanceZ7 left right alpha := by
    exact Finset.mem_union_left _ (hvalue ▸ hsupport)
  apply hgood
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨alpha, Finset.mem_univ _, ?_⟩
  by_cases ha : alpha ∈ badAlpha7 (left ++ right)
  · exact False.elim (hgood (Finset.mem_union_left _
      (Finset.mem_product.mpr ⟨ha, Finset.mem_univ z⟩)))
  · simp [ha, hbadZ]

/-- The sign layout after the circuit Gate rows, two chip rows, and two
bridge components have telescoped their interaction columns. Each list
contains seven-word tuples, with six-word Gate tuples padded by zero. -/
def jointSignedClosure
    (circuitYields circuitUses bridgeGates chipInputs chipOutputs
      chipStarts chipEnds : List JointTuple)
    (alpha z : GateSecure) : GateSecure :=
  productionReciprocalSum7 circuitYields alpha z -
  productionReciprocalSum7 circuitUses alpha z +
  productionReciprocalSum7 bridgeGates alpha z +
  productionReciprocalSum7 chipInputs alpha z -
  productionReciprocalSum7 chipOutputs alpha z -
  productionReciprocalSum7 chipStarts alpha z +
  productionReciprocalSum7 chipEnds alpha z

/-- Conditional five-component profile theorem: once the native AIR and
claimed-sum equations are proved to imply this signed rational closure,
a challenge outside the explicit exceptional set authenticates the entire
joint event multiset. -/
theorem exact_joint_events_of_signed_closure
    (circuitYields circuitUses bridgeGates chipInputs chipOutputs
      chipStarts chipEnds : List JointTuple)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ badPairs7
      (circuitYields ++ bridgeGates ++ chipInputs ++ chipEnds)
      (circuitUses ++ chipOutputs ++ chipStarts))
    (hclosed : jointSignedClosure circuitYields circuitUses bridgeGates
      chipInputs chipOutputs chipStarts chipEnds alpha z = 0) :
    (circuitYields ++ bridgeGates ++ chipInputs ++ chipEnds).Perm
      (circuitUses ++ chipOutputs ++ chipStarts) := by
  apply exact_joint_events_outside_badPairs7 _ _ alpha z hgood
  dsimp [jointSignedClosure] at hclosed
  simp only [productionReciprocalSum7, List.map_append, List.sum_append]
  dsimp [productionReciprocalSum7] at hclosed
  linear_combination hclosed

/-- A chip row's native two fractions, with explicit nonpole premises. -/
theorem chip_row_fraction (qin qout : K)
    (hin : qin ≠ 0) (hout : qout ≠ 0) :
    (1 : K) / qin + (-1) / qout = qin⁻¹ - qout⁻¹ := by
  field_simp
  ring

/-- One bridge Gate pair is `1/d0 + 1/d1`, before `1/16` scaling. -/
theorem bridge_gate_pair_fraction (d0 d1 : K)
    (h0 : d0 ≠ 0) (h1 : d1 ≠ 0) :
    (d0 + d1) / (d0 * d1) = d0⁻¹ + d1⁻¹ := by
  field_simp
  ring

/-- One bridge chip pair is `-1/first + 1/last`. -/
theorem bridge_chip_pair_fraction (first last : K)
    (hfirst : first ≠ 0) (hlast : last ≠ 0) :
    (first - last) / (first * last) = -first⁻¹ + last⁻¹ := by
  field_simp
  ring

/-- Repetition over the native bridge's 16 constant rows cancels its `1/16`
weight. This lemma intentionally requires all denominators and `16` nonzero. -/
theorem bridge_sixteen_rows (numerator denominator : K)
    (hden : denominator ≠ 0) (h16 : (16 : K) ≠ 0) :
    (∑ _row : Fin 16, ((numerator / 16) / denominator)) =
      numerator / denominator := by
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- At one fixed challenge, injective and nonzero compressed denominators
are insufficient for exact multiset equality: distinct events can cancel. -/
theorem fixed_challenge_counterexample :
    (1 / (2 : ℚ) + 1 / 12 = 1 / 3 + 1 / 4) ∧
    ¬ ([2, 12] : List ℚ).Perm [3, 4] := by
  constructor
  · norm_num
  · intro hperm
    have hmem : (2 : ℚ) ∈ ([3, 4] : List ℚ) :=
      hperm.mem_iff.mp (by simp)
    norm_num at hmem

end S31.Gadgets.Air.TaggedPairChallenge
