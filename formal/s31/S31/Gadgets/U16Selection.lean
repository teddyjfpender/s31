import S31.Gadgets.FunctionalConditional

/-!
Vector selection for the u16-backed nominal source types. The backend's
selector uses the same field equation on each limb; an explicit bit premise
covers even the empty-index mathematical case. S31 runtime arrays are
nonempty. These theorems state why a selected digit needs no new independent
range witness when both source digits are range checked.

The relation is a mathematical model of the local constraints, not a proof
that every production Zig profile emits them exactly.
-/

namespace S31.Functional

def U16VectorSelect {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31) : Prop :=
  (selector = 0 ∨ selector = 1) ∧
  ∀ i, fieldSelect selector (onFalse i) (onTrue i) (output i)

theorem u16_vector_select_iff {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31) :
    U16VectorSelect selector onFalse onTrue output ↔
      (selector = 0 ∧ output = onFalse) ∨
      (selector = 1 ∧ output = onTrue) := by
  constructor
  · rintro ⟨bit, lanes⟩
    rcases bit with hzero | hone
    · left
      refine ⟨hzero, funext fun i => ?_⟩
      rcases (field_select_iff _ _ _ _).mp (lanes i) with chosen | chosen
      · exact chosen.2
      · exact False.elim ((by decide : (0 : M31) ≠ 1)
          (hzero.symm.trans chosen.1))
    · right
      refine ⟨hone, funext fun i => ?_⟩
      rcases (field_select_iff _ _ _ _).mp (lanes i) with chosen | chosen
      · exact False.elim ((by decide : (0 : M31) ≠ 1)
          (chosen.1.symm.trans hone))
      · exact chosen.2
  · rintro (⟨hzero, rfl⟩ | ⟨hone, rfl⟩)
    · refine ⟨Or.inl hzero, ?_⟩
      intro i
      exact (field_select_iff _ _ _ _).mpr (Or.inl ⟨hzero, rfl⟩)
    · refine ⟨Or.inr hone, ?_⟩
      intro i
      exact (field_select_iff _ _ _ _).mpr (Or.inr ⟨hone, rfl⟩)

/-- A selected u16 limb is one of two already bounded input limbs. -/
theorem u16_vector_select_bounded {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31)
    (hfalse : ∀ i, (onFalse i).val < 65536)
    (htrue : ∀ i, (onTrue i).val < 65536)
    (accepted : U16VectorSelect selector onFalse onTrue output) :
    ∀ i, (output i).val < 65536 := by
  rcases (u16_vector_select_iff selector onFalse onTrue output).mp accepted with
    ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact hfalse
  · exact htrue

/-! The u16 compiler path uses separate subtraction, two multiplications,
and an addition for each limb. Model all three intermediate wires as arbitrary
witnesses rather than replacing them with the final selector expression. -/

def U16LaneWires (selector onFalse onTrue output : M31) : Prop :=
  ∃ complement leftTerm rightTerm : Field.F,
    complement + Field.toZMod selector = 1 ∧
    leftTerm = complement * Field.toZMod onFalse ∧
    rightTerm = Field.toZMod selector * Field.toZMod onTrue ∧
    Field.toZMod output = leftTerm + rightTerm

theorem u16_lane_wires_iff (selector onFalse onTrue output : M31) :
    Gadgets.bit (Field.toZMod selector) ∧
      U16LaneWires selector onFalse onTrue output ↔
      fieldSelect selector onFalse onTrue output := by
  constructor
  · rintro ⟨hbit, complement, leftTerm, rightTerm, hc, hl, hr, ho⟩
    have hc' : complement = 1 - Field.toZMod selector := by
      linear_combination hc
    change Gadgets.selectConstraint (Field.toZMod selector)
      (Field.toZMod onFalse) (Field.toZMod onTrue) (Field.toZMod output)
    refine ⟨hbit, sub_eq_zero.mpr ?_⟩
    calc
      Field.toZMod output = leftTerm + rightTerm := ho
      _ = (1 - Field.toZMod selector) * Field.toZMod onFalse +
          Field.toZMod selector * Field.toZMod onTrue := by rw [hl, hr, hc']
  · intro accepted
    change Gadgets.selectConstraint (Field.toZMod selector)
      (Field.toZMod onFalse) (Field.toZMod onTrue) (Field.toZMod output)
      at accepted
    refine ⟨accepted.1, 1 - Field.toZMod selector,
      (1 - Field.toZMod selector) * Field.toZMod onFalse,
      Field.toZMod selector * Field.toZMod onTrue, ?_, rfl, rfl, ?_⟩
    · ring
    · exact sub_eq_zero.mp accepted.2

def U16WireVectorSelect {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31) : Prop :=
  Gadgets.bit (Field.toZMod selector) ∧
  ∀ i, U16LaneWires selector (onFalse i) (onTrue i) (output i)

/-- The actual four-operation witness shape is sound and complete for the
same pointwise selector relation, even when the vector has no limbs. -/
theorem u16_wire_vector_select_iff {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31) :
    U16WireVectorSelect selector onFalse onTrue output ↔
      U16VectorSelect selector onFalse onTrue output := by
  constructor
  · rintro ⟨hbit, hwires⟩
    have hselector : selector = 0 ∨ selector = 1 := by
      rcases (Gadgets.bit_sound_complete _).mp hbit with hzero | hone
      · exact Or.inl (Field.toZMod_injective (by simpa [Field.toZMod_zero] using hzero))
      · exact Or.inr (Field.toZMod_injective (by simpa [Field.toZMod_one] using hone))
    exact ⟨hselector, fun i => (u16_lane_wires_iff _ _ _ _).mp ⟨hbit, hwires i⟩⟩
  · rintro ⟨hselector, hlanes⟩
    have hbit : Gadgets.bit (Field.toZMod selector) := by
      apply (Gadgets.bit_sound_complete _).mpr
      rcases hselector with hzero | hone
      · exact Or.inl (by simp [hzero, Field.toZMod_zero])
      · exact Or.inr (by simp [hone, Field.toZMod_one])
    exact ⟨hbit, fun i => ((u16_lane_wires_iff _ _ _ _).mpr (hlanes i)).2⟩

theorem u16_wire_vector_select_bounded {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31)
    (hfalse : ∀ i, (onFalse i).val < 65536)
    (htrue : ∀ i, (onTrue i).val < 65536)
    (accepted : U16WireVectorSelect selector onFalse onTrue output) :
    ∀ i, (output i).val < 65536 :=
  u16_vector_select_bounded selector onFalse onTrue output hfalse htrue
    ((u16_wire_vector_select_iff selector onFalse onTrue output).mp accepted)

/-! Relate the gadget premises to the normalized source value model. A u16
value in relation IR is a list of canonical limbs; `Value.valid` checks each
limb. The source evaluator chooses the false arm exactly when the selector's
canonical value is zero. -/

def U16Value {n : Nat} (words : Fin n → M31) : Value :=
  ⟨.u16, List.ofFn words⟩

theorem u16_value_valid_iff {n : Nat} (words : Fin n → M31) :
    (U16Value words).valid = true ↔ ∀ i, (words i).val < 65536 := by
  simp [U16Value, Value.valid, List.all_eq_true, List.mem_ofFn]

/-- The range premises of the witness theorem follow from the relation IR's
own validation predicate; the selected output also satisfies it. -/
theorem u16_wire_vector_value_valid {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31)
    (hfalse : (U16Value onFalse).valid = true)
    (htrue : (U16Value onTrue).valid = true)
    (accepted : U16WireVectorSelect selector onFalse onTrue output) :
    (U16Value output).valid = true := by
  apply (u16_value_valid_iff output).mpr
  exact u16_wire_vector_select_bounded selector onFalse onTrue output
    ((u16_value_valid_iff onFalse).mp hfalse)
    ((u16_value_valid_iff onTrue).mp htrue) accepted

/-- This uses the same canonical zero test and arm order as `evaluateNode`'s
normalized `select` case, for every satisfying intermediate witness. -/
theorem u16_wire_vector_matches_source {n : Nat} (selector : M31)
    (onFalse onTrue output : Fin n → M31)
    (accepted : U16WireVectorSelect selector onFalse onTrue output) :
    U16Value output =
      if selector.val == 0 then U16Value onFalse else U16Value onTrue := by
  rcases (u16_vector_select_iff selector onFalse onTrue output).mp
    ((u16_wire_vector_select_iff selector onFalse onTrue output).mp accepted) with
    ⟨hzero, hout⟩ | ⟨hone, hout⟩
  · subst selector
    subst output
    rfl
  · subst selector
    subst output
    rfl

end S31.Functional
