import S31.Gadgets

namespace S31.Evidence
open Gadgets

theorem honest_byte_boundary : Radix.byteConstraint 255 (255*256) :=
  Radix.byte_complete _ (by decide)

theorem byte_out_of_range : ¬∃ scaled, Radix.byteConstraint 256 scaled := by
  rw [Radix.byte_sound_complete]
  decide

theorem honest_carry : Radix.addConstraint 65536 65535 1 0 0 1 := by
  unfold Radix.addConstraint; decide
theorem honest_borrow : Radix.subConstraint 65536 0 1 0 65535 1 := by
  unfold Radix.subConstraint; decide

theorem checked_overflow_rejected : ¬Radix.AddChain 65536 [65535] [1] [0] 0 0 := by
  intro h
  have heq := Radix.add_chain_equation (Or.inr rfl) h
  norm_num [Words.decode] at heq

theorem checked_underflow_rejected : ¬Radix.SubChain 65536 [0] [1] [65535] 0 0 := by
  intro h
  have heq := Radix.sub_chain_equation (Or.inr rfl) h
  norm_num [Words.decode] at heq

theorem zero_inverse_witness_free (w : Field.F) : zeroConstraint 0 1 w := by simp [zeroConstraint]

theorem nonboolean_rejected : ¬bit (2 : Field.F) := by unfold bit; decide
theorem illegal_selector_rejected : ¬selectConstraint (2 : Field.F) 0 0 0 := by
  unfold selectConstraint bit; decide

theorem signed_positive_overflow :
    ¬Signed.addOverflow (encodeBool false) (encodeBool false) (encodeBool true) := by
  rw [Signed.add_overflow_sound_complete]
  decide

theorem signed_negative_overflow :
    ¬Signed.addOverflow (encodeBool true) (encodeBool true) (encodeBool false) := by
  rw [Signed.add_overflow_sound_complete]
  decide

theorem signed_subtraction_overflow :
    ¬Signed.subOverflow (encodeBool true) (encodeBool false) (encodeBool false) := by
  rw [Signed.sub_overflow_sound_complete]
  decide

theorem negative_interpretation : Signed.twos 128 128 = -128 := rfl

theorem honest_division : Bitcoin.divisionConstraint 100 7 14 2 := by
  unfold Bitcoin.divisionConstraint; decide
theorem wrong_quotient_rejected : ¬Bitcoin.divisionConstraint 100 7 13 2 := by
  unfold Bitcoin.divisionConstraint; decide
theorem oversized_remainder_rejected : ¬Bitcoin.divisionConstraint 100 7 13 9 := by
  unfold Bitcoin.divisionConstraint; decide

theorem high_product_not_truncated : ¬Schoolbook.Columns [256] [0] 0 0 := by
  intro h
  have heq := Schoolbook.columns_equation h
  norm_num [Words.decode] at heq

theorem terminal_carry_is_necessary : Schoolbook.Columns [256] [0] 0 1 := by
  exact .cons (by unfold Schoolbook.columnConstraint; decide) (.nil (by decide))

theorem invalid_exponent_rejected : ¬∃ selectors, Bitcoin.exponentConstraint 33 selectors := by
  rw [Bitcoin.exponent_sound_complete]
  decide

theorem honest_exponent : ∃ selectors, Bitcoin.exponentConstraint 29 selectors :=
  Bitcoin.exponent_complete 29 (by decide) (by decide)

theorem digest_last_word : RiscvRefinement.M31.reduce (2^32 - 1) = 1 := by decide

theorem honest_field_hash_gate :
    Graph.Code.accepts (⟨[.apply .add [0,1]], [2]⟩ : Graph.Code M31 Graph.FieldOp)
      Hash.fieldPrimitive [RiscvRefinement.M31.reduce 2, RiscvRefinement.M31.reduce 3]
      [RiscvRefinement.M31.reduce 5] := by
  apply (Hash.field_schedule_sound_complete _ _ _).mpr
  rfl

theorem forged_field_hash_gate :
    ¬Graph.Code.accepts (⟨[.apply .add [0,1]], [2]⟩ : Graph.Code M31 Graph.FieldOp)
      Hash.fieldPrimitive [RiscvRefinement.M31.reduce 2, RiscvRefinement.M31.reduce 3]
      [RiscvRefinement.M31.reduce 6] := by
  rw [Hash.field_schedule_sound_complete]
  decide

/-- Valid schedules read only declared inputs or previously emitted gates. -/
theorem one_add_wires_valid :
    Graph.Code.WellFormedFor
      (⟨[.apply .add [0, 1]], [2]⟩ : Graph.Code M31 Graph.FieldOp)
      Graph.fieldArity 2 := by
  apply Graph.Code.check_sound
  decide

theorem forward_wire_check_rejects :
    (⟨[.apply .add [0, 7]], [1]⟩ : Graph.Code M31 Graph.FieldOp).check
      Graph.fieldArity 1 = false := by decide

theorem missing_operand_check_rejects :
    (⟨[.apply .add [0]], [1]⟩ : Graph.Code M31 Graph.FieldOp).check
      Graph.fieldArity 1 = false := by decide

theorem missing_add_operand_rejected :
    ¬Graph.Code.WellFormedFor
      (⟨[.apply .add [0]], [1]⟩ : Graph.Code M31 Graph.FieldOp)
      Graph.fieldArity 1 := by
  intro h
  have hgate := h.2 (Graph.Gate.apply Graph.FieldOp.add [0]) (by simp)
  simp [Graph.Gate.ArityValid, Graph.fieldArity] at hgate

/-- The old fallback interpreter can evaluate this schedule, but strict
acceptance rejects its out-of-range operand at wire 7. -/
theorem forward_wire_rejected :
    ¬Graph.Code.WellFormed
      (⟨[.apply .add [0, 7]], [1]⟩ : Graph.Code M31 Graph.FieldOp) 1 := by
  intro h
  rcases h with ⟨hg, _⟩
  cases hg with
  | cons hgate _ =>
    have hbad := hgate 7 (by decide)
    omega

/-- This counterexample documents why source-bound widths are a premise of
the public padding theorem. The assignment checker rejects a width change. -/
theorem padding_requires_widths : Bindings.pad8 [1] = Bindings.pad8 [1,0] := by decide

/-- A one-word private input is published only through the explicitly claimed
output. Both a changed witness and a changed output claim are rejected. -/
def privateBinding : Program := {
  name := "private_binding"
  inputs := [{ name := "x", shape := ⟨.m31, 1⟩, visibility := .private }]
  nodes := []
  assertions := []
  outputs := ["x"]
}

def honestPrivate : Assignment := {
  publicInputs := []
  privateInputs := [("x", [3])]
  publicOutputs := [("x", [3])]
}

theorem private_binding_honest :
    privateBinding.evaluate honestPrivate =
      .ok [RiscvRefinement.M31.reduce 3, 0, 0, 0, 0, 0, 0, 0] := by decide

theorem private_binding_forged_witness :
    privateBinding.evaluate {honestPrivate with privateInputs := [("x", [4])]} =
      .error .publicMismatch := by decide

theorem private_binding_forged_output :
    privateBinding.evaluate {honestPrivate with publicOutputs := [("x", [4])]} =
      .error .publicMismatch := by decide

/-- The second output is checked independently; matching the first does not
allow a false value for a later declared output. -/
def twoPrivateOutputs : Program := {
  name := "two_private_outputs"
  inputs := [
    { name := "x", shape := ⟨.m31, 1⟩, visibility := .private },
    { name := "y", shape := ⟨.m31, 1⟩, visibility := .private }]
  nodes := []
  assertions := []
  outputs := ["x", "y"]
}

def honestTwoOutputs : Assignment := {
  publicInputs := []
  privateInputs := [("x", [3]), ("y", [4])]
  publicOutputs := [("x", [3]), ("y", [4])]
}

theorem two_outputs_honest :
    twoPrivateOutputs.evaluate honestTwoOutputs =
      .ok [RiscvRefinement.M31.reduce 3, RiscvRefinement.M31.reduce 4,
        0, 0, 0, 0, 0, 0] := by decide

theorem two_outputs_each_bound :
    ∃ values, twoPrivateOutputs.environment honestTwoOutputs = .ok values ∧
      ∀ name ∈ twoPrivateOutputs.outputs,
        Bindings.OutputBound honestTwoOutputs values name :=
  Bindings.evaluate_ok_output_binding _ _ _ two_outputs_honest

theorem second_output_forged :
    twoPrivateOutputs.evaluate
      {honestTwoOutputs with publicOutputs := [("x", [3]), ("y", [5])]} =
      .error .publicMismatch := by decide

end S31.Evidence
