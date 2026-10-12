import S31.Gadgets.Functional.SSAEmitterProof
import S31.Gadgets.Air.Qm31Ops

/-!
An abstract full-row refinement for the checked four-lane SSA fragment.
Every emitted add/multiply instruction contributes one packed QM31-operation
AIR row; row operands are resolved from prior wire values, and the selected
opcode is fixed by the instruction. This connects arbitrary nested compiled
terms to *all* their local arithmetic rows, beyond a final-row example.

The model assumes that a lookup join authenticates each row's operand reads
to those prior wires and that the native AIR implements `Qm31Ops.accepts`.
The current theorem is not a proof of Python emission, Zig row generation,
LogUp, PCS, or the installed verifier.
-/

namespace S31.Functional.SSAAirRows

open S31.Functional.SSACertificate
open S31.Functional.SSAEmitterProof
open S31.Gadgets.Air.Qm31Ops

/-- A witness for one complete packed arithmetic row, including resolved
operand addresses. The nine local polynomial residuals are represented by
`Qm31Ops.accepts`. -/
def acceptsRow (values : List Lanes) (instruction : Instruction)
    (output : Lanes) : Prop :=
  ∃ lhs rhs : Lanes,
    instruction.id = values.length ∧
    values[instruction.lhs]? = some lhs ∧
    values[instruction.rhs]? = some rhs ∧
    accepts (encode (s31Op instruction.multiply))
      (packM31 lhs) (packM31 rhs) (packM31 output)

theorem accepted_row_value (values : List Lanes) (instruction : Instruction)
    (output : Lanes) (h : acceptsRow values instruction output) :
    ∃ lhs rhs : Lanes,
      values[instruction.lhs]? = some lhs ∧
      values[instruction.rhs]? = some rhs ∧
      output = instructionValue instruction.multiply lhs rhs := by
  obtain ⟨lhs, rhs, _, hleft, hright, hair⟩ := h
  refine ⟨lhs, rhs, hleft, hright, ?_⟩
  have hlanes := (s31_row_iff instruction.multiply lhs rhs
    (packM31 output)).mp hair
  funext i
  apply S31.Field.toZMod_injective
  have hi := hlanes i
  rw [coord_packM31] at hi
  cases hmul : instruction.multiply <;>
    simpa [instructionValue, hmul] using hi

theorem accepted_row_executes (values : List Lanes)
    (instruction : Instruction) (output : Lanes)
    (h : acceptsRow values instruction output) :
    executeStep values instruction = some (values ++ [output]) := by
  have hvalue := accepted_row_value values instruction output h
  obtain ⟨_, _, hid, _, _, _⟩ := h
  obtain ⟨lhs, rhs, hleft, hright, houtput⟩ := hvalue
  simp [executeStep, hid, hleft, hright, houtput]

/-- The honest interpreter's output satisfies the nine modeled AIR equations
whenever the instruction's ID and operand references are valid. -/
theorem honest_row_accepted (values : List Lanes)
    (instruction : Instruction) (lhs rhs : Lanes)
    (hid : instruction.id = values.length)
    (hleft : values[instruction.lhs]? = some lhs)
    (hright : values[instruction.rhs]? = some rhs) :
    acceptsRow values instruction
      (instructionValue instruction.multiply lhs rhs) := by
  refine ⟨lhs, rhs, hid, hleft, hright, ?_⟩
  apply (s31_row_iff instruction.multiply lhs rhs
    (packM31 (instructionValue instruction.multiply lhs rhs))).mpr
  intro i
  rw [coord_packM31]
  cases instruction.multiply <;> rfl

/-- An AIR witness supplies one committed output for every instruction.
The resolved list of prior values stands for a successful Gate lookup join. -/
inductive AcceptsTrace : List Lanes → List Instruction → List Lanes → Prop where
  | done (values : List Lanes) : AcceptsTrace values [] values
  | next {values final : List Lanes}
      {instruction : Instruction} {rest : List Instruction}
      (output : Lanes)
      (hrow : acceptsRow values instruction output)
      (hrest : AcceptsTrace (values ++ [output]) rest final) :
      AcceptsTrace values (instruction :: rest) final

theorem accepted_trace_executes {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    instructions.foldlM executeStep initial = some final := by
  induction h with
  | done => rfl
  | next output hrow _ ih =>
      simp [List.foldlM_cons, accepted_row_executes _ _ _ hrow, ih]

/-- Every valid deterministic SSA execution has a corresponding list of
accepted local AIR rows. This is honest-witness completeness for the modeled
arithmetic rows, independently of lookup and proof serialization. -/
theorem executing_trace_has_air_rows (instructions : List Instruction)
    (initial final : List Lanes)
    (h : instructions.foldlM executeStep initial = some final) :
    AcceptsTrace initial instructions final := by
  induction instructions generalizing initial with
  | nil =>
      simp only [List.foldlM_nil] at h
      cases h
      exact .done _
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at h
      cases hid : instruction.id == initial.length with
      | false =>
          have hneq : instruction.id ≠ initial.length :=
            of_decide_eq_false hid
          simp [executeStep, hneq] at h
      | true =>
          have heq : instruction.id = initial.length :=
            of_decide_eq_true hid
          cases hleft : initial[instruction.lhs]? with
          | none => simp [executeStep, heq, hleft] at h
          | some lhs =>
              cases hright : initial[instruction.rhs]? with
              | none => simp [executeStep, heq, hleft, hright] at h
              | some rhs =>
                  let output := instructionValue instruction.multiply lhs rhs
                  have hstep : executeStep initial instruction =
                      some (initial ++ [output]) := by
                    simp [executeStep, heq, hleft, hright, output]
                  rw [hstep] at h
                  exact .next output
                    (honest_row_accepted initial instruction lhs rhs
                      heq hleft hright)
                    (ih (initial ++ [output]) h)

/-- For every source term in the fragment, all of its modeled AIR rows have
an honest witness and the claimed output is exactly the source value. -/
theorem compiled_source_air_complete (source : Source 1)
    (input : Lanes) :
    ∃ final : List Lanes,
      AcceptsTrace [input] (compile source).instructions final ∧
      final[(compile source).output]? =
        some (source.value (fun _ => input)) := by
  have hsource := compiled_normalized_sound source input
  rw [execute_normalized_eq_execute] at hsource
  unfold execute at hsource
  cases hrun : (compile source).instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hsource
  | some final =>
      refine ⟨final, executing_trace_has_air_rows _ _ _ hrun, ?_⟩
      simpa [hrun] using hsource

/-- An accepted arithmetic-row trace for a compiled source cannot claim a
different four-lane output, provided its operand list reflects the actual
addressed Gate values. -/
theorem compiled_source_air_sound (source : Source 1)
    (input claimed : Lanes) (final : List Lanes)
    (hrows : AcceptsTrace [input] (compile source).instructions final)
    (hclaim : final[(compile source).output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  have hrun := accepted_trace_executes hrows
  have hsource := compiled_normalized_sound source input
  rw [execute_normalized_eq_execute] at hsource
  simp [execute, hrun, hclaim] at hsource
  exact hsource

end S31.Functional.SSAAirRows
