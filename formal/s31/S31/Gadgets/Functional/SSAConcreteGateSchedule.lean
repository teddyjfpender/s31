import S31.Gadgets.Functional.SSAAirRows
import S31.Gadgets.Functional.SSANamedProgram

/-!
An exact, address-bearing refinement boundary for the bounded four-lane
add/pointwise-multiply source fragment. A native schedule has exactly one
semantic row for each checked SSA instruction, in source order. Every row
names the addresses of its operand and output wires, uses the selected opcode,
and carries values authenticated to the corresponding prior wires.

`NativeRow.matches` is a premise at this boundary: this file does not prove
that the Python package checker recognizes the native Zig emitter, nor that
LogUp and PCS establish the claimed address/value equalities. Those are
separate implementation and cryptographic obligations. Under the stated
premise, however, there is no unmodeled instruction row or free operand value,
and an accepted public output has exactly the source meaning.
-/

namespace S31.Functional.SSAConcreteGateSchedule

open S31.Functional.SSACertificate
open S31.Functional.SSAAirRows
open S31.Functional.SSANamedProgram
open S31.Gadgets.Air.Qm31Ops

structure NativeRow where
  in0Address : Nat
  in1Address : Nat
  outAddress : Nat
  multiply : Bool
  in0 : Lanes
  in1 : Lanes
  output : Lanes

/-- The wire-address list and wire-value list use the same positional SSA
index. Operand-value equalities are precisely where an authenticated Gate
lookup is needed in the real proof. -/
def NativeRow.matches (addresses : List Nat) (values : List Lanes)
    (instruction : Instruction) (row : NativeRow) : Prop :=
  addresses.length = values.length ∧
  instruction.id = values.length ∧
  addresses[instruction.lhs]? = some row.in0Address ∧
  addresses[instruction.rhs]? = some row.in1Address ∧
  row.outAddress ∉ addresses ∧
  row.multiply = instruction.multiply ∧
  values[instruction.lhs]? = some row.in0 ∧
  values[instruction.rhs]? = some row.in1 ∧
  accepts (encode (s31Op row.multiply))
    (packM31 row.in0) (packM31 row.in1) (packM31 row.output)

theorem NativeRow.matches_air (addresses : List Nat)
    (values : List Lanes) (instruction : Instruction) (row : NativeRow)
    (h : row.matches addresses values instruction) :
    acceptsRow values instruction row.output := by
  obtain ⟨_, hid, _, _, _, hop, hleft, hright, hair⟩ := h
  exact ⟨row.in0, row.in1, hid, hleft, hright, by simpa [hop] using hair⟩

/-- This consumes one and only one native semantic row per SSA instruction.
The final address list also records unique producer addresses. -/
inductive NativeRows : List Nat → List Lanes →
    List Instruction → List NativeRow → List Nat → List Lanes → Prop where
  | done (addresses : List Nat) (values : List Lanes) :
      NativeRows addresses values [] [] addresses values
  | next {addresses finalAddresses : List Nat}
      {values finalValues : List Lanes}
      {instruction : Instruction} {rest : List Instruction}
      {row : NativeRow} {rows : List NativeRow}
      (hmatch : row.matches addresses values instruction)
      (htail : NativeRows (addresses ++ [row.outAddress])
        (values ++ [row.output]) rest rows finalAddresses finalValues) :
      NativeRows addresses values (instruction :: rest) (row :: rows)
        finalAddresses finalValues

theorem NativeRows.to_air_trace {addresses finalAddresses : List Nat}
    {values finalValues : List Lanes}
    {instructions : List Instruction} {rows : List NativeRow}
    (h : NativeRows addresses values instructions rows
      finalAddresses finalValues) :
    AcceptsTrace values instructions finalValues := by
  induction h with
  | done _ values => exact .done values
  | next hmatch _ ih =>
      exact .next _ (NativeRow.matches_air _ _ _ _ hmatch) ih

theorem NativeRows.exact_length {addresses finalAddresses : List Nat}
    {values finalValues : List Lanes}
    {instructions : List Instruction} {rows : List NativeRow}
    (h : NativeRows addresses values instructions rows
      finalAddresses finalValues) :
    rows.length = instructions.length := by
  induction h with
  | done => rfl
  | next _ _ ih => simpa using congrArg Nat.succ ih

theorem NativeRows.fresh_addresses {addresses finalAddresses : List Nat}
    {values finalValues : List Lanes}
    {instructions : List Instruction} {rows : List NativeRow}
    (h : NativeRows addresses values instructions rows
      finalAddresses finalValues)
    (hinitial : addresses.Nodup) : finalAddresses.Nodup := by
  induction h with
  | done => exact hinitial
  | next hmatch _ ih =>
      obtain ⟨_, _, _, _, hfresh, _, _, _, _⟩ := hmatch
      apply ih
      apply List.nodup_append.mpr
      refine ⟨hinitial, by simp, ?_⟩
      intro address haddress other hother heq
      simp only [List.mem_singleton] at hother
      have hotherAddress := heq ▸ haddress
      exact hfresh (hother ▸ hotherAddress)

/-- The exact native row schedule commutes with the executable normalized
relation evaluator. The `NativeRows` premise supplies the authenticated
address/value join and the local AIR equations for every instruction. -/
theorem native_rows_normalized_output (certificate : Certificate)
    (input claimed : Lanes) (rows : List NativeRow)
    (finalAddresses : List Nat) (finalValues : List Lanes)
    (hnative : NativeRows [0] [input] certificate.instructions rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    executeNormalized certificate input = some claimed := by
  have hrun := accepted_trace_executes hnative.to_air_trace
  rw [execute_normalized_eq_execute]
  simpa [execute, hrun] using hclaim

/-- A checked source and exact native schedule cannot accept an incorrect
four-lane public result. This theorem covers the semantic source rows only;
packing, padding, lookup and proof verification remain explicit premises at
their own boundaries. -/
theorem native_rows_source_sound (source : Source 1)
    (certificate : Certificate) (input claimed : Lanes)
    (rows : List NativeRow) (finalAddresses : List Nat)
    (finalValues : List Lanes)
    (hcheck : check source certificate = some ())
    (hnative : NativeRows [0] [input] certificate.instructions rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  have hnativeOutput := native_rows_normalized_output certificate input
    claimed rows finalAddresses finalValues hnative hclaim
  have hsource := checked_certificate_normalized_sound source certificate
    input hcheck
  simpa [hnativeOutput] using hsource

/-- The same refinement for an independently checked canonical named S31
program. `checkNamed` includes normalized `Program.validate` and equality of
the full named node/output structure to the checked SSA serialization. -/
theorem native_rows_named_program_sound (source : Source 1)
    (certificate : Certificate) (program : S31.Program)
    (input claimed : Lanes) (rows : List NativeRow)
    (finalAddresses : List Nat) (finalValues : List Lanes)
    (hNamed : checkNamed source certificate program = some ())
    (hnative : NativeRows [0] [input] certificate.instructions rows
      finalAddresses finalValues)
    (hclaim : finalValues[certificate.output]? = some claimed) :
    claimed = source.value (fun _ => input) := by
  have hnativeOutput := native_rows_normalized_output certificate input
    claimed rows finalAddresses finalValues hnative hclaim
  have hsource := (checked_named_trace_sound source certificate program input
    hNamed).2.2
  simpa [hnativeOutput] using hsource

end S31.Functional.SSAConcreteGateSchedule
