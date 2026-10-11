import S31.Gadgets.Functional.SSATextBytes

/-!
The four-lane M31 add/mul fragment of Zig `canonical.build` sorts the two
canonical operand IDs and reuses the first node with the same operation and
operands. This module implements that transformation over positional SSA.

`optimizeChecked` additionally compares independently expanded source and
compact terms using a decidable commutative-equivalence checker. Acceptance
therefore has a universal semantic theorem, even if the transformation code
is later changed. This is a bounded source-language fragment, not a proof of
Zig serialization, its SHA-256 digest, or native AIR emission.
-/

namespace S31.Functional.Correspondence.CanonicalDagOptimization

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes

private theorem m31_add_comm (a b : M31) : a + b = b + a := by
  change RiscvRefinement.M31.reduce (a.val + b.val) =
    RiscvRefinement.M31.reduce (b.val + a.val)
  rw [Nat.add_comm]

private theorem m31_mul_comm (a b : M31) : a * b = b * a := by
  change RiscvRefinement.M31.reduce (a.val * b.val) =
    RiscvRefinement.M31.reduce (b.val * a.val)
  rw [Nat.mul_comm]

/-- Structural equality up to swapping the children of add/mul nodes. The
checker deliberately does not claim associativity or distributivity. -/
def equivalent : Term → Term → Bool
  | .input, .input => true
  | .add a b, .add c d =>
      (equivalent a c && equivalent b d) ||
        (equivalent a d && equivalent b c)
  | .mul a b, .mul c d =>
      (equivalent a c && equivalent b d) ||
        (equivalent a d && equivalent b c)
  | _, _ => false

theorem equivalent_refl (term : Term) : equivalent term term = true := by
  induction term with
  | input => rfl
  | add left right ihLeft ihRight =>
      simp [equivalent, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp [equivalent, ihLeft, ihRight]

theorem equivalent_instruction (multiply : Bool) {a b c d : Term}
    (hac : equivalent a c = true) (hbd : equivalent b d = true) :
    equivalent (instructionTerm multiply a b)
      (instructionTerm multiply c d) = true := by
  cases multiply <;> simp [instructionTerm, equivalent, hac, hbd]

theorem equivalent_instruction_swap (multiply : Bool) {a b c d : Term}
    (had : equivalent a d = true) (hbc : equivalent b c = true) :
    equivalent (instructionTerm multiply a b)
      (instructionTerm multiply c d) = true := by
  cases multiply <;> simp [instructionTerm, equivalent, had, hbc]

theorem equivalent_sound {a b : Term} (h : equivalent a b = true)
    (input : Lanes) : a.eval input = b.eval input := by
  induction a generalizing b with
  | input =>
      cases b <;> simp [equivalent] at h ⊢
  | add left right ihLeft ihRight =>
      cases b with
      | input => simp [equivalent] at h
      | mul _ _ => simp [equivalent] at h
      | add c d =>
          simp only [equivalent, Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · funext i
            exact congrArg₂ (· + ·) (congrFun (ihLeft hl) i)
              (congrFun (ihRight hr) i)
          · funext i
            calc
              left.eval input i + right.eval input i =
                  d.eval input i + c.eval input i :=
                    congrArg₂ (· + ·) (congrFun (ihLeft hl) i)
                      (congrFun (ihRight hr) i)
              _ = c.eval input i + d.eval input i := m31_add_comm _ _
  | mul left right ihLeft ihRight =>
      cases b with
      | input => simp [equivalent] at h
      | add _ _ => simp [equivalent] at h
      | mul c d =>
          simp only [equivalent, Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · funext i
            exact congrArg₂ (· * ·) (congrFun (ihLeft hl) i)
              (congrFun (ihRight hr) i)
          · funext i
            calc
              left.eval input i * right.eval input i =
                  d.eval input i * c.eval input i :=
                    congrArg₂ (· * ·) (congrFun (ihLeft hl) i)
                      (congrFun (ihRight hr) i)
              _ = c.eval input i * d.eval input i := m31_mul_comm _ _

/-- The key has exactly the operation and ordered canonical operand IDs used
for add/mul expression sharing in `canonical.build`. -/
abbrev Key := Bool × Nat × Nat

/-- Zero-based index of the first matching arithmetic node. -/
def findKey (wanted : Key) : List Key → Option Nat
  | [] => none
  | first :: rest =>
      if first == wanted then some 0 else (findKey wanted rest).map Nat.succ

theorem findKey_sound (wanted : Key) (keys : List Key) (id : Nat)
    (h : findKey wanted keys = some id) :
    keys[id]? = some wanted := by
  induction keys generalizing id with
  | nil => simp [findKey] at h
  | cons first rest ih =>
      by_cases hfirst : first = wanted
      · have hid : id = 0 := by simpa [findKey, hfirst] using h.symm
        subst id
        simp [hfirst]
      · have htail : (findKey wanted rest).map Nat.succ = some id := by
          simpa [findKey, hfirst] using h
        cases hlookup : findKey wanted rest with
        | none => simp [hlookup] at htail
        | some prior =>
            have hid : id = prior + 1 := by simpa [hlookup] using htail.symm
            subst id
            simpa using ih prior hlookup

structure State where
  instructions : List Instruction := []
  keys : List Key := []
  sourceToCanonical : List Nat := [0]
deriving Repr

def keyOf (instruction : Instruction) : Key :=
  (instruction.multiply, instruction.lhs, instruction.rhs)

def State.keysMatchInstructions (state : State) : Prop :=
  state.keys = state.instructions.map keyOf

theorem found_existing_instruction (state : State) (wanted : Key)
    (index : Nat) (hvalid : state.keysMatchInstructions)
    (hfind : findKey wanted state.keys = some index) :
    ∃ instruction, state.instructions[index]? = some instruction ∧
      keyOf instruction = wanted := by
  have hkey := findKey_sound wanted state.keys index hfind
  rw [hvalid, List.getElem?_map] at hkey
  cases hlookup : state.instructions[index]? with
  | none => simp [hlookup] at hkey
  | some instruction =>
      have hsame : keyOf instruction = wanted := by
        simpa [hlookup] using hkey
      exact ⟨instruction, rfl, hsame⟩

/-- One source instruction is translated after its earlier operands have
already been mapped. A repeated key aliases its existing canonical node. -/
def step (state : State) (raw : Instruction) : Option State := do
  if raw.id != state.sourceToCanonical.length then none else
  let lhs ← state.sourceToCanonical[raw.lhs]?
  let rhs ← state.sourceToCanonical[raw.rhs]?
  let orderedLhs := min lhs rhs
  let orderedRhs := max lhs rhs
  let key : Key := (raw.multiply, orderedLhs, orderedRhs)
  match findKey key state.keys with
  | some existing =>
      some { state with sourceToCanonical := state.sourceToCanonical ++ [existing + 1] }
  | none =>
      let id := state.instructions.length + 1
      let instruction : Instruction :=
        { id, lhs := orderedLhs, rhs := orderedRhs, multiply := raw.multiply }
      some { instructions := state.instructions ++ [instruction],
             keys := state.keys ++ [key],
             sourceToCanonical := state.sourceToCanonical ++ [id] }

theorem step_keys_match (state next : State) (raw : Instruction)
    (hvalid : state.keysMatchInstructions)
    (hstep : step state raw = some next) :
    next.keysMatchInstructions := by
  unfold step at hstep
  by_cases hid : raw.id = state.sourceToCanonical.length
  · cases hlhs : state.sourceToCanonical[raw.lhs]? with
    | none => simp [hid, hlhs] at hstep
    | some lhs =>
        cases hrhs : state.sourceToCanonical[raw.rhs]? with
        | none => simp [hid, hlhs, hrhs] at hstep
        | some rhs =>
            let key : Key := (raw.multiply, min lhs rhs, max lhs rhs)
            cases hfind : findKey key state.keys with
            | none =>
                have hnext : next =
                    { instructions := state.instructions ++
                        [{ id := state.instructions.length + 1,
                           lhs := min lhs rhs, rhs := max lhs rhs,
                           multiply := raw.multiply }],
                      keys := state.keys ++ [key],
                      sourceToCanonical := state.sourceToCanonical ++
                        [state.instructions.length + 1] } := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using hstep.symm
                subst next
                simpa [State.keysMatchInstructions, List.map_append,
                  keyOf, key] using hvalid
            | some existing =>
                have hnext : next =
                    { state with sourceToCanonical :=
                        state.sourceToCanonical ++ [existing + 1] } := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using hstep.symm
                subst next
                exact hvalid
  · simp [hid] at hstep

theorem step_source_length (state next : State) (raw : Instruction)
    (hstep : step state raw = some next) :
    next.sourceToCanonical.length = state.sourceToCanonical.length + 1 := by
  unfold step at hstep
  by_cases hid : raw.id = state.sourceToCanonical.length
  · cases hlhs : state.sourceToCanonical[raw.lhs]? with
    | none => simp [hid, hlhs] at hstep
    | some lhs =>
        cases hrhs : state.sourceToCanonical[raw.rhs]? with
        | none => simp [hid, hlhs, hrhs] at hstep
        | some rhs =>
            let key : Key := (raw.multiply, min lhs rhs, max lhs rhs)
            cases hfind : findKey key state.keys with
            | none =>
                have hnext : next.sourceToCanonical =
                    state.sourceToCanonical ++ [state.instructions.length + 1] := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using
                    congrArg (fun item => item.map State.sourceToCanonical) hstep.symm
                simp [hnext]
            | some existing =>
                have hnext : next.sourceToCanonical =
                    state.sourceToCanonical ++ [existing + 1] := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using
                    congrArg (fun item => item.map State.sourceToCanonical) hstep.symm
                simp [hnext]
  · simp [hid] at hstep

theorem step_exists (state : State) (raw : Instruction)
    (hid : raw.id = state.sourceToCanonical.length)
    (hlhs : raw.lhs < state.sourceToCanonical.length)
    (hrhs : raw.rhs < state.sourceToCanonical.length) :
    ∃ next, step state raw = some next := by
  have hleft : ∃ lhs, state.sourceToCanonical[raw.lhs]? = some lhs := by
    exact ⟨state.sourceToCanonical[raw.lhs]'hlhs, by simp⟩
  have hright : ∃ rhs, state.sourceToCanonical[raw.rhs]? = some rhs := by
    exact ⟨state.sourceToCanonical[raw.rhs]'hrhs, by simp⟩
  obtain ⟨lhs, hleft⟩ := hleft
  obtain ⟨rhs, hright⟩ := hright
  unfold step
  simp [hid, hleft, hright]
  cases findKey (raw.multiply, min lhs rhs, max lhs rhs) state.keys <;>
    simp

theorem fold_keys_match (instructions : List Instruction)
    (state next : State) (hvalid : state.keysMatchInstructions)
    (hfold : instructions.foldlM step state = some next) :
    next.keysMatchInstructions := by
  induction instructions generalizing state with
  | nil =>
      have hsame : state = next := by simpa using hfold
      subst next
      exact hvalid
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at hfold
      cases hstep : step state instruction with
      | none => simp [hstep] at hfold
      | some middle =>
          exact ih middle (step_keys_match state middle instruction hvalid hstep)
            (by simpa [hstep] using hfold)

theorem fold_source_length (instructions : List Instruction)
    (state next : State)
    (hfold : instructions.foldlM step state = some next) :
    next.sourceToCanonical.length =
      state.sourceToCanonical.length + instructions.length := by
  induction instructions generalizing state with
  | nil =>
      have hsame : state = next := by simpa using hfold
      subst next
      simp
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at hfold
      cases hstep : step state instruction with
      | none => simp [hstep] at hfold
      | some middle =>
          have htail := ih middle (by simpa [hstep] using hfold)
          have hhead := step_source_length state middle instruction hstep
          simp only [List.length_cons]
          omega

/-- Positional SSA well-formedness independent of any particular input. -/
def validScheduleFrom : Nat → List Instruction → Prop
  | _, [] => True
  | nextId, instruction :: rest =>
      instruction.id = nextId ∧
      instruction.lhs < nextId ∧ instruction.rhs < nextId ∧
      validScheduleFrom (nextId + 1) rest

theorem fold_exists_of_valid (instructions : List Instruction)
    (state : State)
    (hvalid : validScheduleFrom state.sourceToCanonical.length instructions) :
    ∃ final, instructions.foldlM step state = some final := by
  induction instructions generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons instruction rest ih =>
      obtain ⟨hid, hlhs, hrhs, hrest⟩ := hvalid
      obtain ⟨middle, hstep⟩ := step_exists state instruction hid hlhs hrhs
      have hlength := step_source_length state middle instruction hstep
      have hvalidRest :
          validScheduleFrom middle.sourceToCanonical.length rest := by
        simpa [hlength] using hrest
      obtain ⟨final, hfinal⟩ := ih middle hvalidRest
      exact ⟨final, by simp [List.foldlM_cons, hstep, hfinal]⟩

/-- A bounded compact DAG for one-input SSA. The upper bound matches the
currently proved direct-gate text-byte fragment. -/
def optimize (raw : Certificate) : Option Certificate := do
  if raw.instructions.length > 16 then none else
  let state ← raw.instructions.foldlM step {}
  let output ← state.sourceToCanonical[raw.output]?
  return { instructions := state.instructions, output }

def validCertificate (raw : Certificate) : Prop :=
  raw.instructions.length ≤ 16 ∧
  validScheduleFrom 1 raw.instructions ∧
  raw.output < raw.instructions.length + 1

/-- The structural optimizer is total for every bounded, fresh,
backward-referencing positional SSA with a bound output. -/
theorem optimize_exists_of_valid (raw : Certificate)
    (hvalid : validCertificate raw) :
    ∃ compact, optimize raw = some compact := by
  obtain ⟨hcount, hschedule, houtput⟩ := hvalid
  obtain ⟨state, hfold⟩ :=
    fold_exists_of_valid raw.instructions ({} : State) hschedule
  have hlength := fold_source_length raw.instructions ({} : State) state hfold
  have hbound : raw.output < state.sourceToCanonical.length := by
    simpa [hlength, Nat.add_comm] using houtput
  have hlookup : ∃ output, state.sourceToCanonical[raw.output]? = some output := by
    exact ⟨state.sourceToCanonical[raw.output]'hbound, by simp⟩
  obtain ⟨output, hlookup⟩ := hlookup
  unfold optimize
  have hsmall : ¬raw.instructions.length > 16 := by omega
  simp [hsmall, hfold, hlookup]

/-- Independently reconstruct both expanded expression trees. It fails
closed if either positional program is malformed or the optimizer changed
anything beyond commutative ordering and repeated subexpression sharing. -/
def audit (raw compact : Certificate) : Bool :=
  match termFor raw, termFor compact with
  | some sourceTerm, some compactTerm => equivalent sourceTerm compactTerm
  | _, _ => false

def optimizeChecked (raw : Certificate) : Option Certificate := do
  let compact ← optimize raw
  if audit raw compact then some compact else none

/-- Universal semantic preservation for every accepted optimized program and
every four-lane field input. This is independent of test vectors. -/
theorem audited_semantics (raw compact : Certificate) (input : Lanes)
    (h : audit raw compact = true) :
    executeNormalized raw input = executeNormalized compact input := by
  unfold audit at h
  cases hraw : termFor raw with
  | none => simp [hraw] at h
  | some sourceTerm =>
      cases hcompact : termFor compact with
      | none => simp [hraw, hcompact] at h
      | some compactTerm =>
          have heq : sourceTerm.eval input = compactTerm.eval input :=
            equivalent_sound (by simpa [hraw, hcompact] using h) input
          rw [termFor_sound raw sourceTerm input hraw,
            termFor_sound compact compactTerm input hcompact, heq]

theorem optimizeChecked_semantics (raw compact : Certificate) (input : Lanes)
    (h : optimizeChecked raw = some compact) :
    executeNormalized raw input = executeNormalized compact input := by
  unfold optimizeChecked at h
  cases hopt : optimize raw with
  | none => simp [hopt] at h
  | some produced =>
      by_cases haudit : audit raw produced = true
      · have hsame : produced = compact := by
          simpa [hopt, haudit] using h
        subst compact
        exact audited_semantics raw produced input haudit
      · simp [hopt, haudit] at h

/-- Reversed operands and duplicate results both collapse to the same node;
the two distinct first producers remain in dependency order. -/
def reversedAndRepeated : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := false },
       { id := 2, lhs := 0, rhs := 0, multiply := true },
       { id := 3, lhs := 1, rhs := 2, multiply := false },
       { id := 4, lhs := 2, rhs := 1, multiply := false }],
    output := 4 }

def compactExample : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := false },
       { id := 2, lhs := 0, rhs := 0, multiply := true },
       { id := 3, lhs := 1, rhs := 2, multiply := false }],
    output := 3 }

theorem reversed_and_repeated_collapses :
    optimizeChecked reversedAndRepeated = some compactExample := by decide

theorem reversed_and_repeated_semantics (input : Lanes) :
    executeNormalized reversedAndRepeated input =
      executeNormalized compactExample input := by
  exact optimizeChecked_semantics _ _ input reversed_and_repeated_collapses

/-- A changed operation cannot pass the independent symbolic audit. -/
def wrongCompact : Certificate :=
  { compactExample with instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := false },
       { id := 2, lhs := 0, rhs := 0, multiply := true },
       { id := 3, lhs := 1, rhs := 2, multiply := true }] }

theorem wrong_operation_rejected :
    audit reversedAndRepeated wrongCompact = false := by decide

def wrongOutput : Certificate := { compactExample with output := 2 }

theorem wrong_output_mapping_rejected :
    audit reversedAndRepeated wrongOutput = false := by decide

end S31.Functional.Correspondence.CanonicalDagOptimization
