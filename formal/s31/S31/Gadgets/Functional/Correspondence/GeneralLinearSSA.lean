import S31.Gadgets.Functional.Correspondence.SourceFunctionBytes

/-!
General, shape-indexed linear SSA correspondence for the total M31 array
arithmetic fragment. Every instruction has a fresh positional ID, two prior
operands, and one of add/sub/mul. There may be any number of inputs, nodes,
lanes, and unused nodes. The checker reconstructs an independent source term
for the selected output. It rejects malformed references and a mismatched
source term. Theorems quantify over arbitrary witness values and arbitrary
inactive padding in every packed row.

This is the semantic kernel for the `linear-ssa-m31-v1` compiler artifact. It
does not parse S31 source text or JSON, authenticate the artifact, prove the
Python compiler equivalent to this kernel, or prove the PCS/FRI verifier.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSA

open S31
open S31.Functional.Correspondence.SourceFunctionBytes

abbrev Lanes (n : Nat) := Fin n → M31
abbrev ArithmeticOp := S31.Functional.Correspondence.SourceFunctionBytes.Op

inductive Term where
  | input (id : Nat)
  | binary (op : ArithmeticOp) (left right : Term)
deriving DecidableEq, Repr

def Term.eval {n : Nat} (inputs : Nat → Lanes n) : Term → Lanes n
  | .input id => inputs id
  | .binary op left right =>
      fun i => op.eval (left.eval inputs i) (right.eval inputs i)

structure Instruction where
  id : Nat
  lhs : Nat
  rhs : Nat
  op : ArithmeticOp
deriving DecidableEq, Repr

structure Certificate where
  inputs : Nat
  instructions : List Instruction
  output : Nat
deriving DecidableEq, Repr

def initialTerms (count : Nat) : List Term :=
  (List.range count).map Term.input

def checkStep (terms : List Term) (instruction : Instruction) :
    Option (List Term) := do
  if instruction.id != terms.length then none else
  let lhs ← terms[instruction.lhs]?
  let rhs ← terms[instruction.rhs]?
  return terms ++ [.binary instruction.op lhs rhs]

def check (certificate : Certificate) (source : Term) : Option Unit := do
  let terms ← certificate.instructions.foldlM checkStep
    (initialTerms certificate.inputs)
  let output ← terms[certificate.output]?
  if output = source then some () else none

def initialValues {n : Nat} (count : Nat) (inputs : Nat → Lanes n) :
    List (Lanes n) :=
  (List.range count).map inputs

def executeStep {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) : Option (List (Lanes n)) := do
  if instruction.id != values.length then none else
  let lhs ← values[instruction.lhs]?
  let rhs ← values[instruction.rhs]?
  return values ++ [fun i => instruction.op.eval (lhs i) (rhs i)]

def execute {n : Nat} (certificate : Certificate)
    (inputs : Nat → Lanes n) : Option (Lanes n) := do
  let values ← certificate.instructions.foldlM executeStep
    (initialValues certificate.inputs inputs)
  values[certificate.output]?

theorem execute_step_correct {n : Nat} (terms : List Term)
    (instruction : Instruction) (inputs : Nat → Lanes n) :
    executeStep (terms.map (Term.eval inputs)) instruction =
      (checkStep terms instruction).map
        (fun next => next.map (Term.eval inputs)) := by
  by_cases hid : instruction.id = terms.length
  · simp only [executeStep, checkStep, List.length_map,
      List.getElem?_map, hid]
    cases hleft : terms[instruction.lhs]? with
    | none => simp
    | some lhs =>
        cases hright : terms[instruction.rhs]? with
        | none => simp
        | some rhs =>
            simp [List.map_append, Term.eval]
  · simp [executeStep, checkStep, hid]

theorem execute_folds_correct {n : Nat}
    (instructions : List Instruction) (terms : List Term)
    (inputs : Nat → Lanes n) :
    instructions.foldlM executeStep (terms.map (Term.eval inputs)) =
      (instructions.foldlM checkStep terms).map
        (fun next => next.map (Term.eval inputs)) := by
  induction instructions generalizing terms with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.foldlM_cons]
      rw [execute_step_correct]
      cases hstep : checkStep terms instruction with
      | none => simp
      | some next => simpa [hstep] using ih next

/-- The independent checker and field interpreter agree for all admitted
graphs and all inputs. It is crucial that this holds for unused nodes too:
a malformed dangling instruction is rejected before the output is read. -/
theorem checked_execution {n : Nat} (certificate : Certificate)
    (source : Term) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ()) :
    execute certificate inputs = some (source.eval inputs) := by
  unfold check at hcheck
  cases hterms : certificate.instructions.foldlM checkStep
      (initialTerms certificate.inputs) with
  | none => simp [hterms] at hcheck
  | some terms =>
      cases hout : terms[certificate.output]? with
      | none => simp [hterms, hout] at hcheck
      | some term =>
          have hterm : term = source := by
            have hdec : (term == source) = true := by
              simpa [hterms, hout] using hcheck
            exact of_decide_eq_true hdec
          have hrun : certificate.instructions.foldlM executeStep
              (initialValues certificate.inputs inputs) =
                some (terms.map (Term.eval inputs)) := by
            have hinit : initialValues certificate.inputs inputs =
                (initialTerms certificate.inputs).map (Term.eval inputs) := by
              simp [initialValues, initialTerms, List.map_map,
                Function.comp_def, Term.eval]
            rw [hinit]
            simpa [hterms] using
              execute_folds_correct certificate.instructions
                (initialTerms certificate.inputs) inputs
          simp [execute, hrun, List.getElem?_map, hout, hterm]

/-- A modeled packed AIR row reads exactly the two prior values at its
encoded IDs and constrains all active lanes of its output. -/
def acceptsRow {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31) : Prop :=
  ∃ lhs rhs : Lanes n,
    instruction.id = values.length ∧
    values[instruction.lhs]? = some lhs ∧
    values[instruction.rhs]? = some rhs ∧
    instruction.op.packed lhs rhs output tailA tailB

/-- The very same operands and result satisfy the executable normalized
relation node. This relation includes the exact output kind and lane count. -/
def acceptsNode {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) (output : Lanes n) : Prop :=
  ∃ lhs rhs : Lanes n,
    instruction.id = values.length ∧
    values[instruction.lhs]? = some lhs ∧
    values[instruction.rhs]? = some rhs ∧
    evaluateNode (S31.Functional.arithmeticEnv lhs rhs)
      instruction.op.node = .ok ⟨.m31, List.ofFn output⟩

theorem row_iff_node {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31) :
    acceptsRow values instruction output tailA tailB ↔
      acceptsNode values instruction output := by
  constructor
  · rintro ⟨lhs, rhs, hid, hlhs, hrhs, hrow⟩
    exact ⟨lhs, rhs, hid, hlhs, hrhs,
      (packed_iff_node instruction.op lhs rhs output tailA tailB).mp hrow⟩
  · rintro ⟨lhs, rhs, hid, hlhs, hrhs, hnode⟩
    exact ⟨lhs, rhs, hid, hlhs, hrhs,
      (packed_iff_node instruction.op lhs rhs output tailA tailB).mpr hnode⟩

theorem accepted_row_executes {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31)
    (h : acceptsRow values instruction output tailA tailB) :
    executeStep values instruction = some (values ++ [output]) := by
  obtain ⟨lhs, rhs, hid, hlhs, hrhs, hrow⟩ := h
  have hvalue : output =
      (fun i => instruction.op.eval (lhs i) (rhs i)) := by
    funext i
    exact (packed_iff_eval instruction.op lhs rhs output tailA tailB).mp hrow i
  simp [executeStep, hid, hlhs, hrhs, hvalue]

theorem honest_row_accepted {n : Nat} (values : List (Lanes n))
    (instruction : Instruction) (lhs rhs : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31)
    (hid : instruction.id = values.length)
    (hlhs : values[instruction.lhs]? = some lhs)
    (hrhs : values[instruction.rhs]? = some rhs) :
    acceptsRow values instruction
      (fun i => instruction.op.eval (lhs i) (rhs i)) tailA tailB := by
  exact ⟨lhs, rhs, hid, hlhs, hrhs,
    (packed_iff_eval instruction.op lhs rhs _ tailA tailB).mpr
      (fun _ => rfl)⟩

inductive AcceptsTrace {n : Nat} :
    List (Lanes n) → List Instruction → List (Lanes n) → Prop where
  | done (values : List (Lanes n)) : AcceptsTrace values [] values
  | next {values final : List (Lanes n)}
      {instruction : Instruction} {rest : List Instruction}
      (output : Lanes n) (tailA tailB : Nat → Fin 4 → M31)
      (hrow : acceptsRow values instruction output tailA tailB)
      (hrest : AcceptsTrace (values ++ [output]) rest final) :
      AcceptsTrace values (instruction :: rest) final

/-- The graph-level normalized relation uses the same resolved prior-wire
reads, but runs the executable S31 `evaluateNode` at every instruction. -/
inductive AcceptsNormalizedTrace {n : Nat} :
    List (Lanes n) → List Instruction → List (Lanes n) → Prop where
  | done (values : List (Lanes n)) :
      AcceptsNormalizedTrace values [] values
  | next {values final : List (Lanes n)}
      {instruction : Instruction} {rest : List Instruction}
      (output : Lanes n)
      (hnode : acceptsNode values instruction output)
      (hrest : AcceptsNormalizedTrace (values ++ [output]) rest final) :
      AcceptsNormalizedTrace values (instruction :: rest) final

/-- All packed arithmetic rows and all normalized relation nodes accept the
same complete witness graph. The arbitrary inactive padding may be chosen
independently at every step. -/
theorem air_iff_normalized_trace {n : Nat}
    (initial final : List (Lanes n))
    (instructions : List Instruction) :
    AcceptsTrace initial instructions final ↔
      AcceptsNormalizedTrace initial instructions final := by
  constructor
  · intro h
    induction h with
    | done => exact .done _
    | next output tailA tailB hrow _ ih =>
        exact .next output
          ((row_iff_node _ _ output tailA tailB).mp hrow) ih
  · intro h
    induction h with
    | done => exact .done _
    | next output hnode _ ih =>
        exact .next output (fun _ _ => 0) (fun _ _ => 0)
          ((row_iff_node _ _ output (fun _ _ => 0)
            (fun _ _ => 0)).mpr hnode) ih

theorem accepted_trace_executes {n : Nat}
    {initial final : List (Lanes n)}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    instructions.foldlM executeStep initial = some final := by
  induction h with
  | done => rfl
  | next output tailA tailB hrow _ ih =>
      simp [List.foldlM_cons,
        accepted_row_executes _ _ output tailA tailB hrow, ih]

theorem executing_trace_has_air_rows {n : Nat}
    (instructions : List Instruction)
    (initial final : List (Lanes n))
    (h : instructions.foldlM executeStep initial = some final) :
    AcceptsTrace initial instructions final := by
  induction instructions generalizing initial with
  | nil =>
      simp only [List.foldlM_nil] at h
      cases h
      exact .done _
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at h
      by_cases hid : instruction.id = initial.length
      · cases hlhs : initial[instruction.lhs]? with
        | none => simp [executeStep, hid, hlhs] at h
        | some lhs =>
            cases hrhs : initial[instruction.rhs]? with
            | none => simp [executeStep, hid, hlhs, hrhs] at h
            | some rhs =>
                let output : Lanes n :=
                  fun i => instruction.op.eval (lhs i) (rhs i)
                have hstep : executeStep initial instruction =
                    some (initial ++ [output]) := by
                  simp [executeStep, hid, hlhs, hrhs, output]
                rw [hstep] at h
                exact .next output (fun _ _ => 0) (fun _ _ => 0)
                  (honest_row_accepted initial instruction lhs rhs
                    (fun _ _ => 0) (fun _ _ => 0) hid hlhs hrhs)
                  (ih (initial ++ [output]) h)
      · simp [executeStep, hid] at h

/-- A checked source graph cannot have an AIR-accepted output different from
its own denotation. This theorem has no fixed input, lane, or node budget. -/
theorem checked_air_sound {n : Nat} (certificate : Certificate)
    (source : Term) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hcheck : check certificate source = some ())
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval inputs := by
  have hrun := accepted_trace_executes hrows
  have hsource := checked_execution certificate source inputs hcheck
  simp [execute, hrun, houtput] at hsource
  exact hsource

/-- Every checked source graph has honest row witnesses for every instruction,
including unused instructions. -/
theorem checked_air_complete {n : Nat} (certificate : Certificate)
    (source : Term) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ()) :
    ∃ final : List (Lanes n),
      AcceptsTrace (initialValues certificate.inputs inputs)
        certificate.instructions final ∧
      final[certificate.output]? = some (source.eval inputs) := by
  have hsource := checked_execution certificate source inputs hcheck
  unfold execute at hsource
  cases hrun : certificate.instructions.foldlM executeStep
      (initialValues certificate.inputs inputs) with
  | none => simp [hrun] at hsource
  | some final =>
      refine ⟨final,
        executing_trace_has_air_rows _ _ _ hrun, ?_⟩
      simpa [hrun] using hsource

/-- For any admitted source graph, *complete* normalized-node acceptance
binds the selected output to its source term. -/
theorem checked_normalized_sound {n : Nat} (certificate : Certificate)
    (source : Term) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hcheck : check certificate source = some ())
    (hnodes : AcceptsNormalizedTrace
      (initialValues certificate.inputs inputs)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval inputs :=
  checked_air_sound certificate source inputs claimed final hcheck
    ((air_iff_normalized_trace _ _ _).mpr hnodes) houtput

theorem checked_normalized_complete {n : Nat} (certificate : Certificate)
    (source : Term) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ()) :
    ∃ final : List (Lanes n),
      AcceptsNormalizedTrace (initialValues certificate.inputs inputs)
        certificate.instructions final ∧
      final[certificate.output]? = some (source.eval inputs) := by
  obtain ⟨final, hrows, houtput⟩ :=
    checked_air_complete certificate source inputs hcheck
  exact ⟨final, (air_iff_normalized_trace _ _ _).mp hrows, houtput⟩

/-- Typed mirror of the emitted certificate's `ssa.inputs` entries. The
outer JSON parser and its exact-byte hash checks remain outside Lean. -/
structure EmittedInput where
  id : Nat
  name : String
  visibility : String
deriving DecidableEq, Repr

/-- Typed mirror of one emitted `ssa.nodes` entry in the binary-arithmetic
profile. Unsupported operations never decode to the kernel `Instruction`. -/
structure EmittedNode where
  id : Nat
  name : String
  op : String
  lhs : Nat
  rhs : Nat
deriving DecidableEq, Repr

/-- Exact data fields of the `ssa` part of
`s31-source-relation-certificate-v1` needed by this theorem. -/
structure EmittedSSA where
  lane_count : Nat
  inputs : List EmittedInput
  nodes : List EmittedNode
  assertions : List (Nat × Nat)
  output : Nat
deriving DecidableEq, Repr

def decodeOp : String → Option ArithmeticOp
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | _ => none

def EmittedNode.decode (node : EmittedNode) : Option Instruction := do
  let op ← decodeOp node.op
  return { id := node.id, lhs := node.lhs, rhs := node.rhs, op }

def EmittedSSA.names (ssa : EmittedSSA) : List String :=
  ssa.inputs.map EmittedInput.name ++ ssa.nodes.map EmittedNode.name

/-- Fail-closed decoding of the emitted arithmetic `ssa` shape. An assertion,
unknown opcode or visibility, nonconsecutive input ID, duplicate/empty name,
or zero lane count cannot enter this theorem's kernel. `check` below rejects
nonfresh node IDs, unavailable operands, and unavailable output IDs. -/
def EmittedSSA.decode (ssa : EmittedSSA) : Option Certificate := do
  if ssa.lane_count = 0 then none else
  if !ssa.assertions.isEmpty then none else
  if ssa.inputs.map EmittedInput.id != List.range ssa.inputs.length then none else
  if !ssa.names.Nodup || ssa.names.contains "" then none else
  if !ssa.inputs.all (fun input =>
      input.visibility == "private" || input.visibility == "public") then none else
  let instructions ← ssa.nodes.mapM EmittedNode.decode
  return { inputs := ssa.inputs.length, instructions := instructions, output := ssa.output }

/-- This is the Lean decision that a decoded emitted `ssa` graph has exactly
the independently supplied source term. It is conditional on the caller
presenting the same decoded data and source term as the actual package bytes. -/
def checkEmittedSSA (ssa : EmittedSSA) (source : Term) : Option Certificate := do
  let certificate ← ssa.decode
  check certificate source
  return certificate

theorem checked_emitted_certificate (ssa : EmittedSSA) (source : Term)
    (certificate : Certificate)
    (h : checkEmittedSSA ssa source = some certificate) :
    ssa.decode = some certificate ∧
    check certificate source = some () := by
  unfold checkEmittedSSA at h
  cases hdecode : ssa.decode with
  | none => simp [hdecode] at h
  | some decoded =>
      cases hcheck : check decoded source with
      | none => simp [hdecode, hcheck] at h
      | some value =>
          cases value
          have heq : decoded = certificate := by
            simpa [hdecode, hcheck] using h
          subst certificate
          exact ⟨rfl, hcheck⟩

/-- Concrete correspondence theorem for the `ssa` data shape emitted by
the compiler artifact: any complete accepted packed-row graph has the source
term's value at its selected output. -/
theorem emitted_ssa_air_sound (ssa : EmittedSSA) (source : Term)
    (certificate : Certificate)
    (inputs : Nat → Lanes ssa.lane_count)
    (claimed : Lanes ssa.lane_count)
    (final : List (Lanes ssa.lane_count))
    (hcheck : checkEmittedSSA ssa source = some certificate)
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval inputs :=
  checked_air_sound certificate source inputs claimed final
    (checked_emitted_certificate ssa source certificate hcheck).2
    hrows houtput

theorem emitted_ssa_air_complete (ssa : EmittedSSA) (source : Term)
    (certificate : Certificate)
    (inputs : Nat → Lanes ssa.lane_count)
    (hcheck : checkEmittedSSA ssa source = some certificate) :
    ∃ final : List (Lanes ssa.lane_count),
      AcceptsTrace (initialValues certificate.inputs inputs)
        certificate.instructions final ∧
      final[certificate.output]? = some (source.eval inputs) :=
  checked_air_complete certificate source inputs
    (checked_emitted_certificate ssa source certificate hcheck).2

/-- Two private five-lane inputs, a subtraction, then one reused subtraction
result added to itself. This matches the intended emitted certificate's ID
and operand convention; names and visibility are checked by the artifact
checker, not by this positional theorem. -/
def subtractionThenDouble : Certificate :=
  { inputs := 2,
    instructions :=
      [{ id := 2, lhs := 0, rhs := 1, op := .sub },
       { id := 3, lhs := 2, rhs := 2, op := .add }],
    output := 3 }

def subtractionThenDoubleSource : Term :=
  .binary .add
    (.binary .sub (.input 0) (.input 1))
    (.binary .sub (.input 0) (.input 1))

theorem subtraction_then_double_checked :
    check subtractionThenDouble subtractionThenDoubleSource = some () := by
  decide

def subtractionThenDoubleEmitted : EmittedSSA :=
  { lane_count := 5,
    inputs :=
      [{ id := 0, name := "a", visibility := "private" },
       { id := 1, name := "b", visibility := "private" }],
    nodes :=
      [{ id := 2, name := "delta", op := "sub", lhs := 0, rhs := 1 },
       { id := 3, name := "doubled", op := "add", lhs := 2, rhs := 2 }],
    assertions := [], output := 3 }

theorem emitted_subtraction_then_double_checked :
    checkEmittedSSA subtractionThenDoubleEmitted
      subtractionThenDoubleSource = some subtractionThenDouble := by
  decide

theorem emitted_assertion_rejected :
    checkEmittedSSA
      { subtractionThenDoubleEmitted with assertions := [(0, 1)] }
      subtractionThenDoubleSource = none := by
  decide

theorem emitted_unknown_opcode_rejected :
    checkEmittedSSA
      { subtractionThenDoubleEmitted with nodes :=
        [{ id := 2, name := "delta", op := "xor", lhs := 0, rhs := 1 },
         { id := 3, name := "doubled", op := "add", lhs := 2, rhs := 2 }] }
      subtractionThenDoubleSource = none := by
  decide

theorem wrong_selected_output_rejected :
    check { subtractionThenDouble with output := 2 }
      subtractionThenDoubleSource = none := by
  decide

theorem forward_reference_rejected :
    check { subtractionThenDouble with instructions :=
      [{ id := 2, lhs := 3, rhs := 1, op := .sub },
       { id := 3, lhs := 2, rhs := 2, op := .add }] }
      subtractionThenDoubleSource = none := by
  decide

theorem changed_subtraction_rejected :
    check { subtractionThenDouble with instructions :=
      [{ id := 2, lhs := 0, rhs := 1, op := .add },
       { id := 3, lhs := 2, rhs := 2, op := .add }] }
      subtractionThenDoubleSource = none := by
  decide

theorem subtraction_then_double_sound
    (a b claimed : Lanes 5) (final : List (Lanes 5))
    (hrows : AcceptsTrace [a, b]
      subtractionThenDouble.instructions final)
    (houtput : final[3]? = some claimed) :
    ∀ i : Fin 5, claimed i = (a i - b i) + (a i - b i) := by
  have h := checked_air_sound subtractionThenDouble
    subtractionThenDoubleSource (fun id => if id = 0 then a else b)
    claimed final subtraction_then_double_checked
    (by simpa [initialValues] using hrows) houtput
  intro i
  simpa [subtractionThenDoubleSource, Term.eval] using congrFun h i

end S31.Functional.Correspondence.GeneralLinearSSA
