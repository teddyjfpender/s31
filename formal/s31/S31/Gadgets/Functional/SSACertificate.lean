import S31.Gadgets.Functional.CompilerCorrespondence

/-!
A checker for an add/mul SSA certificate with one four-lane input. Wire 0 is
the input; instruction `id = k` produces wire k and may read only earlier
wires. The checker independently reconstructs the source expression, including
static `let` sharing, from the certificate. The theorem concerns this checked
positional SSA and its executable field interpreter. Correspondence to Python
serialization, Zig circuit building, and AIR column emission remains open.
-/

namespace S31.Functional.SSACertificate

open S31

abbrev Lanes := Fin 4 → M31

inductive Term where
  | input
  | add (left right : Term)
  | mul (left right : Term)
deriving DecidableEq, Repr

def Term.eval (input : Lanes) : Term → Lanes
  | .input => input
  | .add left right => fun i => left.eval input i + right.eval input i
  | .mul left right => fun i => left.eval input i * right.eval input i

/-- The source core uses de Bruijn variables so `let` binding and shadowing
are unambiguous. The initial context contains exactly the circuit input. -/
inductive Source : Nat → Type where
  | var {n : Nat} (index : Fin n) : Source n
  | add {n : Nat} (left right : Source n) : Source n
  | mul {n : Nat} (left right : Source n) : Source n
  | letValue {n : Nat} (value : Source n) (body : Source (n + 1)) : Source n

def Source.elaborate {n : Nat} (env : Fin n → Term) : Source n → Term
  | .var index => env index
  | .add left right => .add (left.elaborate env) (right.elaborate env)
  | .mul left right => .mul (left.elaborate env) (right.elaborate env)
  | .letValue value body =>
      body.elaborate (Fin.cons (value.elaborate env) env)

def Source.value {n : Nat} (env : Fin n → Lanes) : Source n → Lanes
  | .var index => env index
  | .add left right => fun i => left.value env i + right.value env i
  | .mul left right => fun i => left.value env i * right.value env i
  | .letValue value body =>
      body.value (Fin.cons (value.value env) env)

theorem Source.elaborate_eval {n : Nat} (source : Source n)
    (env : Fin n → Term) (input : Lanes) :
    (source.elaborate env).eval input =
      source.value (fun i => (env i).eval input) := by
  induction source with
  | var index => rfl
  | add left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· + ·) (congrFun (ihLeft env) i)
        (congrFun (ihRight env) i)
  | mul left right ihLeft ihRight =>
      funext i
      exact congrArg₂ (· * ·) (congrFun (ihLeft env) i)
        (congrFun (ihRight env) i)
  | letValue value body ihValue ihBody =>
      simp only [Source.elaborate, Source.value]
      rw [ihBody]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i
      · exact ihValue env
      · intro j
        rfl

structure Instruction where
  id : Nat
  lhs : Nat
  rhs : Nat
  multiply : Bool
deriving DecidableEq, Repr

structure Certificate where
  instructions : List Instruction
  output : Nat
deriving DecidableEq, Repr

def instructionTerm (multiply : Bool) (lhs rhs : Term) : Term :=
  if multiply then .mul lhs rhs else .add lhs rhs

def instructionValue (multiply : Bool) (lhs rhs : Lanes) : Lanes :=
  if multiply then (fun i => lhs i * rhs i)
  else (fun i => lhs i + rhs i)

/-- Exact next index enforces freshness; `get?` enforces backward references.
The returned list is the expanded source term for every named wire. -/
def checkStep (terms : List Term) (instruction : Instruction) :
    Option (List Term) := do
  if instruction.id != terms.length then none else
  let lhs ← terms[instruction.lhs]?
  let rhs ← terms[instruction.rhs]?
  return terms ++ [instructionTerm instruction.multiply lhs rhs]

/-- An independent field interpreter for the same positional SSA. -/
def executeStep (values : List Lanes) (instruction : Instruction) :
    Option (List Lanes) := do
  if instruction.id != values.length then none else
  let lhs ← values[instruction.lhs]?
  let rhs ← values[instruction.rhs]?
  return values ++ [instructionValue instruction.multiply lhs rhs]

/-- The same positional step, evaluated by the actual normalized S31 node
interpreter. Local operand names are supplied by `arithmeticEnv`; wire IDs and
edge validity are separately enforced by the certificate checker. -/
def executeNormalizedStep (values : List Lanes) (instruction : Instruction) :
    Option (List Lanes) := do
  if instruction.id != values.length then none else
  let lhs ← values[instruction.lhs]?
  let rhs ← values[instruction.rhs]?
  match evaluateNode (arithmeticEnv lhs rhs)
      (arithmeticNode instruction.multiply) with
  | .error _ => none
  | .ok result =>
      some (values ++ [fun i => result.words.getD i.val 0])

def check (source : Source 1) (certificate : Certificate) : Option Unit := do
  let terms ← certificate.instructions.foldlM checkStep [.input]
  let actual ← terms[certificate.output]?
  if actual == source.elaborate (fun _ => .input) then some () else none

def execute (certificate : Certificate) (input : Lanes) : Option Lanes := do
  let values ← certificate.instructions.foldlM executeStep [input]
  values[certificate.output]?

def executeNormalized (certificate : Certificate) (input : Lanes) :
    Option Lanes := do
  let values ← certificate.instructions.foldlM executeNormalizedStep [input]
  values[certificate.output]?

/-- A deterministic emitter for the source fragment. `let` evaluates its
value once and places that one wire ID in the body's variable environment. -/
def Source.emit {n : Nat} (env : Fin n → Nat)
    (prior : List Instruction) : Source n → List Instruction × Nat
  | .var index => (prior, env index)
  | .add left right =>
      let (afterLeft, lhs) := left.emit env prior
      let (afterRight, rhs) := right.emit env afterLeft
      let id := afterRight.length + 1
      (afterRight ++ [{ id, lhs, rhs, multiply := false }], id)
  | .mul left right =>
      let (afterLeft, lhs) := left.emit env prior
      let (afterRight, rhs) := right.emit env afterLeft
      let id := afterRight.length + 1
      (afterRight ++ [{ id, lhs, rhs, multiply := true }], id)
  | .letValue value body =>
      let (afterValue, id) := value.emit env prior
      body.emit (Fin.cons id env) afterValue

def compile (source : Source 1) : Certificate :=
  let (instructions, output) := source.emit (fun _ => 0) []
  { instructions, output }

theorem instruction_term_eval (multiply : Bool) (lhs rhs : Term)
    (input : Lanes) :
    (instructionTerm multiply lhs rhs).eval input =
      instructionValue multiply (lhs.eval input) (rhs.eval input) := by
  cases multiply <;> rfl

private theorem ofFn_getD (words : Fin 4 → M31) :
    (fun i : Fin 4 => (List.ofFn words).getD i.val 0) = words := by
  funext i
  fin_cases i <;> rfl

theorem normalized_step_eq_execute (values : List Lanes)
    (instruction : Instruction) :
    executeNormalizedStep values instruction = executeStep values instruction := by
  by_cases hid : instruction.id = values.length
  · simp only [executeNormalizedStep, executeStep, hid, ↓reduceIte]
    cases hleft : values[instruction.lhs]? with
    | none => simp [hleft]
    | some lhs =>
        cases hright : values[instruction.rhs]? with
        | none => simp [hleft, hright]
        | some rhs =>
            simp [hleft, hright, arithmeticNode_eval,
              instructionValue, ofFn_getD]
            funext i
            fin_cases i <;> cases instruction.multiply <;> rfl
  · simp [executeNormalizedStep, executeStep, hid]

theorem execute_normalized_eq_execute (certificate : Certificate)
    (input : Lanes) :
    executeNormalized certificate input = execute certificate input := by
  have hstep : executeNormalizedStep = executeStep := by
    funext values instruction
    exact normalized_step_eq_execute values instruction
  simp only [executeNormalized, execute, hstep]

/-- Checker and independent field interpreter agree after each instruction,
including their rejection of a nonfresh name or unavailable operand. -/
theorem execute_step_correct (terms : List Term)
    (instruction : Instruction) (input : Lanes) :
    executeStep (terms.map (Term.eval input)) instruction =
      (checkStep terms instruction).map
        (fun next => next.map (Term.eval input)) := by
  by_cases hid : instruction.id = terms.length
  · simp only [executeStep, checkStep, List.length_map,
      List.getElem?_map, hid, ↓reduceIte]
    cases hleft : terms[instruction.lhs]? with
    | none => simp [hleft]
    | some lhs =>
        cases hright : terms[instruction.rhs]? with
        | none => simp [hleft, hright]
        | some rhs =>
            simp [hleft, hright, List.map_append,
              instruction_term_eval]
  · simp [executeStep, checkStep, hid]

theorem execute_folds_correct (instructions : List Instruction)
    (terms : List Term) (input : Lanes) :
    instructions.foldlM executeStep (terms.map (Term.eval input)) =
      (instructions.foldlM checkStep terms).map
        (fun next => next.map (Term.eval input)) := by
  induction instructions generalizing terms with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.foldlM_cons]
      rw [execute_step_correct]
      cases hstep : checkStep terms instruction with
      | none => simp [hstep]
      | some next => simpa [hstep] using ih next

/-- Every accepted certificate has an executable field trace and its output
is the source value, for every possible four-lane input. -/
theorem checked_certificate_sound (source : Source 1)
    (certificate : Certificate) (input : Lanes)
    (hcheck : check source certificate = some ()) :
    execute certificate input =
      some (source.value (fun _ => input)) := by
  unfold check at hcheck
  cases hterms : certificate.instructions.foldlM checkStep [Term.input] with
  | none => simp [hterms] at hcheck
  | some terms =>
      cases hout : terms[certificate.output]? with
      | none => simp [hterms, hout] at hcheck
      | some term =>
          have hterm : term = source.elaborate (fun _ => Term.input) := by
            have hdec : (term == source.elaborate (fun _ => Term.input)) = true := by
              simpa [hterms, hout] using hcheck
            exact of_decide_eq_true hdec
          have hrun : certificate.instructions.foldlM executeStep [input] =
              some (terms.map (Term.eval input)) := by
            simpa [hterms] using
              execute_folds_correct certificate.instructions [Term.input] input
          simp [execute, hrun, List.getElem?_map, hout, hterm,
            Source.elaborate_eval, Term.eval]

/-- This version runs each accepted SSA instruction through `evaluateNode`,
the executable normalized S31 relation evaluator. -/
theorem checked_certificate_normalized_sound (source : Source 1)
    (certificate : Certificate) (input : Lanes)
    (hcheck : check source certificate = some ()) :
    executeNormalized certificate input =
      some (source.value (fun _ => input)) := by
  rw [execute_normalized_eq_execute]
  exact checked_certificate_sound source certificate input hcheck

/-- The source uses one multiplication to define `square`, then reuses that
wire twice. The certificate has exactly two multiplication instructions. -/
def sharedSquare : Source 1 :=
  .letValue (.mul (.var ⟨0, by decide⟩) (.var ⟨0, by decide⟩))
    (.mul (.var ⟨0, by decide⟩) (.var ⟨0, by decide⟩))

def sharedSquareCertificate : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 2, lhs := 1, rhs := 1, multiply := true }],
    output := 2 }

theorem shared_square_certificate_accepted :
    check sharedSquare sharedSquareCertificate = some () := by decide

theorem compile_shared_square :
    compile sharedSquare = sharedSquareCertificate := by decide

theorem compiled_shared_square_accepted :
    check sharedSquare (compile sharedSquare) = some () := by
  rw [compile_shared_square]
  exact shared_square_certificate_accepted

theorem shared_square_certificate_value (input : Lanes) :
    execute sharedSquareCertificate input =
      some (fun i => (input i * input i) * (input i * input i)) := by
  rw [checked_certificate_sound sharedSquare sharedSquareCertificate input
    shared_square_certificate_accepted]
  rfl

def wrongOperand : Certificate :=
  { sharedSquareCertificate with instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 2, lhs := 0, rhs := 1, multiply := true }] }

def wrongOutput : Certificate :=
  { sharedSquareCertificate with output := 1 }

def duplicateName : Certificate :=
  { sharedSquareCertificate with instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 1, lhs := 1, rhs := 1, multiply := true }] }

def forwardReference : Certificate :=
  { sharedSquareCertificate with instructions :=
      [{ id := 1, lhs := 2, rhs := 0, multiply := true },
       { id := 2, lhs := 1, rhs := 1, multiply := true }] }

def missingOutput : Certificate :=
  { sharedSquareCertificate with output := 3 }

theorem malformed_certificates_rejected :
    check sharedSquare wrongOperand = none ∧
    check sharedSquare wrongOutput = none ∧
    check sharedSquare duplicateName = none ∧
    check sharedSquare forwardReference = none ∧
    check sharedSquare missingOutput = none := by decide

end S31.Functional.SSACertificate
