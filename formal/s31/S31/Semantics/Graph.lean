import S31.Semantics.Words

namespace S31.Graph

/-- A straight-line schedule. Operand indices address the input prefix followed
by previously produced wires. Hash algorithms construct these schedules; the
constraint layer gives each primitive an independent relation on its witnesses. -/
inductive Gate (α : Type) (Op : Type) where
  | constant (value : α)
  | apply (op : Op) (args : List Nat)
deriving Repr

structure Code (α : Type) (Op : Type) where
  gates : List (Gate α Op)
  outputs : List Nat
deriving Repr

structure Builder (α : Type) (Op : Type) where
  inputCount : Nat
  gates : Array (Gate α Op) := #[]

abbrev Build (α : Type) (Op : Type) := StateM (Builder α Op)

variable {α : Type} {Op : Type}

def emit (g : Gate α Op) : Build α Op Nat := do
  let state ← get
  let index := state.inputCount + state.gates.size
  set { state with gates := state.gates.push g }
  return index

def literal (x : α) : Build α Op Nat := emit (.constant x)
def unary (op : Op) (x : Nat) : Build α Op Nat := emit (.apply op [x])
def binary (op : Op) (x y : Nat) : Build α Op Nat := emit (.apply op [x, y])

def build (inputs : Nat) (program : Build α Op (List Nat)) : Code α Op :=
  let (outputs, state) := program.run ⟨inputs, #[]⟩
  ⟨state.gates.toList, outputs⟩

def Gate.eval [Inhabited α] (interpret : Op → List α → α)
    (values : List α) : Gate α Op → α
  | .constant x => x
  | .apply op args => interpret op (args.map (values.getD · default))

def run [Inhabited α] (interpret : Op → List α → α) :
    List (Gate α Op) → List α → List α
  | [], values => values
  | gate :: gates, values => run interpret gates (values ++ [gate.eval interpret values])

def Code.eval [Inhabited α] (code : Code α Op)
    (interpret : Op → List α → α) (inputs : List α) : List α :=
  let values := run interpret code.gates inputs
  code.outputs.map (values.getD · default)

/-- Each gate may read inputs or previously emitted gates only. -/
def Gate.ValidAt (bound : Nat) : Gate α Op → Prop
  | .constant _ => True
  | .apply _ args => ∀ index ∈ args, index < bound

inductive GatesValid : Nat → List (Gate α Op) → Prop where
  | nil (bound : Nat) : GatesValid bound []
  | cons {bound gate gates} :
      gate.ValidAt bound → GatesValid (bound + 1) gates →
      GatesValid bound (gate :: gates)

/-- The complete schedule has no out-of-range wire reads, including outputs. -/
def Code.WellFormed (code : Code α Op) (inputCount : Nat) : Prop :=
  GatesValid inputCount code.gates ∧
    ∀ index ∈ code.outputs, index < inputCount + code.gates.length

/-- Primitive semantics may also read a default operand if called with too few
arguments. A valid circuit must supply the primitive's exact arity. -/
def Gate.ArityValid (arity : Op → Nat) : Gate α Op → Prop
  | .constant _ => True
  | .apply op args => args.length = arity op

def Code.WellFormedFor (code : Code α Op) (arity : Op → Nat)
    (inputCount : Nat) : Prop :=
  code.WellFormed inputCount ∧
    ∀ gate ∈ code.gates, gate.ArityValid arity

/-- Executable certificate checker for a gate schedule. The theorem below
connects its Boolean result to the logical circuit validity condition. -/
def Gate.check (arity : Op → Nat) (bound : Nat) : Gate α Op → Bool
  | .constant _ => true
  | .apply op args =>
      decide (args.length = arity op) && args.all (fun index => decide (index < bound))

def gatesCheck (arity : Op → Nat) : Nat → List (Gate α Op) → Bool
  | _, [] => true
  | bound, gate :: gates => gate.check arity bound && gatesCheck arity (bound + 1) gates

def Code.check (code : Code α Op) (arity : Op → Nat) (inputCount : Nat) : Bool :=
  gatesCheck arity inputCount code.gates &&
    code.outputs.all (fun index => decide (index < inputCount + code.gates.length))

theorem Gate.check_sound (arity : Op → Nat) (bound : Nat) (gate : Gate α Op)
    (h : gate.check arity bound = true) :
    gate.ValidAt bound ∧ gate.ArityValid arity := by
  cases gate with
  | constant _ => exact ⟨trivial, trivial⟩
  | apply op args =>
    simp only [Gate.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact ⟨(by simpa only [Gate.ValidAt, decide_eq_true_eq] using h.2),
      (by simpa only [Gate.ArityValid] using h.1)⟩

theorem gatesCheck_sound (arity : Op → Nat) (bound : Nat)
    (gates : List (Gate α Op)) (h : gatesCheck arity bound gates = true) :
    GatesValid bound gates ∧ ∀ gate ∈ gates, gate.ArityValid arity := by
  induction gates generalizing bound with
  | nil => exact ⟨.nil bound, by simp⟩
  | cons gate gates ih =>
    have hparts : gate.check arity bound = true ∧
        gatesCheck arity (bound + 1) gates = true := by
      simpa only [gatesCheck, Bool.and_eq_true] using h
    obtain ⟨hgate, harity⟩ := gate.check_sound arity bound hparts.1
    obtain ⟨htail, htailArity⟩ := ih (bound + 1) hparts.2
    constructor
    · exact .cons hgate htail
    · intro item member
      rcases List.mem_cons.mp member with rfl | hmember
      · exact harity
      · exact htailArity item hmember

theorem Code.check_sound (code : Code α Op) (arity : Op → Nat) (inputCount : Nat)
    (h : code.check arity inputCount = true) :
    code.WellFormedFor arity inputCount := by
  have hparts : gatesCheck arity inputCount code.gates = true ∧
      code.outputs.all (fun index => decide (index < inputCount + code.gates.length)) = true := by
    simpa only [Code.check, Bool.and_eq_true] using h
  obtain ⟨hgates, harity⟩ := gatesCheck_sound arity inputCount code.gates hparts.1
  refine ⟨⟨hgates, ?_⟩, harity⟩
  intro index member
  exact of_decide_eq_true ((List.all_eq_true.mp hparts.2) index member)

theorem run_length [Inhabited α] (interpret : Op → List α → α)
    (gates : List (Gate α Op)) (inputs : List α) :
    (run interpret gates inputs).length = inputs.length + gates.length := by
  induction gates generalizing inputs with
  | nil => simp [run]
  | cons gate gates ih =>
    simp only [run]
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm]

theorem Code.output_in_run [Inhabited α] (code : Code α Op)
    (interpret : Op → List α → α) (inputs : List α)
    (valid : code.WellFormed inputs.length)
    (index : Nat) (member : index ∈ code.outputs) :
    index < (run interpret code.gates inputs).length := by
  rw [run_length]
  exact valid.2 index member

inductive FieldOp where | add | mul
deriving DecidableEq, Repr

def fieldArity : FieldOp → Nat
  | .add | .mul => 2

instance : Inhabited M31 := ⟨RiscvRefinement.M31.zero⟩

def fieldEval (op : FieldOp) (args : List M31) : M31 :=
  let a := args.getD 0 0
  let b := args.getD 1 0
  match op with
  | .add => a + b
  | .mul => a * b

inductive WordOp where
  | add | xor | and | not
  | rotr (amount : Nat)
  | shr (amount : Nat)
deriving DecidableEq, Repr

def wordArity : WordOp → Nat
  | .add | .xor | .and => 2
  | .not | .rotr _ | .shr _ => 1

def wordEval (op : WordOp) (args : List Words.Word) : Words.Word :=
  let a := args.getD 0 0
  let b := args.getD 1 0
  match op with
  | .add => a + b
  | .xor => a ^^^ b
  | .and => a &&& b
  | .not => ~~~a
  | .rotr n => Words.rotr a n
  | .shr n => a >>> n

abbrev FieldBuild := Build M31 FieldOp
abbrev WordBuild := Build Words.Word WordOp

end S31.Graph
