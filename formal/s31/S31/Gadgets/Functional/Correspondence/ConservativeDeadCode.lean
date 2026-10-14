import S31.Gadgets.Functional.Effects

/-!
A semantic model of the enum-triggered, conservative dead-code pass. Nodes
have positional SSA names. The only erasable constructors are total field
arithmetic; assertions and arbitrary partial/effectful operations are roots.

`SafeMask` states the obligations of a backward-liveness scan. The theorem
is about any mask satisfying those obligations, not a verification of the
Python scan, source parser, normalized JSON, Zig relation compiler, or PCS.
The fuelled evaluator gives both source and pruned graphs the same address
space: erasing a node leaves its ID empty, without renumbering later wires.
-/

namespace S31.Functional.Correspondence.ConservativeDeadCode

open S31.Functional

inductive Node where
  | input (index : Nat)
  | constant (value : M31)
  | add (lhs rhs : Nat)
  | sub (lhs rhs : Nat)
  | mul (lhs rhs : Nat)
  | addConst (lhs : Nat) (value : M31)
  | mulConst (lhs : Nat) (value : M31)
  | assertEq (lhs rhs : Nat)
  | effect (dependencies : List Nat) (run : List M31 → Option M31)

def Node.references : Node → List Nat
  | .input _ | .constant _ => []
  | .add lhs rhs | .sub lhs rhs | .mul lhs rhs | .assertEq lhs rhs => [lhs, rhs]
  | .addConst lhs _ | .mulConst lhs _ => [lhs]
  | .effect dependencies _ => dependencies

/-- This is deliberately the Python pass's narrow allowlist. In particular,
`assertEq` and `effect` remain observable even when their result is unused. -/
def Node.erasable : Node → Bool
  | .constant _ | .add _ _ | .sub _ _ | .mul _ _ | .addConst _ _ | .mulConst _ _ => true
  | _ => false

def Node.apply (inputs : Nat → M31) : Node → List M31 → Option M31
  | .input index, _ => some (inputs index)
  | .constant value, _ => some value
  | .add _ _, [lhs, rhs] => some (lhs + rhs)
  | .sub _ _, [lhs, rhs] => some (lhs - rhs)
  | .mul _ _, [lhs, rhs] => some (lhs * rhs)
  | .addConst _ value, [lhs] => some (lhs + value)
  | .mulConst _ value, [lhs] => some (lhs * value)
  | .assertEq _ _, [lhs, rhs] => if lhs == rhs then some 0 else none
  | .effect _ run, values => run values
  | _, _ => none

def readAll (lookup : Nat → Option M31) : List Nat → Option (List M31)
  | [] => some []
  | index :: rest => do
      let value ← lookup index
      let values ← readAll lookup rest
      pure (value :: values)

private theorem readAll_congr (references : List Nat)
    (lhs rhs : Nat → Option M31)
    (hagrees : ∀ index ∈ references, lhs index = rhs index) :
    readAll lhs references = readAll rhs references := by
  induction references with
  | nil => rfl
  | cons index rest ih =>
      have hhead := hagrees index (by simp)
      have htail : ∀ item ∈ rest, lhs item = rhs item := by
        intro item hmem
        exact hagrees item (by simp [hmem])
      simp [readAll, hhead, ih htail]

/-- A failed assertion or partial operation returns `none`. The model
intentionally does not claim native AIR rows implement this evaluator. -/
def evalAt (program : Nat → Option Node) (inputs : Nat → M31) :
    Nat → Nat → Option M31
  | 0, _ => none
  | fuel + 1, index => do
      let node ← program index
      let values ← readAll (evalAt program inputs fuel) node.references
      node.apply inputs values

def erased (program : Nat → Option Node) (keep : Nat → Bool) :
    Nat → Option Node :=
  fun index => if keep index then program index else none

/-- Conditions a conservative reverse liveness scan must establish.

`outputs` includes all public output and public ABI leaf wires. `observed`
contains assertion node IDs. All other non-erasable nodes are retained even
if they are not named in either list. `dependencies` is the backward closure.
No claim is made that an arbitrary mask satisfies these conditions. -/
structure SafeMask (program : Nat → Option Node)
    (keep : Nat → Bool) (outputs observed : List Nat) : Prop where
  outputsKept : ∀ index ∈ outputs, keep index = true
  observedKept : ∀ index ∈ observed, keep index = true
  effectsKept : ∀ index node, program index = some node →
    node.erasable = false → keep index = true
  dependencies : ∀ index node, keep index = true →
    program index = some node →
    ∀ dependency ∈ node.references, keep dependency = true

/-- The mathematical backward-liveness closure: public/ABI leaves and
assertions are roots, every non-erasable operation is a root, and every
dependency of a live node is live. This is a specification of the scanner,
not a proof that the Python implementation computes this least closure. -/
inductive Needed (program : Nat → Option Node)
    (outputs observed : List Nat) : Nat → Prop where
  | output (index : Nat) : index ∈ outputs → Needed program outputs observed index
  | observation (index : Nat) :
      index ∈ observed → Needed program outputs observed index
  | effect (index : Nat) (node : Node) :
      program index = some node → node.erasable = false →
      Needed program outputs observed index
  | dependency (index dependency : Nat) (node : Node) :
      Needed program outputs observed index →
      program index = some node → dependency ∈ node.references →
      Needed program outputs observed dependency

noncomputable def reachableMask (program : Nat → Option Node)
    (outputs observed : List Nat) (index : Nat) : Bool :=
  by classical exact decide (Needed program outputs observed index)

theorem reachableMask_safe (program : Nat → Option Node)
    (outputs observed : List Nat) :
    SafeMask program (reachableMask program outputs observed)
      outputs observed := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro index hmember
    simp [reachableMask, Needed.output index hmember]
  · intro index hmember
    simp [reachableMask, Needed.observation index hmember]
  · intro index node hnode heffect
    simp [reachableMask, Needed.effect index node hnode heffect]
  · intro index node hkeep hnode dependency hmember
    have hneeded : Needed program outputs observed index := by
      simpa [reachableMask] using hkeep
    simp [reachableMask,
      Needed.dependency index dependency node hneeded hnode hmember]

/-- Every retained SSA result has exactly the same value or failure as in
the unpruned graph. The induction includes arbitrary partial operations;
the only thing required of them is that their dependencies agree. -/
theorem retained_value_eq (program : Nat → Option Node)
    (keep : Nat → Bool) (outputs observed : List Nat)
    (safe : SafeMask program keep outputs observed)
    (inputs : Nat → M31) (fuel : Nat) :
    ∀ index, keep index = true →
      evalAt (erased program keep) inputs fuel index =
        evalAt program inputs fuel index := by
  induction fuel with
  | zero =>
      intro index _
      rfl
  | succ prior inductionHypothesis =>
      intro index hkeep
      cases hnode : program index with
      | none => simp [evalAt, erased, hkeep, hnode]
      | some node =>
          have hreferences :
              readAll (evalAt (erased program keep) inputs prior)
                  node.references =
                readAll (evalAt program inputs prior) node.references := by
            apply readAll_congr
            intro dependency hmember
            exact inductionHypothesis dependency
              (safe.dependencies index node hkeep hnode dependency hmember)
          simp [evalAt, erased, hkeep, hnode, hreferences]

/-- Public outputs and assertion observations agree for every input and
every evaluation depth. Equality includes failure (`none`). -/
theorem observations_eq (program : Nat → Option Node)
    (keep : Nat → Bool) (outputs observed : List Nat)
    (safe : SafeMask program keep outputs observed)
    (inputs : Nat → M31) (fuel : Nat) :
    (outputs.map (evalAt (erased program keep) inputs fuel),
      observed.map (evalAt (erased program keep) inputs fuel)) =
    (outputs.map (evalAt program inputs fuel),
      observed.map (evalAt program inputs fuel)) := by
  have hvalue := retained_value_eq program keep outputs observed safe inputs fuel
  congr 1
  · apply List.map_congr_left
    intro index hmember
    exact hvalue index (safe.outputsKept index hmember)
  · apply List.map_congr_left
    intro index hmember
    exact hvalue index (safe.observedKept index hmember)

/-- The equality also covers each non-erasable node, including partial
checks and calls whose result is not a public output. -/
theorem effect_value_eq (program : Nat → Option Node)
    (keep : Nat → Bool) (outputs observed : List Nat)
    (safe : SafeMask program keep outputs observed)
    (inputs : Nat → M31) (fuel index : Nat) (node : Node)
    (hnode : program index = some node)
    (heffect : node.erasable = false) :
    evalAt (erased program keep) inputs fuel index =
      evalAt program inputs fuel index :=
  retained_value_eq program keep outputs observed safe inputs fuel index
    (safe.effectsKept index node hnode heffect)

/-- Semantic preservation for the least backward-liveness specification.
This statement quantifies over all inputs and fuel depths. -/
theorem reachable_pruning_observations_eq
    (program : Nat → Option Node) (outputs observed : List Nat)
    (inputs : Nat → M31) (fuel : Nat) :
    (outputs.map (evalAt
        (erased program (reachableMask program outputs observed)) inputs fuel),
      observed.map (evalAt
        (erased program (reachableMask program outputs observed)) inputs fuel)) =
    (outputs.map (evalAt program inputs fuel),
      observed.map (evalAt program inputs fuel)) :=
  observations_eq program (reachableMask program outputs observed)
    outputs observed (reachableMask_safe program outputs observed) inputs fuel

end S31.Functional.Correspondence.ConservativeDeadCode
