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

/-- First matching node, with ID zero reserved for the public input. -/
def findKey (wanted : Key) : List Key → Option Nat
  | [] => none
  | first :: rest =>
      if first == wanted then some 1 else (findKey wanted rest).map Nat.succ

structure State where
  instructions : List Instruction := []
  keys : List Key := []
  sourceToCanonical : List Nat := [0]
deriving Repr

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
      some { state with sourceToCanonical := state.sourceToCanonical ++ [existing] }
  | none =>
      let id := state.instructions.length + 1
      let instruction : Instruction :=
        { id, lhs := orderedLhs, rhs := orderedRhs, multiply := raw.multiply }
      some { instructions := state.instructions ++ [instruction],
             keys := state.keys ++ [key],
             sourceToCanonical := state.sourceToCanonical ++ [id] }

/-- A bounded compact DAG for one-input SSA. The upper bound matches the
currently proved direct-gate text-byte fragment. -/
def optimize (raw : Certificate) : Option Certificate := do
  if raw.instructions.length > 16 then none else
  let state ← raw.instructions.foldlM step {}
  let output ← state.sourceToCanonical[raw.output]?
  return { instructions := state.instructions, output }

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
