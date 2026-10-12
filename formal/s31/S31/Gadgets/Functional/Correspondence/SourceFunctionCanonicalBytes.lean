import S31.Gadgets.Functional.Correspondence.SourceFunctionBytes

/-!
Exact compact legacy canonical IR bytes for the bounded named-function source
fragment. The native canonicalizer sorts the two operand IDs for add and mul;
it preserves their order for sub. This module models that choice and proves
that it does not change M31 semantics. Equality with a file is decidable and
does not assume the production Python or Zig implementations are correct.
-/

namespace S31.Functional.Correspondence.SourceFunctionCanonicalBytes

open S31.Functional.Correspondence.SourceFunctionBytes

abbrev Token := S31.Functional.SSATextBytes.Token
abbrev token := S31.Functional.SSATextBytes.token

private theorem m31_add_comm (a b : S31.M31) : a + b = b + a := by
  change RiscvRefinement.M31.reduce (a.val + b.val) =
    RiscvRefinement.M31.reduce (b.val + a.val)
  rw [Nat.add_comm]

private theorem m31_mul_comm (a b : S31.M31) : a * b = b * a := by
  change RiscvRefinement.M31.reduce (a.val * b.val) =
    RiscvRefinement.M31.reduce (b.val * a.val)
  rw [Nat.mul_comm]

def leftInputSecond (p : Parsed) : Bool :=
  choose p.bodyLeftSecond p.callFirstSecond p.callSecondSecond

def rightInputSecond (p : Parsed) : Bool :=
  choose p.bodyRightSecond p.callFirstSecond p.callSecondSecond

/-- On IDs 0 and 1, Boolean AND is minimum and OR is maximum. -/
def canonicalLeftSecond (p : Parsed) : Bool :=
  if p.op = .sub then leftInputSecond p
  else leftInputSecond p && rightInputSecond p

def canonicalRightSecond (p : Parsed) : Bool :=
  if p.op = .sub then rightInputSecond p
  else leftInputSecond p || rightInputSecond p

def inputId (second : Bool) : Token :=
  token (if second then "1" else "0")

def inputNode (name : Token) (length : Nat) : Token :=
  token "{\"tag\":\"input\",\"kind\":\"m31\",\"length\":" ++
  token (toString length) ++
  token ",\"lhs\":null,\"rhs\":null,\"constant\":null," ++
  token "\"rounds\":null,\"body\":null,\"input_name\":\"" ++ name ++
  token "\",\"visibility\":\"private\"}"

def gateNode (p : Parsed) : Token :=
  token "{\"tag\":\"" ++ p.op.name ++
  token "\",\"kind\":\"m31\",\"length\":" ++
  token (toString p.length) ++ token ",\"lhs\":" ++
  inputId (canonicalLeftSecond p) ++ token ",\"rhs\":" ++
  inputId (canonicalRightSecond p) ++
  token ",\"constant\":null,\"rounds\":null,\"body\":null," ++
  token "\"input_name\":null,\"visibility\":null}"

def encodeCanonical (p : Parsed) : Token :=
  token "{\"version\":1,\"nodes\":[" ++
  inputNode p.firstInput p.length ++ token "," ++
  inputNode p.secondInput p.length ++ token "," ++ gateNode p ++
  token "],\"assertions\":[],\"public_outputs\":[{\"name\":\"" ++
  p.outputName ++ token "\",\"id\":2}]}"

/-- Source, normalized relation, and compact canonical IR bytes must all
identify the same parsed one-gate circuit. -/
def checkCanonical (source normalized canonical : Token) : Option Parsed := do
  let p ← checkRelation source normalized
  if encodeCanonical p = canonical then some p else none

theorem checked_canonical_bytes (source normalized canonical : Token)
    (p : Parsed) (h : checkCanonical source normalized canonical = some p) :
    checkRelation source normalized = some p ∧
      encodeCanonical p = canonical := by
  unfold checkCanonical at h
  cases hr : checkRelation source normalized with
  | none => simp [hr] at h
  | some q =>
      by_cases hc : encodeCanonical q = canonical
      · simp [hr, hc] at h
        subst p
        exact ⟨rfl, hc⟩
      · simp [hr, hc] at h

/-- Evaluate the arithmetic gate with exactly the positional operands
written in the compact canonical IR. -/
def canonicalValue (p : Parsed)
    (a b : Fin p.length → S31.M31) : Fin p.length → S31.M31 :=
  fun i => p.op.eval
    (choose (canonicalLeftSecond p) a b i)
    (choose (canonicalRightSecond p) a b i)

/-- Sorting add and mul operands is semantically free; subtraction retains
its source operand order. -/
theorem canonicalValue_eq_relationValue (p : Parsed)
    (a b : Fin p.length → S31.M31) :
    canonicalValue p a b = p.relationValue a b := by
  rw [p.relationValue_eq_value a b]
  funext i
  cases hop : p.op <;>
    cases hleft : p.bodyLeftSecond <;>
    cases hright : p.bodyRightSecond <;>
    cases hfirst : p.callFirstSecond <;>
    cases hsecond : p.callSecondSecond <;>
    simp [canonicalValue, canonicalLeftSecond,
      canonicalRightSecond, leftInputSecond,
      rightInputSecond, Parsed.value, Parsed.left, Parsed.right,
      choose, Op.eval, hop, hleft, hright, hfirst, hsecond] <;>
      first | exact m31_add_comm _ _ | exact m31_mul_comm _ _

/-- Every satisfying packed row for a checked source/relation/IR triple
agrees with the positional gate represented by its compact canonical bytes. -/
theorem checked_canonical_air_iff (source normalized canonical : Token)
    (p : Parsed) (h : checkCanonical source normalized canonical = some p)
    (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    p.air a b claimed tailA tailB ↔
      encodeCanonical p = canonical ∧ claimed = canonicalValue p a b := by
  obtain ⟨hr, hc⟩ := checked_canonical_bytes source normalized canonical p h
  rw [air_iff_value]
  simp [hc, canonicalValue_eq_relationValue p a b,
    p.relationValue_eq_value a b]

end S31.Functional.Correspondence.SourceFunctionCanonicalBytes
