import S31.Semantics.Program
import S31.Gadgets.Field

namespace S31.Gadgets.Bindings

def values (env : Nat → M31) (wires : List Nat) : List M31 := wires.map env

theorem constant_wires (env : Nat → M31) (wire length : Nat) (value : M31)
    (h : env wire = value) :
    values env (List.replicate length wire) = List.replicate length value := by
  simp [values, h]

theorem cast_wire_identity (env : Nat → M31) (wires : List Nat) :
    values env wires = wires.map env := rfl

theorem array_get_wire (env : Nat → M31) (wires : List Nat) (i : Nat) (hi : i < wires.length) :
    values env [wires[i]] = [(values env wires)[i]'(by simp [values, hi])] := by
  simp [values]

theorem array_concat_wires (env : Nat → M31) (left right : List Nat) :
    values env (left ++ right) = values env left ++ values env right := by
  simp [values]

theorem array_slice_wires (env : Nat → M31) (wires : List Nat) (offset length : Nat) :
    values env ((wires.drop offset).take length) = ((values env wires).drop offset).take length := by
  simp [values, List.map_take, List.map_drop]

def assertion (a b : M31) : Prop := a - b = 0

theorem assertion_sound_complete (a b : M31) : assertion a b ↔ a = b :=
  RiscvRefinement.M31.sub_eq_zero_iff a b

def pad8 (words : List M31) : List M31 := words ++ List.replicate (8 - words.length) 0

theorem padding_length (words : List M31) (h : words.length ≤ 8) : (pad8 words).length = 8 := by
  simp only [pad8, List.length_append, List.length_replicate]
  omega

theorem padding_prefix (words : List M31) : (pad8 words).take words.length = words := by
  simp [pad8]

/-- Widths belong to the source-bound statement. Without the equal-width
premise, trailing zero padding would make [x] and [x,0] indistinguishable. -/
theorem padding_binding (xs ys : List M31) (hwidth : xs.length = ys.length) :
    pad8 xs = pad8 ys ↔ xs = ys := by
  constructor
  · intro h
    have heq := congrArg (List.take xs.length) h
    rw [padding_prefix] at heq
    rw [hwidth, padding_prefix] at heq
    exact heq
  · exact congrArg pad8

theorem segment_binding (xs ys left right : List M31) (hwidth : xs.length = ys.length) :
    xs ++ left = ys ++ right ↔ xs = ys ∧ left = right := by
  constructor
  · intro h; exact List.append_inj h hwidth
  · rintro ⟨rfl, rfl⟩; rfl

theorem proof_mode_validation (p : Program) (mode : ProofMode) :
    {p with proofMode := mode}.validate = p.validate := rfl

theorem proof_mode_claims (p : Program) (mode : ProofMode) (a : Assignment) :
    {p with proofMode := mode}.claimedWords a = p.claimedWords a := rfl

theorem proof_mode_environment (p : Program) (mode : ProofMode) (a : Assignment) :
    {p with proofMode := mode}.environment a = p.environment a := rfl

theorem proof_mode_semantics (p : Program) (mode : ProofMode) (a : Assignment) :
    {p with proofMode := mode}.evaluate a = p.evaluate a := rfl

/-- A private witness cannot change the eight-word public statement assembled
from the declared public inputs and outputs. -/
theorem claims_private_independent (p : Program) (a : Assignment) (privateValues : RawValues) :
    p.claimedWords {a with privateInputs := privateValues} = p.claimedWords a := rfl

/-- Changing the claimed outputs cannot change execution or its assertions. -/
theorem environment_claims_independent (p : Program) (a : Assignment) (outputs : RawValues) :
    p.environment {a with publicOutputs := outputs} = p.environment a := rfl

/-- The derived `BEq` on `Value` compares both the kind and every M31 word.
Making this implication explicit avoids silently treating a Boolean comparison
as mathematical equality in the public output theorem. -/
private theorem value_beq_eq (x y : Value) (h : (x == y) = true) : x = y := by
  cases x with
  | mk xk xw =>
    cases y with
    | mk yk yw =>
      change (xk == yk && xw == yw) = true at h
      have hp : (xk == yk) = true ∧ (xw == yw) = true := by
        simpa only [Bool.and_eq_true] using h
      rcases hp with ⟨hkbool, hwbool⟩
      have hw : xw = yw := (beq_iff_eq).mp hwbool
      have hk : xk = yk := by
        cases xk <;> cases yk
        · rfl
        · change false = true at hkbool; cases hkbool
        · change false = true at hkbool; cases hkbool
        · rfl
      simp [hk, hw]

/-- The claimed output parses to precisely the computed value, including its
kind and full width. -/
def OutputBound (a : Assignment) (values : Env) (name : String) : Prop :=
  ∃ actual, lookup values name = some actual ∧
    assigned a.publicOutputs name actual.shape = .ok actual

theorem outputsAgreeNames_sound (a : Assignment) (values : Env) (names : List String)
    (h : outputsAgreeNames a values names = .ok ()) :
    ∀ name ∈ names, OutputBound a values name := by
  induction names with
  | nil => simp
  | cons first rest ih =>
    cases hlookup : lookup values first with
    | none => simp [outputsAgreeNames, hlookup] at h
    | some actual =>
      cases hassigned : assigned a.publicOutputs first actual.shape with
      | error err => simp [outputsAgreeNames, hlookup, hassigned] at h
      | ok expected =>
        cases hbeq : actual == expected with
        | false => simp [outputsAgreeNames, hlookup, hassigned, hbeq] at h
        | true =>
          have htail : outputsAgreeNames a values rest = .ok () := by
            simpa [outputsAgreeNames, hlookup, hassigned, hbeq] using h
          intro name hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · refine ⟨actual, hlookup, ?_⟩
            simpa [value_beq_eq actual expected hbeq] using hassigned
          · exact ih htail name hrest

/-- A successful evaluation returns precisely the statement checked by the
assignment parser. The output comparison may reject a claim, but cannot
replace it with another value. -/
theorem evaluate_ok_claimed (p : Program) (a : Assignment) (words : List M31)
    (h : p.evaluate a = .ok words) : p.claimedWords a = .ok words := by
  cases henv : p.environment a with
  | error e =>
    simp only [Program.evaluate, henv] at h
    change Except.bind (Except.error e : Result Env) _ = .ok words at h
    simp [Except.bind] at h
  | ok env =>
    cases hc : p.claimedWords a with
    | error e =>
      simp only [Program.evaluate, henv, hc] at h
      change Except.bind (Except.ok env : Result Env) _ = .ok words at h
      simp [Except.bind] at h
      change Except.bind (Except.error e : Result (List M31)) _ = .ok words at h
      simp [Except.bind] at h
    | ok claimed =>
      cases ho : p.outputsAgree a env with
      | error e =>
        simp only [Program.evaluate, henv, hc] at h
        change Except.bind (Except.ok env : Result Env) _ = .ok words at h
        simp [Except.bind] at h
        change Except.bind (Except.ok claimed : Result (List M31)) _ = .ok words at h
        simp [Except.bind, ho] at h
      | ok u =>
        simp only [Program.evaluate, henv, hc] at h
        change Except.bind (Except.ok env : Result Env) _ = .ok words at h
        simp [Except.bind] at h
        change Except.bind (Except.ok claimed : Result (List M31)) _ = .ok words at h
        simp [Except.bind, ho] at h
        simp [h]

/-- A successful program run binds *each* declared public output to its
computed value; the claim list alone is not used as evidence of this fact. -/
theorem evaluate_ok_output_binding (p : Program) (a : Assignment) (words : List M31)
    (h : p.evaluate a = .ok words) :
    ∃ values, p.environment a = .ok values ∧
      ∀ name ∈ p.outputs, OutputBound a values name := by
  cases henv : p.environment a with
  | error err =>
    simp only [Program.evaluate, henv] at h
    change Except.bind (Except.error err : Result Env) _ = .ok words at h
    simp [Except.bind] at h
  | ok values =>
    cases hc : p.claimedWords a with
    | error err =>
      simp only [Program.evaluate, henv, hc] at h
      change Except.bind (Except.ok values : Result Env) _ = .ok words at h
      simp [Except.bind] at h
      change Except.bind (Except.error err : Result (List M31)) _ = .ok words at h
      simp [Except.bind] at h
    | ok claimed =>
      cases ho : p.outputsAgree a values with
      | error err =>
        simp only [Program.evaluate, henv, hc] at h
        change Except.bind (Except.ok values : Result Env) _ = .ok words at h
        simp [Except.bind] at h
        change Except.bind (Except.ok claimed : Result (List M31)) _ = .ok words at h
        simp [Except.bind, ho] at h
      | ok checked =>
        refine ⟨values, rfl, ?_⟩
        have hu : checked = () := Subsingleton.elim _ _
        rw [hu] at ho
        exact outputsAgreeNames_sound a values p.outputs
          (by simpa only [Program.outputsAgree] using ho)

/-- Two accepted private witnesses for the same public assignment have the
same public statement, even if they compute through different environments. -/
theorem successful_private_assignments_same_claim (p : Program) (a : Assignment)
    (privateValues : RawValues) (left right : List M31)
    (hl : p.evaluate a = .ok left)
    (hr : p.evaluate {a with privateInputs := privateValues} = .ok right) :
    left = right := by
  have hlc := evaluate_ok_claimed p a left hl
  have hrc := evaluate_ok_claimed p {a with privateInputs := privateValues} right hr
  rw [claims_private_independent] at hrc
  rw [hlc] at hrc
  exact Except.ok.inj hrc

end S31.Gadgets.Bindings
