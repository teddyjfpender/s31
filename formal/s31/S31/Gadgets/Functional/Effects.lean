import S31.Gadgets.Functional.Conditional

/-!
Why an eager fixed circuit needs total conditional branches. This small
semantic model includes a checked inverse: unlike field addition and
multiplication it has no result at zero. The decidable `isTotal` check is
deliberately conservative, matching the source compiler's rule that an
inverse is partial even when a particular argument happens to be nonzero.

This is a theorem about the effect rule, not a verification of the Python
effect checker or its transitive call analysis.
-/

namespace S31.Functional

open Graph

inductive EffectExpr (n : Nat) where
  | input : Fin n → EffectExpr n
  | literal : M31 → EffectExpr n
  | add : EffectExpr n → EffectExpr n → EffectExpr n
  | mul : EffectExpr n → EffectExpr n → EffectExpr n
  | checkedInverse : EffectExpr n → EffectExpr n

def EffectExpr.eval {n : Nat} (inputs : Fin n → M31) : EffectExpr n → Option M31
  | .input i => some (inputs i)
  | .literal x => some x
  | .add a b => do
      let x ← a.eval inputs
      let y ← b.eval inputs
      pure (x + y)
  | .mul a b => do
      let x ← a.eval inputs
      let y ← b.eval inputs
      pure (x * y)
  | .checkedInverse a => do
      let x ← a.eval inputs
      if x = 0 then none else some (Field.inverse x)

/-- A computable, value-independent effect check. `false` means the
expression may fail on a well-typed input, not that it always fails. -/
def EffectExpr.isTotal {n : Nat} : EffectExpr n → Bool
  | .input _ | .literal _ => true
  | .add a b | .mul a b => a.isTotal && b.isTotal
  | .checkedInverse _ => false

/-- Safe expressions lower to the same first-order residual polynomial used
by the strict graph theorem. An inverse has no polynomial lowering here. -/
def EffectExpr.toPoly? {n : Nat} : EffectExpr n → Option (Poly n)
  | .input i => some (.input i)
  | .literal x => some (.literal x)
  | .add a b => do
      let x ← a.toPoly?
      let y ← b.toPoly?
      pure (.add x y)
  | .mul a b => do
      let x ← a.toPoly?
      let y ← b.toPoly?
      pure (.mul x y)
  | .checkedInverse _ => none

theorem EffectExpr.total_has_value {n : Nat} (e : EffectExpr n)
    (inputs : Fin n → M31) (htotal : e.isTotal = true) :
    ∃ value, e.eval inputs = some value := by
  induction e with
  | input i => exact ⟨inputs i, rfl⟩
  | literal x => exact ⟨x, rfl⟩
  | add a b iha ihb =>
      have ⟨ha, hb⟩ : a.isTotal = true ∧ b.isTotal = true := by
        simpa [EffectExpr.isTotal] using htotal
      obtain ⟨x, hx⟩ := iha ha
      obtain ⟨y, hy⟩ := ihb hb
      exact ⟨x + y, by simp [EffectExpr.eval, hx, hy]⟩
  | mul a b iha ihb =>
      have ⟨ha, hb⟩ : a.isTotal = true ∧ b.isTotal = true := by
        simpa [EffectExpr.isTotal] using htotal
      obtain ⟨x, hx⟩ := iha ha
      obtain ⟨y, hy⟩ := ihb hb
      exact ⟨x * y, by simp [EffectExpr.eval, hx, hy]⟩
  | checkedInverse a _ =>
      cases htotal

/-- Every accepted expression has a residual polynomial with exactly the
same value on every input. The inverse case is impossible under `isTotal`. -/
theorem EffectExpr.total_to_poly {n : Nat} (e : EffectExpr n)
    (inputs : Fin n → M31) (htotal : e.isTotal = true) :
    ∃ poly, e.toPoly? = some poly ∧
      e.eval inputs = some (poly.eval inputs) := by
  induction e with
  | input i => exact ⟨.input i, rfl, rfl⟩
  | literal x => exact ⟨.literal x, rfl, rfl⟩
  | add a b iha ihb =>
      have ⟨ha, hb⟩ : a.isTotal = true ∧ b.isTotal = true := by
        simpa [EffectExpr.isTotal] using htotal
      obtain ⟨pa, hpa, hea⟩ := iha ha
      obtain ⟨pb, hpb, heb⟩ := ihb hb
      exact ⟨.add pa pb,
        by simp [EffectExpr.toPoly?, hpa, hpb],
        by simp [EffectExpr.eval, hea, heb, Poly.eval]⟩
  | mul a b iha ihb =>
      have ⟨ha, hb⟩ : a.isTotal = true ∧ b.isTotal = true := by
        simpa [EffectExpr.isTotal] using htotal
      obtain ⟨pa, hpa, hea⟩ := iha ha
      obtain ⟨pb, hpb, heb⟩ := ihb hb
      exact ⟨.mul pa pb,
        by simp [EffectExpr.toPoly?, hpa, hpb],
        by simp [EffectExpr.eval, hea, heb, Poly.eval]⟩
  | checkedInverse a _ =>
      cases htotal

/-- The computable effect check is sufficient to feed the existing strict
graph theorem: every satisfying auxiliary witness is bound to source
evaluation, and the honest value has a witness. -/
theorem EffectExpr.total_graph_accepts {n : Nat} (e : EffectExpr n)
    (inputs : List M31) (hinputs : inputs.length = n)
    (htotal : e.isTotal = true) :
    ∃ poly, e.toPoly? = some poly ∧
      ∀ output : M31,
        poly.code.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive
          inputs [output] ↔
        e.eval (fun i => inputs.getD i.val 0) = some output := by
  obtain ⟨poly, hpoly, heval⟩ := e.total_to_poly
    (fun i => inputs.getD i.val 0) htotal
  refine ⟨poly, hpoly, ?_⟩
  intro output
  rw [Poly.code_accepts poly inputs [output] hinputs, heval]
  simp [eq_comm]

/-- Ordinary `if` evaluates just the chosen branch. -/
def lazyIf {n : Nat} (choice : Bool) (onTrue onFalse : EffectExpr n)
    (inputs : Fin n → M31) : Option M31 :=
  if choice then onTrue.eval inputs else onFalse.eval inputs

/-- A fixed circuit must produce witnesses for both arms. The selector
relation is the same bit-constrained field selection used above. -/
def EagerIfAccepts {n : Nat} (choice : Bool) (onTrue onFalse : EffectExpr n)
    (inputs : Fin n → M31) (output : M31) : Prop :=
  ∃ trueValue falseValue,
    onTrue.eval inputs = some trueValue ∧
    onFalse.eval inputs = some falseValue ∧
    fieldSelect (if choice then 1 else 0) falseValue trueValue output

/-- For total branches, eager witness existence and ordinary lazy
conditional evaluation agree for every input and both selector values. -/
theorem eager_if_iff_lazy_if {n : Nat} (choice : Bool)
    (onTrue onFalse : EffectExpr n) (inputs : Fin n → M31)
    (output : M31) (htrue : onTrue.isTotal = true)
    (hfalse : onFalse.isTotal = true) :
    EagerIfAccepts choice onTrue onFalse inputs output ↔
      lazyIf choice onTrue onFalse inputs = some output := by
  obtain ⟨trueValue, ht⟩ := onTrue.total_has_value inputs htrue
  obtain ⟨falseValue, hf⟩ := onFalse.total_has_value inputs hfalse
  cases choice with
  | false =>
      constructor
      · rintro ⟨t, f, _, hf', selected⟩
        have ff : f = falseValue := Option.some.inj (hf'.symm.trans hf)
        have chosen : output = f := by
          rcases (field_select_iff _ _ _ _).mp selected with h | h
          · exact h.2
          · cases h.1
        change onFalse.eval inputs = some output
        rw [hf, ← ff, chosen]
      · intro h
        change onFalse.eval inputs = some output at h
        have heq : output = falseValue := Option.some.inj (h.symm.trans hf)
        exact ⟨trueValue, falseValue, ht, hf,
          (field_select_iff _ _ _ _).mpr (Or.inl ⟨rfl, heq⟩)⟩
  | true =>
      constructor
      · rintro ⟨t, f, ht', _, selected⟩
        have tf : t = trueValue := Option.some.inj (ht'.symm.trans ht)
        have chosen : output = t := by
          rcases (field_select_iff _ _ _ _).mp selected with h | h
          · cases h.1
          · exact h.2
        change onTrue.eval inputs = some output
        rw [ht, ← tf, chosen]
      · intro h
        change onTrue.eval inputs = some output at h
        have heq : output = trueValue := Option.some.inj (h.symm.trans ht)
        exact ⟨trueValue, falseValue, ht, hf,
          (field_select_iff _ _ _ _).mpr (Or.inr ⟨rfl, heq⟩)⟩

/-- Both residual arms share one strict graph and its two witnessed outputs
are joined by the same selector equation used by the source conditional. -/
def EagerGraphAccepts {n : Nat} (choice : Bool)
    (onTrue onFalse : EffectExpr n) (inputs : List M31)
    (output : M31) : Prop :=
  ∃ truePoly falsePoly trueValue falseValue,
    onTrue.toPoly? = some truePoly ∧
    onFalse.toPoly? = some falsePoly ∧
    (PolyList.code [truePoly, falsePoly]).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs [trueValue, falseValue] ∧
    fieldSelect (if choice then 1 else 0) falseValue trueValue output

/-- A conservative totality check is sufficient for the *combined* strict
graph and selector relation to mean exactly the lazy conditional. -/
theorem eager_graph_iff_lazy_if {n : Nat} (choice : Bool)
    (onTrue onFalse : EffectExpr n) (inputs : List M31)
    (output : M31) (hinputs : inputs.length = n)
    (htrue : onTrue.isTotal = true) (hfalse : onFalse.isTotal = true) :
    EagerGraphAccepts choice onTrue onFalse inputs output ↔
      lazyIf choice onTrue onFalse
        (fun i => inputs.getD i.val 0) = some output := by
  let assignment : Fin n → M31 := fun i => inputs.getD i.val 0
  obtain ⟨truePoly, htp, htv⟩ := onTrue.total_to_poly assignment htrue
  obtain ⟨falsePoly, hfp, hfv⟩ := onFalse.total_to_poly assignment hfalse
  have hgraph (t f : M31) :
      (PolyList.code [truePoly, falsePoly]).strictAccepts
        fieldArity Gadgets.Hash.fieldPrimitive inputs [t, f] ↔
      t = truePoly.eval assignment ∧ f = falsePoly.eval assignment := by
    rw [Gadgets.Hash.field_schedule_strict_sound_complete]
    simp [hinputs, PolyList.code_valid, PolyList.code_eval, assignment]
  rw [← eager_if_iff_lazy_if choice onTrue onFalse assignment output htrue hfalse]
  constructor
  · rintro ⟨tp, fp, t, f, htp', hfp', accepted, selected⟩
    have et : tp = truePoly := Option.some.inj (htp'.symm.trans htp)
    have ef : fp = falsePoly := Option.some.inj (hfp'.symm.trans hfp)
    subst tp
    subst fp
    obtain ⟨ht, hf⟩ := (hgraph t f).mp accepted
    exact ⟨t, f, by simpa [ht] using htv,
      by simpa [hf] using hfv, selected⟩
  · rintro ⟨t, f, hte, hfe, selected⟩
    have ht : t = truePoly.eval assignment :=
      Option.some.inj (hte.symm.trans htv)
    have hf : f = falsePoly.eval assignment :=
      Option.some.inj (hfe.symm.trans hfv)
    exact ⟨truePoly, falsePoly, t, f, htp, hfp,
      (hgraph t f).mpr ⟨ht, hf⟩, selected⟩

/-- A lazy conditional can succeed although its eager circuit has no
witness: the unchosen inverse of zero would still need to be satisfied. -/
theorem inactive_inverse_counterexample (x : M31) :
    lazyIf false (.checkedInverse (.literal 0)) (.literal x)
      (fun i : Fin 0 => i.elim0) = some x ∧
    ¬ EagerIfAccepts false (.checkedInverse (.literal 0)) (.literal x)
      (fun i : Fin 0 => i.elim0) x := by
  constructor
  · rfl
  · rintro ⟨value, _, hvalue, _, _⟩
    simp [EffectExpr.eval] at hvalue

end S31.Functional
