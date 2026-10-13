import S31.Gadgets.PcsFri.OperationalExtraction

/-!
The PCS verifier computes DEEP quotient answers at normalized positions, then
expands them into raw transcript order. S31 now recomputes them directly on
the captured raw rows before FRI admission. This file proves the list-level
bridge: when the recorded list equals the quotient at every raw position,
operational acceptance can be stated over that quotient function itself.

The native recomputation call is source pinned and tested, not a Lean proof of
Zig execution. The quotient formula, captured Merkle leaf authentication, and
Fiat–Shamir challenge custody remain separate premises.
-/

namespace S31.Gadgets.PcsFri.RawDeepCustody

open S31.Gadgets.PcsFri.QueryAndTranscript
open S31.Gadgets.PcsFri.LayerAcceptance
open S31.Gadgets.PcsFri.OperationalExtraction

variable {F : Type*}

/-- Exact raw order and multiplicity, including repeated transcript queries. -/
def rawAnswers (raw : List Nat) (answers : List F) (row : Nat → F) : Prop :=
  answers = raw.map row

/-- Equal raw answer arrays force equality of the two row functions at every
queried position; no equality outside the queried set is needed. -/
theorem raw_answers_agree_on_queries (raw : List Nat) (answers : List F)
    (captured quotient : Nat → F)
    (hcaptured : rawAnswers raw answers captured)
    (hquotient : rawAnswers raw answers quotient) :
    ∀ q ∈ raw, captured q = quotient q := by
  have hmaps : raw.map captured = raw.map quotient := by
    exact hcaptured.symm.trans hquotient
  clear hcaptured hquotient answers
  induction raw with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.cons.injEq] at hmaps
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hmaps.1
      · exact ih hmaps.2 q hq

/-- Only the initial current-value check depends on the DEEP answer function;
later layers and the terminal check inherit the same folded current values. -/
theorem operationalAccepts_change_initial (raw : List Nat)
    (captured quotient : Nat → F) (layers : List (Layer F))
    (terminal : Terminal F)
    (hagree : ∀ q ∈ raw, captured q = quotient q)
    (haccept : operationalAccepts raw captured layers terminal) :
    operationalAccepts raw quotient layers terminal := by
  cases layers with
  | nil =>
      refine ⟨haccept.1, ?_⟩
      intro q hq
      exact (hagree q hq).symm.trans (haccept.2 q hq)
  | cons layer rest =>
      refine ⟨⟨?_, haccept.1.2⟩, haccept.2⟩
      intro q hq
      exact (hagree q hq).symm.trans (haccept.1.1 q hq)

/-- Raw DEEP answer custody, operational replay, and explicit Merkle binding
compose to modeled acceptance of the quotient values for any layer schedule. -/
theorem raw_deep_and_operational_implies_accepts
    (raw : List Nat) (answers : List F)
    (captured quotient : Nat → F) (layers : List (Layer F))
    (terminal : Terminal F)
    (hcaptured : rawAnswers raw answers captured)
    (hquotient : rawAnswers raw answers quotient)
    (hoperational : operationalAccepts raw captured layers terminal)
    (hbinding : oracleBoundSchedule raw layers) :
    accepts (normalized raw) quotient layers terminal := by
  apply operational_and_binding_implies_accepts raw quotient layers terminal
  · exact operationalAccepts_change_initial raw captured quotient layers terminal
      (raw_answers_agree_on_queries raw answers captured quotient hcaptured hquotient)
      hoperational
  · exact hbinding

end S31.Gadgets.PcsFri.RawDeepCustody
