import S31.Gadgets.Air.GateProducerRoster

/-!
Two small counterexamples to interpreting the generic Lean producer scan as the
native fixed-family address check. They do not challenge the uniqueness theorem:
they show why native range correspondence needs a separate premise.

Run from `formal/s31` with `lake env lean adversarial/SourceMixedProducerBound.lean`.
-/

namespace S31.Adversarial.SourceMixedProducerBound

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateProducerCheck
open S31.Gadgets.Air.GateProducerRoster

/-- The native 512-variable scan rejects address 512, but the existentially
chosen Lean bound can be raised to 513. -/
example : scan 512 (∅ : Finset Nat) [512] = none := by decide

example : ∃ bound result,
    scan bound (∅ : Finset Nat) [512] = some result :=
  ⟨513, {512}, by decide⟩

/-- Native `scanAddresses` range-checks even a zero-multiplicity row before
skipping it. The logical-producer roster intentionally omits that row. -/
private def inactiveOutsideNativeRange : Row :=
  { in0Address := 0
    in1Address := 0
    outAddress := 512
    flags := S31.Gadgets.Air.Qm31Ops.encode .add
    in0 := S31.Gadgets.Packed.base 0
    in1 := S31.Gadgets.Packed.base 0
    output := S31.Gadgets.Packed.base 0
    multiplicity := 0 }

example : (logicalProducers [inactiveOutsideNativeRange] []).map Prod.fst = [] := by
  decide

example : ∃ result,
    scan 512 (∅ : Finset Nat)
      ((logicalProducers [inactiveOutsideNativeRange] []).map Prod.fst) = some result :=
  ⟨∅, by decide⟩

example : ¬ inactiveOutsideNativeRange.outAddress < 512 := by decide

end S31.Adversarial.SourceMixedProducerBound
