import S31.Gadgets.Air.NativeLogUpAir

namespace S31.Gadgets.Air.NativeLogUpAirProof
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpInteraction

/-- The native six-element Gate lookup key is the same polynomial evaluation
used by the Lean challenge-collision and zero-denominator bounds. -/
theorem native_combine_eq (tuple : Fin 6 → GateSecure)
    (alpha z : GateSecure) :
    NativeLogUpAir.combine tuple alpha z = combineTerm tuple alpha z := by
  simp [NativeLogUpAir.combine, combineTerm, tupleHorner]
  ring

/-- The native single-fraction AIR equation is the modeled residual. -/
theorem native_single_eq (term : Term GateSecure) (diff : GateSecure) :
    NativeLogUpAir.single term diff = singleResidual term diff := by
  rfl

/-- The native paired-fraction AIR equation is the modeled residual,
including the denominator product that can vanish at a bad challenge. -/
theorem native_pair_eq (left right : Term GateSecure) (diff : GateSecure) :
    NativeLogUpAir.pair left right diff =
      pairResidual left right diff := by
  rfl

end S31.Gadgets.Air.NativeLogUpAirProof
