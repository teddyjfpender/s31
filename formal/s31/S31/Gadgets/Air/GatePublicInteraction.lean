import S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-!
The legacy gate verifier checks one public LogUp sum and eleven component
claims before it mixes the claims into the Fiat--Shamir channel. This module
models that final field equation. It does not identify the claims with
authenticated interaction columns; that is the outstanding P02 refinement.
-/

namespace S31.Gadgets.Air.GatePublicInteraction

open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Packed

/-- The source loop in `validateLogupSum`, starting with the public sum. -/
def nativeClaimLoop (publicSum : GateSecure) : List GateSecure → GateSecure
  | [] => publicSum
  | claim :: rest => nativeClaimLoop (publicSum + claim) rest

theorem nativeClaimLoop_eq_sum (publicSum : GateSecure)
    (claims : List GateSecure) :
    nativeClaimLoop publicSum claims = publicSum + claims.sum := by
  induction claims generalizing publicSum with
  | nil => simp [nativeClaimLoop]
  | cons claim rest ih =>
      rw [nativeClaimLoop, ih]
      simp only [List.sum_cons]
      ring

/-- This is the public equation tested by the native circuit statement:
eight digest output gates at addresses 3..10, the fixed `u` gate at 2,
and all eleven component claimed sums. -/
def nativeGateClosure (outputs : List Quad)
    (claims : List GateSecure) (alpha z : GateSecure) : GateSecure :=
  nativeClaimLoop
    (nativeLookupSum outputs 0 alpha z) claims

theorem nativeGateClosure_eq_event_sum
    (outputs : List Quad) (claims : List GateSecure)
    (alpha z : GateSecure) :
    nativeGateClosure outputs claims alpha z =
      claims.sum + productionReciprocalSum7
        (publicOutputYields outputs) alpha z := by
  rw [nativeGateClosure, nativeClaimLoop_eq_sum,
    nativeLookupSum_eq_public_events]
  ring

theorem closed_native_gate_claims_eq_negative_public
    (outputs : List Quad) (claims : List GateSecure)
    (alpha z : GateSecure)
    (hclosed : nativeGateClosure outputs claims alpha z = 0) :
    claims.sum = -productionReciprocalSum7
      (publicOutputYields outputs) alpha z := by
  rw [nativeGateClosure_eq_event_sum] at hclosed
  exact eq_neg_of_add_eq_zero_left hclosed

theorem public_event_count (outputs : List Quad)
    (height : outputs.length = 8) :
    (publicOutputYields outputs).length = 9 := by
  have haux (index : Nat) (xs : List Quad) :
      (outputEventsAux index xs).length = xs.length := by
    induction xs generalizing index with
    | nil => simp [outputEventsAux]
    | cons _ rest ih => simp [outputEventsAux, ih]
  simp [publicOutputYields, haux, height]

end S31.Gadgets.Air.GatePublicInteraction
