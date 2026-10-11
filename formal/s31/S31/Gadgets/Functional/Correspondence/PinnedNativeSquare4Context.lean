import S31.Gadgets.Functional.Correspondence.PinnedNativeSquare4Witness

/-!
One native square4 base assignment instantiates the arbitrary-trace algebraic
context used by `RawGateSoundness`. The public feeder's nine events are
external *uses*; the row writers produce the corresponding values. All
arithmetic, fixed-cell, and ideal Gate facts below are about the inspected
uncommitted base trace. This module does not authenticate proof openings,
interaction columns, the native feeder implementation, PCS/FRI, or
Fiat--Shamir challenge sampling.
-/

namespace S31.Functional.Correspondence.PinnedNativeSquare4Context

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.RawGateSoundness
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.PinnedNativeSquare4Witness

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def sampleInput : Lanes := fun i =>
  RiscvRefinement.M31.reduce (([0, 1, 2, 7] : List Nat)[i.val]!)

def sampleClaim : Lanes := fun i =>
  RiscvRefinement.M31.reduce (([0, 1, 16, 2401] : List Nat)[i.val]!)

/-- Every algebraic field of the bounded physical trace context is satisfied
by the same pinned 512-row native square4 base assignment. This includes the
unit, basis, and inverse producers and all eight public words as external
Gate uses. The context itself does not assert or derive proof acceptance. -/
theorem native_physical_context :
    PhysicalTraceContext trace squareCertificate 474 sampleInput sampleClaim := by
  refine {
    partition := square_partition
    fixed := physical_fixed_premise
    arithmetic := all_native_arithmetic_roots_zero
    unique := native_producers_unique
    zero := ?_
    basis1 := ?_
    basis2 := ?_
    basis3 := ?_
    maskBasis := ?_
    inverseBasis := ?_
    inputPins := ?_
    outputPins := ?_ }
  · decide
  · decide
  · decide
  · decide
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

/-- The concrete external feeder lists exactly the public statement used by
this context, with no external yields; no public values are silently assumed
from the prover's independent witness assignment. -/
theorem native_feeder_statement :
    (∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (sampleInput i))) ∈ trace.externalUses) ∧
    (∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (sampleClaim i))) ∈ trace.externalUses) ∧
    trace.externalYields = [] := by
  exact ⟨native_physical_context.inputPins,
    native_physical_context.outputPins, external_gate_feeder_exact.2⟩

/-- The source certificate executes to the same four words used by the
native public feeder on this concrete input. This is the positional
certificate's field interpreter, not a proof of native parser execution. -/
theorem source_certificate_evaluates_sample :
    executeNormalized squareCertificate sampleInput = some sampleClaim := by
  decide

/-- The existing arbitrary-trace Gate theorem can now be applied directly
to the pinned native physical context: any result of the checked positional
certificate on this input equals the feeder's claimed result. The premise
about `executeNormalized` is about source semantics; the AIR/ideal Gate
premises are discharged by the inspected native base trace. This theorem
still makes no claim about committed proofs or verifier acceptance. -/
theorem native_claim_of_certificate_execution (output : Lanes)
    (hexecute : executeNormalized squareCertificate sampleInput = some output) :
    output = sampleClaim := by
  exact physical_balanced_certificate_claim trace squareCertificate 474
    sampleInput sampleClaim output native_physical_context
    (by decide) hexecute native_ideal_gate_balanced

end S31.Functional.Correspondence.PinnedNativeSquare4Context
