import S31.Gadgets.Air.SourceMixedRoster
import S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-!
A typed ideal event boundary for the experimental source-pinned mixed profile.
One boundary owns each call's eight canonical Gate addresses, eight M31 bridge
words, round count, and square-plus-constant step. The same bridge words form
the eight Gate reads and the two chip endpoint events. Its Gate-positive list
also includes the verifier's eight public output tuples and fixed `u` tuple.

The theorems below start with an **exact joint event permutation**, not a
native proof. They do not establish that Zig emits these lists, that the
source compiler supplies these addresses/constants, that Gate arithmetic
rows or producer uniqueness hold, or that AIR/LogUp/PCS/Fiat--Shamir acceptance
implies their hypotheses. Those are separate correspondence and soundness
obligations.
-/

namespace S31.Gadgets.Air.SourceMixedPath

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.IndexedManyChipPath
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.RawChipIndexCoverage

/-- A source-shaped one-to-eight-call boundary. The `baseline` lists stand for
any other Gate events of the circuit component; they are kept explicit so the
bridge/public feeder is not silently folded into the native circuit claim. -/
structure Boundary (N : Nat) where
  rounds : Fin N → Nat
  constants : Fin N → F
  addresses : Fin N → Fin 8 → CanonicalAddress
  words : Fin N → Fin 8 → F
  rows : List CanonicalRow
  baselineUses : List CanonicalEvent
  baselineYields : List CanonicalEvent
  publicOutputs : Fin 8 → F

/-- Eight public M31 output words at native Gate addresses 3..10, followed by
the fixed `u` word at address 2. All addresses are canonical by type. -/
def Boundary.publicFeeder {N : Nat} (boundary : Boundary N) :
    List CanonicalEvent :=
  List.ofFn (fun output : Fin 8 =>
    ((⟨3 + output.val, by omega⟩ : CanonicalAddress),
      base (boundary.publicOutputs output))) ++
    [((⟨2, by decide⟩ : CanonicalAddress), ⟨0, 0, 1, 0⟩)]

/-- The typed public feeder is the same ordered output-and-`u` tuple list
used by the modeled native verifier claim fold. -/
theorem Boundary.publicFeeder_native_events {N : Nat}
    (boundary : Boundary N) :
    (boundary.publicFeeder.map CanonicalEvent.toGate).map
      embedGateEvent =
      publicOutputYields
        (List.ofFn fun output : Fin 8 =>
          base (boundary.publicOutputs output)) := by
  rfl

/-- One call reads exactly eight Gate words: four input ports followed by
four output ports. The input/output states below use these same `words`. -/
def Boundary.callBridgeGates {N : Nat} (boundary : Boundary N)
    (call : Fin N) : List CanonicalEvent :=
  List.ofFn (fun lane : Fin 8 =>
    (boundary.addresses call lane, base (boundary.words call lane)))

def Boundary.bridgeGates {N : Nat} (boundary : Boundary N) :
    List CanonicalEvent :=
  (List.finRange N).flatMap boundary.callBridgeGates

theorem Boundary.callBridgeGates_length {N : Nat}
    (boundary : Boundary N) (call : Fin N) :
    (boundary.callBridgeGates call).length = 8 := by
  simp [Boundary.callBridgeGates]

/-- Every admitted call contributes eight, including repeated source input
addresses: occurrences, not distinct addresses, are what LogUp counts. -/
theorem Boundary.bridgeGates_length {N : Nat}
    (boundary : Boundary N) :
    boundary.bridgeGates.length = 8 * N := by
  simp [Boundary.bridgeGates, List.length_flatMap,
    Boundary.callBridgeGates_length]
  omega

/-- A bridge Gate occurrence has the production six-word Gate layout padded
to seven words. The native bridge AIR repeats its words across sixteen rows;
this theorem uses the constant row-valued words of this typed boundary. -/
theorem Boundary.bridgeGate_native_tuple {N : Nat}
    (boundary : Boundary N) (call : Fin N) (lane : Fin 8)
    (row : Fin 16) :
    embedGateEvent
      ((boundary.addresses call lane).val,
        base (boundary.words call lane)) =
      sourceBridgeGateTuple
        (fun slot => ((boundary.addresses call slot).val : F))
        (fun slot _ => boundary.words call slot) lane row := by
  funext coordinate
  fin_cases coordinate <;>
    rfl

def Boundary.start {N : Nat} (boundary : Boundary N)
    (call : Fin N) : State :=
  fun lane => boundary.words call (bridgeInputLane lane)

def Boundary.finish {N : Nat} (boundary : Boundary N)
    (call : Fin N) : State :=
  fun lane => boundary.words call (bridgeOutputLane lane)

def Boundary.step {N : Nat} (boundary : Boundary N)
    (call : Fin N) (state : State) : State :=
  fun lane => state lane ^ 2 + boundary.constants call

/-- This is a *joint* Gate model: its external yields include the verifier's
public feeder and all bridge Gate reads. It is not the circuit component's
claimed-sum equation in isolation. -/
def Boundary.jointGateSource {N : Nat} (boundary : Boundary N) :
    GateSource :=
  { rows := boundary.rows,
    externalUses := boundary.baselineUses,
    externalYields := boundary.baselineYields ++
      boundary.publicFeeder ++ boundary.bridgeGates }

/-- One exact seven-word permutation forces both the complete Gate lookup
multiset and each source-shaped square-plus-constant chip path. Gate local
arithmetic, unique producers, public statement identity, compiler-to-event
correspondence, and native proof authentication are separate premises. -/
theorem joint_gate_and_every_chip_path {N : Nat}
    (hN : N ≤ 8) (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hpositive : ∀ call, 0 < boundary.rounds call)
    (hR : ∀ call, boundary.rounds call < 2147483647)
    (hjoint : ((boundary.jointGateSource).circuitYields ++
      jointUses rows boundary.finish).Perm
      ((boundary.jointGateSource).circuitUses ++
        jointYields rows boundary.start))
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input) :
    balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields ∧
      ∀ call, boundary.finish call =
        iterateStep (boundary.step call) (boundary.rounds call)
          (boundary.start call) := by
  constructor
  · exact boundary.jointGateSource.exact_joint_implies_gate_balance
      (jointUses rows boundary.finish) (jointYields rows boundary.start)
      (jointUses_chip_only rows boundary.finish)
      (jointYields_chip_only rows boundary.start) hjoint
  · exact every_call_complete_path_of_gate_prefixed_joint hN rows
      boundary.start boundary.finish boundary.step
      boundary.jointGateSource.circuitYields
      boundary.jointGateSource.circuitUses
      boundary.jointGateSource.circuit_yields_gate_tag
      boundary.jointGateSource.circuit_uses_gate_tag
      hpositive hR hjoint hstep

/-- Conditional rational-compression version. `hgood` excludes the explicit
collision/pole set for the *entire* joint tuple support. The accepted native
proof-to-`hclosed` and good-challenge links are not established here. -/
theorem joint_gate_and_every_chip_path_of_good_challenge
    {N : Nat} (hN : N ≤ 8) (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hpositive : ∀ call, 0 < boundary.rounds call)
    (hR : ∀ call, boundary.rounds call < 2147483647)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ badPairs7
      (boundary.jointGateSource.circuitYields ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitUses ++
        jointYields rows boundary.start))
    (hclosed : productionReciprocalSum7
      (boundary.jointGateSource.circuitYields ++
        jointUses rows boundary.finish) alpha z =
      productionReciprocalSum7
        (boundary.jointGateSource.circuitUses ++
          jointYields rows boundary.start) alpha z)
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input) :
    balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields ∧
      ∀ call, boundary.finish call =
        iterateStep (boundary.step call) (boundary.rounds call)
          (boundary.start call) := by
  exact joint_gate_and_every_chip_path hN boundary rows hpositive hR
    (exact_joint_events_outside_badPairs7 _ _ alpha z hgood hclosed)
    hstep

end S31.Gadgets.Air.SourceMixedPath
