import S31.Gadgets.Air.SourceMixedAddressSchedule

/-!
The reviewed N=1..8 private mixed chain has a compositional source meaning.
The chip path theorem fixes each call's result; unique Gate producers at the
source-shaped shared addresses fix the value handed to the next call. These
premises are explicit and are not derived from native proof verification here.
-/

namespace S31.Gadgets.Air.SourceMixedChainSemantics

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.RawChipIndexCoverage
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

def sourceStep (call : Nat) (state : State) : State :=
  fun lane => state lane ^ 2 + (13 + call : F)

/-- Evaluation of exactly `n` source repeat nodes, in source order. -/
def sourcePrefix : Nat → State → State
  | 0, initial => initial
  | n + 1, initial => iterateStep (sourceStep n) 16 (sourcePrefix n initial)

theorem every_call_matches_source_prefix {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N) (boundary : Boundary N)
    (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced
      (allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields))
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial)
    (hrounds : ∀ call, boundary.rounds call = 16)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hchip : ∀ call, boundary.finish call =
      iterateStep (boundary.step call) (boundary.rounds call)
        (boundary.start call)) :
    ∀ call : Fin N,
      boundary.finish call = sourcePrefix (call.val + 1) initial := by
  have handoff : ∀ (call : Fin N) (hnext : call.val + 1 < N),
      boundary.start ⟨call.val + 1, hnext⟩ =
        boundary.finish call := by
    intro call hnext
    funext lane
    exact adjacent_call_words_coherent hN boundary haddresses hbalance hunique
      call hnext lane
  have sourceStepEq : ∀ call : Fin N,
      boundary.step call = sourceStep call.val := by
    intro call
    funext state lane
    simp [Boundary.step, sourceStep, hconstants call]
  have aux : ∀ n, (hn : n < N) →
      boundary.finish ⟨n, hn⟩ = sourcePrefix (n + 1) initial := by
    intro n
    induction n with
    | zero =>
        intro hn
        rw [hchip ⟨0, hn⟩, hrounds ⟨0, hn⟩,
          sourceStepEq ⟨0, hn⟩]
        simpa [sourcePrefix] using congrArg
          (iterateStep (sourceStep 0) 16) hfirst
    | succ n ih =>
        intro hn
        have hprev : n < N := by omega
        have hstart := handoff ⟨n, hprev⟩ hn
        rw [hchip ⟨n + 1, hn⟩, hrounds ⟨n + 1, hn⟩,
          sourceStepEq ⟨n + 1, hn⟩, hstart, ih hprev]
        rfl
  intro call
  exact aux call.val call.isLt

/-- Exact joint Gate/chip event balance and every chip row's local recurrence
give the entire source prefix, once Gate producer uniqueness and compiler
address equality are supplied. No native proof-to-exact-event reduction is
claimed here. -/
theorem source_prefix_of_joint_event_balance {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N) (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hunique : uniqueProduced
      (allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields))
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial)
    (hrounds : ∀ call, boundary.rounds call = 16)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hjoint : ((boundary.jointGateSource).circuitUses ++
      jointUses rows boundary.finish).Perm
      ((boundary.jointGateSource).circuitYields ++
        jointYields rows boundary.start))
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input) :
    ∀ call : Fin N,
      boundary.finish call = sourcePrefix (call.val + 1) initial := by
  have hpathAndBalance := joint_gate_and_every_chip_path hN boundary rows
    (by intro call; rw [hrounds call]; omega)
    (by intro call; rw [hrounds call]; omega)
    hjoint hstep
  have hpaths := hpathAndBalance.2
  exact every_call_matches_source_prefix hN hpositive boundary initial
    haddresses hpathAndBalance.1 hunique hfirst hrounds hconstants hpaths

end S31.Gadgets.Air.SourceMixedChainSemantics
